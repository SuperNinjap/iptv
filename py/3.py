#!/usr/bin/env python3
"""
IPTV m3u 播放列表批量中转器（按需缓存 · 自动清理版）
=====================================================
解决三类问题：
  1. 源站播放 token 只有约 30 秒寿命 → 后台自动续期，播放器无感
  2. 整份 m3u 里几十上百个频道 → 「谁在播才缓存谁」，没在看的一律不动
  3. 缓存切片占满磁盘/内存 → 播完即停、停即清空，播放中也只留一个窗口

本版相对上一版的关键变化（都是为上面 2、3 条）：
  · 空闲判定只看「播放器的真实请求」（m3u8 或分片），后台续期本身不算活着
    —— 上一版 refresher 每轮自己 touch()，IDLE_SEC 永远不成立，所以看过一次就永久续期
  · 未在播放的频道只预取最新 2 个分片，播放器跳过/拖走的旧分片不再补下
  · 播放中只保留最近 WINDOW 个分片，字典淘汰和磁盘删除同步做，另加磁盘兜底扫描
  · 频道一停（空闲超时 / 切换）立刻停线程、清空内存池、删掉整个分片目录
  · 启动时清掉上次异常退出残留的缓存；后台还有守护线程定期扫残
  · 分片先写 .part 再原子改名，避免播放器读到半截文件

用法：
    python3 iptv_relay_multi.py                      # 直接跑，用内置远程列表
    python3 iptv_relay_multi.py 你的列表.m3u          # 用本地文件
    python3 iptv_relay_multi.py -p 8080 -o local.m3u  # 改端口/输出名
    cat 你的列表.m3u | python3 iptv_relay_multi.py -   # 从管道读

然后：
    · 本机播放：播放器打开 http://127.0.0.1:8080/playlist.m3u
    · 局域网/电视盒子：http://<电脑IP>:8080/playlist.m3u

参数：
    src         列表来源：本地路径 / http(s) 地址 / - (stdin)，不填用内置远程列表
    -p/--port   本地端口，默认 8080
    -o/--out    生成到本地的 m3u 文件名，默认脚本同目录
    -u/--ua     请求用的 User-Agent，默认 MAG 机顶盒 UA
    -i/--idle   播放器多久没请求就停止缓存并清盘（秒），默认 60
    -f/--filter 只处理名字包含该关键字的频道
    -s/--segdir 切片缓存目录
    -w/--window 播放中保留多少个分片，默认 30
    -r/--reload 每隔多少分钟重新拉取远程列表，0 表示只拉一次，默认 30
"""

import argparse
import http.server
import os
import re
import shutil
import socketserver
import sys
import threading
import time
import urllib.error
import urllib.request
from collections import OrderedDict
from urllib.parse import quote, urljoin

MAG_UA = ("Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 "
          "(KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3")

REFRESH_INTERVAL = 18      # token 活约 30s，18s 换一次才安全
WINDOW = 30                # 播放中保留切片数
IDLE_SEC = 10              # 播放器多久没请求 → 停止缓存 + 清盘
PRELOAD = 2                # 还没开始播放时最多预取几个最新分片
SEG_DL_LIMIT = 6           # 单轮最多补几个分片，防止一次爆下载
MAX_FAILS = 3              # 单个分片最多试几次，超了就放弃（不无限重试）
# 默认放在脚本同级目录，避免 /tmp 容量不足（部分系统 /tmp 只有 256MB）
SEG_ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "segs")

# ---------------------------------------------------------------- 内置远程列表
DEFAULT_PLAYLIST = (
    "https://ghfast.top/https://raw.githubusercontent.com/SuperNinjap/iptv/main/USA.m3u"
)
CACHE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".playlist_cache.m3u")


def log(*a):
    print(time.strftime("[%H:%M:%S]"), *a, flush=True)


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    """自己接管 302：直接读 Location，不靠 geturl() 猜。"""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise urllib.error.HTTPError(req.full_url, code, msg, headers, fp)


_OPENER = urllib.request.build_opener(_NoRedirect)


# ---------------------------------------------------------------- 列表加载
def load_playlist(src, ua=MAG_UA, timeout=90):
    """从 本地文件 / http(s) URL / stdin 读取 m3u 文本，带缓存回退。"""
    if src == "-":
        log("从标准输入读取列表")
        return sys.stdin.read()

    if re.match(r"^https?://", src):
        log(f"从远程拉取列表：{src}")
        try:
            req = urllib.request.Request(src, headers={
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
                "Accept": "*/*",
            })
            with urllib.request.urlopen(req, timeout=timeout) as r:
                data = r.read()
            text = data.decode("utf-8", "ignore")
            if "#EXTM3U" not in text[:2000].upper():
                raise ValueError("返回内容不像 m3u（缺少 #EXTM3U）")
            try:
                with open(CACHE_FILE, "w", encoding="utf-8") as f:
                    f.write(text)
            except OSError:
                pass
            log(f"拉取成功：{len(data)} 字节，已更新本地缓存")
            return text
        except Exception as e:
            log(f"远程拉取失败：{e}")
            if os.path.exists(CACHE_FILE):
                log(f"回退使用本地缓存 {CACHE_FILE}")
                return open(CACHE_FILE, encoding="utf-8", errors="ignore").read()
            raise

    log(f"读取本地文件：{src}")
    if not os.path.exists(src):
        raise FileNotFoundError(
            f"找不到列表文件 {src!r}。"
            f"提示：不填参数会用内置远程列表；"
            f"手机上若 App 传参丢了 -p，纯数字会被自动当端口处理"
        )
    return open(src, encoding="utf-8", errors="ignore").read()


# ---------------------------------------------------------------- m3u 解析
def parse_m3u(text):
    """返回 [(title, group, logo, url), ...]"""
    chans = []
    meta = {}
    title = ""
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("#EXTINF"):
            attrs = dict(re.findall(r'([\w-]+)="([^"]*)"', line))
            meta = {
                "group": attrs.get("group-title", ""),
                "logo": attrs.get("tvg-logo", ""),
                "name": attrs.get("tvg-name", ""),
            }
            title = line.split(",", 1)[-1].strip() if "," in line else meta["name"]
        elif line.startswith("#"):
            continue
        else:
            if title or meta:
                chans.append((title or meta.get("name", "") or f"频道{len(chans)+1}",
                              meta.get("group", ""), meta.get("logo", ""), line))
                title, meta = "", {}
            else:
                chans.append((f"频道{len(chans)+1}", "", "", line))
    return chans


# ---------------------------------------------------------------- 单频道中转
class ChannelRelay:
    def __init__(self, idx, name, group, logo, url, ua):
        self.idx = idx
        self.name = name
        self.group = group
        self.logo = logo
        self.ua = ua
        self.entry = self._to_m3u8(url)
        self.segs = OrderedDict()          # seq -> {url, dur, local, fails}
        self.lock = threading.Lock()
        self.running = False
        self.last_client = 0.0             # 只有播放器真实请求才更新
        self.play_pos = None               # 播放器最近请求的分片号
        self.fail = 0
        self.seg_dir = os.path.join(SEG_ROOT, str(idx))
        self.stop_evt = threading.Event()
        self.first_ready = threading.Event()
        self.threads = []

    # ------------------------------------------------ 地址
    @staticmethod
    def _to_m3u8(u):
        if "extension=" in u:
            return re.sub(r"extension=\w*", "extension=m3u8", u)
        if ".m3u8" in u:
            return u
        sep = "&" if "?" in u else "?"
        return u + sep + "extension=m3u8"

    # ------------------------------------------------ 生命周期
    def alive(self):
        """当前算不算「正在被看」。后台续期/下载动作本身不算。"""
        if self.stop_evt.is_set() or not self.running:
            return False
        return (time.time() - self.last_client) <= IDLE_SEC

    def note_client(self, seq=None):
        """播放器请求（m3u8 或分片）→ 续命 + 记录播放位置。"""
        self.last_client = time.time()
        if seq is not None:
            with self.lock:
                self.play_pos = seq

    def start(self):
        self.stop_evt = threading.Event()
        self.first_ready = threading.Event()
        self.running = True
        self.last_client = time.time()
        self.fail = 0
        os.makedirs(self.seg_dir, exist_ok=True)
        for fn in (self.refresher, self.downloader):
            t = threading.Thread(target=fn, daemon=True)
            t.start()
            self.threads.append(t)

    def stop(self, reason="空闲"):
        """停线程 + 清内存池 + 删整目录（缓存不留在盘上）。"""
        was_running = self.running
        self.running = False
        self.stop_evt.set()
        self.play_pos = None
        with self.lock:
            self.segs.clear()
        shutil.rmtree(self.seg_dir, ignore_errors=True)
        self.threads = []
        if was_running:
            log(f"[{self.idx}]{self.name} {reason}，已停止缓存并清空磁盘")

    # ------------------------------------------------ 源站清单
    def _read_list(self, url, depth=0):
        if depth > 3:
            return None, "__ERR_too_many_redirect"
        req = urllib.request.Request(url, headers={"User-Agent": self.ua})
        try:
            with _OPENER.open(req, timeout=20) as r:
                body = r.read().decode("utf-8", "ignore")
                if body.lstrip().upper().startswith("#EXTM3U"):
                    return url, body
                loc = r.headers.get("Location")
                if loc:
                    return self._read_list(urljoin(url, loc), depth + 1)
                return None, "__ERR_not_m3u8"
        except urllib.error.HTTPError as e:
            loc = e.headers.get("Location") if e.headers else None
            if loc:
                return self._read_list(urljoin(url, loc), depth + 1)
            return None, f"__ERR_{e.code}"
        except Exception as e:
            return None, f"__ERR_{type(e).__name__}"

    def _fetch_playlist(self):
        """一次请求拿 m3u8：302 跟 Location，直接 200 返回清单也认。"""
        return self._read_list(self.entry)

    def _parse(self, text, base):
        m = re.search(r"#EXT-X-MEDIA-SEQUENCE:(\d+)", text)
        bseq = int(m.group(1)) if m else 0
        out, dur, i = [], 10.0, 0
        for line in text.splitlines():
            line = line.strip()
            if line.startswith("#EXTINF:"):
                try:
                    dur = float(line.split(":")[1].split(",")[0])
                except Exception:
                    dur = 10.0
            elif line and not line.startswith("#") and ".ts" in line:
                url = line if line.startswith("http") else urljoin(base, line)
                mm = re.search(r"_(\d+)\.ts", line)
                out.append((int(mm.group(1)) if mm else bseq + i, url, dur))
                i += 1
        return out

    # ------------------------------------------------ 续期线程
    def refresher(self):
        while self.running:
            if not self.alive():
                self.stop("播放器已停止请求")
                break
            pl, text = self._fetch_playlist()
            if pl and text and not text.startswith("__ERR"):
                try:
                    items = self._parse(text, pl)
                    if not items:
                        raise ValueError("清单里没有分片")
                    new = 0
                    with self.lock:
                        for seq, url, dur in items:
                            if seq not in self.segs:
                                self.segs[seq] = {"url": url, "dur": dur,
                                                  "local": None, "fails": 0}
                                new += 1
                    self.prune()
                    self.fail = 0
                    if new:
                        log(f"[{self.idx}]{self.name} 续期OK 新增{new} 池{len(self.segs)}")
                except Exception as e:
                    self.fail += 1
                    log(f"[{self.idx}]{self.name} 解析失败 {e}")
                    if self.fail >= MAX_FAILS:
                        log(f"[{self.idx}]{self.name} 连续失败，暂停 30s")
                        self.stop_evt.wait(30)
            else:
                self.fail += 1
                log(f"[{self.idx}]{self.name} 取token失败 {text}")
                if self.fail >= MAX_FAILS:
                    log(f"[{self.idx}]{self.name} 连续失败，暂停 30s")
                    self.stop_evt.wait(30)
            self.stop_evt.wait(REFRESH_INTERVAL)

    # ------------------------------------------------ 下载线程
    def _download_one(self, seq, url):
        p = os.path.join(self.seg_dir, f"{seq}.ts")
        tmp = p + ".part"
        try:
            req = urllib.request.Request(url, headers={"User-Agent": self.ua})
            with urllib.request.urlopen(req, timeout=20) as r, open(tmp, "wb") as f:
                shutil.copyfileobj(r, f)
            if os.path.getsize(tmp) < 1000:
                os.remove(tmp)
                raise ValueError("分片太小")
            os.replace(tmp, p)          # 原子替换，播放器读不到半截文件
        except Exception:
            try:
                if os.path.exists(tmp):
                    os.remove(tmp)
            except OSError:
                pass
            with self.lock:
                it = self.segs.get(seq)
                if it is not None:
                    it["fails"] = it.get("fails", 0) + 1
                    if it["fails"] >= MAX_FAILS:
                        it["local"] = None      # 放弃，不再反复重试
            return False
        with self.lock:
            it = self.segs.get(seq)
            if it is None:                  # 下载途中已被淘汰 → 不留
                keep = False
            else:
                it["local"] = p
                keep = True
        if not keep:
            try:
                os.remove(p)
            except OSError:
                pass
            return False
        self.first_ready.set()
        return True

    def downloader(self):
        os.makedirs(self.seg_dir, exist_ok=True)
        while self.running:
            todo = []
            with self.lock:
                pos = self.play_pos
                items = [(s, i["url"]) for s, i in self.segs.items()
                         if i["local"] is None and i.get("fails", 0) < MAX_FAILS]
            if pos is None:
                # 还没开始串流：只预取最新几个，别把整段历史拉下来
                todo = items[-PRELOAD:]
            else:
                # 只补播放位置前后的，播放器早就跳过的旧分片不再下
                todo = [(s, u) for s, u in items if s >= pos - 1][:SEG_DL_LIMIT]
            for s, u in todo:
                if not self.running:
                    break
                if time.time() - self.last_client > IDLE_SEC:
                    break
                self._download_one(s, u)
            self.prune()
            time.sleep(0.3 if todo else 0.8)

    # ------------------------------------------------ 缓存回收
    def prune(self):
        """播放中只留 WINDOW 个分片：字典裁 + 磁盘删，双保险。"""
        dropped = []
        with self.lock:
            while len(self.segs) > WINDOW:
                _, info = self.segs.popitem(last=False)
                if info.get("local"):
                    dropped.append(info["local"])
            keep = {os.path.basename(i["local"]) for i in self.segs.values() if i.get("local")}
        for p in dropped:
            try:
                os.remove(p)
            except OSError:
                pass
        try:
            names = os.listdir(self.seg_dir)
        except OSError:
            return
        now = time.time()
        for fn in names:
            fp = os.path.join(self.seg_dir, fn)
            try:
                age = now - os.path.getmtime(fp)
            except OSError:
                continue
            if fn.endswith(".ts"):
                # 3 秒内的新文件留给下载线程收尾，避免竞态误删
                if fn not in keep and age > 3:
                    try:
                        os.remove(fp)
                    except OSError:
                        pass
            elif fn.endswith(".part") and age > 60:
                try:
                    os.remove(fp)
                except OSError:
                    pass

    # ------------------------------------------------ 本地清单
    def has_ready(self):
        with self.lock:
            return any(i["local"] for i in self.segs.values())

    def wait_first(self, timeout=6.0):
        if self.has_ready():
            return
        self.first_ready.wait(timeout)

    def build_m3u8(self):
        with self.lock:
            ready = sorted([(s, i) for s, i in self.segs.items() if i["local"]])
        head = ["#EXTM3U", "#EXT-X-VERSION:3", "#EXT-X-TARGETDURATION:14"]
        if not ready:
            return "\n".join(head + ["#EXT-X-MEDIA-SEQUENCE:0"]) + "\n"
        ready = ready[-WINDOW:]
        first = ready[0][0]
        out = head + [f"#EXT-X-MEDIA-SEQUENCE:{first}"]
        prev = None
        for s, i in ready:
            if prev is not None and s != prev + 1:
                out.append("#EXT-X-DISCONTINUITY")
            out.append(f"#EXTINF:{i['dur']:.3f},")
            out.append(f"/ch/{self.idx}/seg/{s}.ts")
            prev = s
        return "\n".join(out) + "\n"


# ---------------------------------------------------------------- 管理
CHANS = {}
LOCK = threading.Lock()


def get_relay(idx, seq=None):
    with LOCK:
        ch = CHANS.get(idx)
        if not ch:
            return None
        if not ch.running:
            ch.start()
            log(f"[{idx}]{ch.name} 开始按需缓存")
        ch.note_client(seq)
        return ch


class Handler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *a):
        pass

    def _send(self, body, ctype):
        if isinstance(body, str):
            body = body.encode()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = self.path.split("?")[0]
        # 总播放列表
        if path in ("/", "/playlist.m3u", "/playlist.m3u8"):
            lines = ["#EXTM3U"]
            for idx, ch in CHANS.items():
                g = f' group-title="{ch.group}"' if ch.group else ""
                n = f' tvg-name="{ch.name}"' if ch.name else ""
                lines.append(f"#EXTINF:-1{n}{g},{ch.name}")
                lines.append(f"http://{self.headers.get('Host','127.0.0.1')}/ch/{idx}/live.m3u8")
            return self._send("\n".join(lines) + "\n", "application/vnd.apple.mpegurl")
        # 单频道 m3u8 —— 只有这里被请求，才算「有人在看这个台」
        m = re.match(r"^/ch/(\d+)/live\.m3u8$", path)
        if m:
            ch = get_relay(int(m.group(1)))
            if not ch:
                return self.send_error(404)
            if not ch.has_ready():
                ch.wait_first(6.0)      # 等首个分片，别回空清单让播放器报错
            return self._send(ch.build_m3u8(), "application/vnd.apple.mpegurl")
        # 切片
        m = re.match(r"^/ch/(\d+)/seg/(\d+)\.ts$", path)
        if m:
            idx, seq = int(m.group(1)), int(m.group(2))
            ch = get_relay(idx, seq)
            p = os.path.join(SEG_ROOT, str(idx), f"{seq}.ts")
            if os.path.exists(p):
                with open(p, "rb") as f:
                    data = f.read()
                return self._send(data, "video/mp2t")
            return self.send_error(404)
        # 状态
        if path == "/status":
            with LOCK:
                chans = list(CHANS.values())
            running = [c for c in chans if c.running]
            total_bytes = 0
            for c in running:
                try:
                    for fn in os.listdir(c.seg_dir):
                        try:
                            total_bytes += os.path.getsize(os.path.join(c.seg_dir, fn))
                        except OSError:
                            pass
                except OSError:
                    pass
            head = [f"频道总数: {len(chans)}   正在缓存: {len(running)}",
                    f"缓存占用: {total_bytes/1048576:.1f} MB   （没在看的频道不缓存）"]
            rows = []
            for c in running:
                idle = int(time.time() - c.last_client)
                rows.append(f"#{c.idx} {c.name} | 分组={c.group} | 分片池={len(c.segs)} "
                            f"| 播放位置={c.play_pos} | 上次请求={idle}s前")
            if not rows:
                rows = ["(当前没有频道在播放，播放器请求某个频道后才会开始缓存)"]
            return self._send("\n".join(head + [""] + rows), "text/plain; charset=utf-8")
        self.send_error(404)


def sanitize_args(ap):
    """兼容 Android App / 内嵌 Python 环境里不可靠的参数传递。"""
    raw = sys.argv[1:]

    if len(raw) == 1 and " " in raw[0]:
        log(f"参数被合并成一项 {raw[0]!r}，自动拆分")
        raw = raw[0].split()

    a = ap.parse_args(raw)

    if a.src and re.fullmatch(r"\d{2,5}", a.src.strip()):
        log(f"参数 {a.src!r} 是纯数字，判定为端口号（App 传参丢了 -p），按 -p {a.src} 处理")
        a.port = int(a.src)
        a.src = DEFAULT_PLAYLIST

    elif a.src and a.src.startswith("-"):
        log(f"参数 {a.src!r} 像选项而非列表来源，忽略并用内置列表")
        a.src = DEFAULT_PLAYLIST

    return a


def bind_server(port, handler):
    """端口被占用时自动往后找，手机常见 8080 已被别的 App 占了。"""
    for p in range(port, port + 30):
        try:
            srv = socketserver.ThreadingTCPServer(("0.0.0.0", p), handler)
            if p != port:
                log(f"端口 {port} 被占用，改用 {p}")
            return srv, p
        except OSError:
            continue
    raise OSError(f"{port}~{port+29} 范围内端口全被占用")


def purge_stale_cache():
    """启动时清掉上次异常退出残留的缓存（只删本脚本缓存目录里的文件）。"""
    freed = 0
    try:
        subs = os.listdir(SEG_ROOT)
    except OSError:
        return
    for sub in subs:
        d = os.path.join(SEG_ROOT, sub)
        if os.path.isdir(d):
            for fn in os.listdir(d):
                try:
                    freed += os.path.getsize(os.path.join(d, fn))
                except OSError:
                    pass
            shutil.rmtree(d, ignore_errors=True)
    if freed:
        log(f"已清理上次残留缓存 {freed/1048576:.1f} MB")


def janitor_loop():
    """兜底守护：到点停掉没人看的频道，删掉不该存在的缓存目录。"""
    while True:
        time.sleep(10)
        try:
            with LOCK:
                chans = list(CHANS.values())
            for ch in chans:
                if ch.running and not ch.alive():
                    ch.stop("长时间无人播放")
                if not ch.running and os.path.isdir(ch.seg_dir):
                    shutil.rmtree(ch.seg_dir, ignore_errors=True)
        except Exception:
            pass


def main():
    global IDLE_SEC, SEG_ROOT, WINDOW
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("src", nargs="?", default=DEFAULT_PLAYLIST,
                    help="m3u 来源：本地路径 / http(s) 地址 / - (stdin)；不填用内置远程列表")
    ap.add_argument("-p", "--port", type=int, default=8080)
    ap.add_argument("-o", "--out",
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "local_playlist.m3u"))
    ap.add_argument("-u", "--ua", default=MAG_UA)
    ap.add_argument("-i", "--idle", type=int, default=IDLE_SEC,
                    help="播放器多久没请求就停止缓存并清盘（秒）")
    ap.add_argument("-f", "--filter", default="")
    ap.add_argument("-s", "--segdir", default=SEG_ROOT, help="切片缓存目录")
    ap.add_argument("-w", "--window", type=int, default=WINDOW, help="播放中保留切片数")
    ap.add_argument("-r", "--reload", type=int, default=30,
                    help="每隔多少分钟重新拉取远程列表，0=只拉一次")
    a = sanitize_args(ap)
    IDLE_SEC = a.idle
    SEG_ROOT = a.segdir
    WINDOW = a.window
    os.makedirs(SEG_ROOT, exist_ok=True)
    purge_stale_cache()

    text = load_playlist(a.src, a.ua)
    chans = parse_m3u(text)
    if a.filter:
        chans = [c for c in chans if a.filter in c[0]]
    if not chans:
        log("没解析到任何频道，检查列表格式（要有 #EXTINF 行和地址行）")
        sys.exit(1)

    for i, (name, group, logo, url) in enumerate(chans, 1):
        CHANS[i] = ChannelRelay(i, name, group, logo, url, a.ua)
    log(f"解析到 {len(CHANS)} 个频道（谁在播才缓存谁，默认空闲 {IDLE_SEC}s 后清盘）")

    socketserver.ThreadingTCPServer.allow_reuse_address = True
    httpd, port = bind_server(a.port, Handler)
    httpd.daemon_threads = True

    write_local_playlist(a.out, port)
    threading.Thread(target=janitor_loop, daemon=True).start()
    log(f"本地播放列表已写出 → {a.out}")
    log(f"服务地址 → http://127.0.0.1:{port}/playlist.m3u")
    log(f"状态查看 → http://127.0.0.1:{port}/status")
    log(f"局域网访问 → http://<本机IP>:{port}/playlist.m3u")
    if a.src.startswith("http"):
        log(f"远程列表每 {a.reload} 分钟自动重拉（0=不重拉）")

    if a.reload > 0 and a.src.startswith("http"):
        threading.Thread(target=reload_loop, args=(a.src, a.ua, a.reload, a.filter, a.out, port),
                         daemon=True).start()

    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        for c in CHANS.values():
            c.stop("程序退出")
        log("已停止")


def write_local_playlist(path, port):
    with open(path, "w", encoding="utf-8") as f:
        f.write("#EXTM3U\n")
        for i, c in CHANS.items():
            g = f' group-title="{c.group}"' if c.group else ""
            lg = f' tvg-logo="{c.logo}"' if c.logo else ""
            f.write(f"#EXTINF:-1{lg}{g},{c.name}\n")
            f.write(f"http://127.0.0.1:{port}/ch/{i}/live.m3u8\n")


def reload_loop(src, ua, minutes, flt, out, port):
    """定时重拉远程列表：更新地址、收录新频道，正在播的不动。"""
    while True:
        time.sleep(minutes * 60)
        try:
            text = load_playlist(src, ua)
            chans = parse_m3u(text)
            if flt:
                chans = [c for c in chans if flt in c[0]]
            if not chans:
                log("重拉结果为空，跳过本次更新")
                continue
            added = updated = 0
            with LOCK:
                for i, (name, group, logo, url) in enumerate(chans, 1):
                    ch = CHANS.get(i)
                    if ch is None:
                        CHANS[i] = ChannelRelay(i, name, group, logo, url, ua)
                        added += 1
                    else:
                        new_entry = ChannelRelay._to_m3u8(url)
                        if ch.entry != new_entry:
                            ch.entry = new_entry
                            updated += 1
            write_local_playlist(out, port)
            log(f"列表已刷新：新增 {added}，更新 {updated}，总计 {len(CHANS)}")
        except Exception as e:
            log(f"列表重拉失败：{e}")


if __name__ == "__main__":
    main()
