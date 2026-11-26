#!/usr/bin/env python3
"""
IPTV m3u 播放列表批量中转器
================================
解决两类问题：
  1. 源站播放 token 只有约 30 秒寿命 → 后台自动续期，播放器无感
  2. 整份 m3u 里几十上百个频道要同时处理 → 按需启动，不播就不续，省流量不惹源站

原理：
  把 m3u 里每个频道的原始地址（通常是 /play/live.php?...&extension=ts）改写成
  extension=m3u8，后台每 18 秒换一次 token、抢先下载切片、重拼成本地滚动 m3u8。
  播放器只读本地地址，因此能无限连续播放。

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
    -o/--out    生成到本地的 m3u 文件名，默认 /tmp/local_playlist.m3u
    -u/--ua     请求用的 User-Agent，默认 MAG 机顶盒 UA
    -i/--idle   停看多少秒后停止缓存并删除切片，默认 60
    -f/--filter 只处理名字包含该关键字的频道
    -s/--segdir 切片缓存目录
    -w/--window 保留切片数，每片约 10 秒
    -r/--reload 每隔多少分钟重新拉取远程列表，0 表示只拉一次，默认 30
    --multi     允许同时缓存多个频道（默认关，只缓存当前在看的那个）

本版在原文件基础上新增（其余逻辑保持原样）：
  · 只缓存当前在看的频道：播放器请求哪个频道才启动哪个，切台时旧频道立即
    停止续期并清空它的分片目录，不会在后台偷偷缓存没看的频道
  · 停看即清理：超过 -i 秒没有任何播放器请求（清单和切片都不请求），立即停线程、
    清内存分片池、删掉该频道的整个缓存目录；程序退出时也清理
  · 顺带修掉的几处会导致播不出/卡住的问题：后台续期不再自己刷新空闲计时、
    302 取地址判断、分片相对路径拼接、清单里的 EVENT 标记、失败分片无限重试、
    首次请求空清单
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
WINDOW = 30                # 本地保留切片数（每片约 10s）

# ---- 本版新增：按需缓存相关 ----
SINGLE_ACTIVE = True       # 只缓存当前在看的那个频道；--multi 可关掉
FIRST_SEG_WAIT = 6.0       # 首次请求清单时，最多等首个分片多久（避免播放器拿到空清单）
SEG_FAIL_MAX = 3           # 单个分片下载失败重试次数上限，超了就丢，避免死循环
SWITCH_GRACE = 5.0         # 切台后给旧频道几秒宽限再清盘，防止播放器预取造成来回打架
# 默认放在脚本同级目录，避免 /tmp 容量不足（部分系统 /tmp 只有 256MB）
SEG_ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "segs")

# ---------------------------------------------------------------- 内置远程列表
# 不带参数直接运行时就加载这份列表。想换成别的，命令行传路径/URL 即可覆盖。
DEFAULT_PLAYLIST = (
    "https://ghfast.top/https://raw.githubusercontent.com/SuperNinjap/iptv/main/USA.m3u"
)
# 远程列表本地缓存：网络拉取失败时回退用它
CACHE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".playlist_cache.m3u")


def log(*a):
    print(time.strftime("[%H:%M:%S]"), *a, flush=True)


# ---------------------------------------------------------------- 列表加载
def load_playlist(src, ua=MAG_UA, timeout=90):
    """从 本地文件 / http(s) URL / stdin 读取 m3u 文本，带缓存回退。"""
    # stdin
    if src == "-":
        log("从标准输入读取列表")
        return sys.stdin.read()

    # 远程 URL
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

    # 本地文件
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
        self.segs = OrderedDict()
        self.lock = threading.Lock()
        self.running = False
        self.last_touch = time.time()
        self.fail = 0
        self.seg_dir = os.path.join(SEG_ROOT, str(idx))
        # 本版新增：每启动一次 +1，用来让上一轮线程立刻退出，避免停台后还在偷偷下载
        self.gen = 0
        self.start_lock = threading.Lock()
        self.stop_at = 0.0      # 被切走后的清盘时间点，0 表示不待停

    @staticmethod
    def _to_m3u8(u):
        if "extension=" in u:
            return re.sub(r"extension=\w*", "extension=m3u8", u)
        if ".m3u8" in u:
            return u
        sep = "&" if "?" in u else "?"
        return u + sep + "extension=m3u8"

    def touch(self):
        self.last_touch = time.time()
        self.stop_at = 0.0      # 又有播放请求了，取消“待停止”

    # ---------------- 本版新增：启停与清盘 ----------------
    def start(self):
        """启动续期+下载线程（只有播放器真请求这个频道才会走到这里）。"""
        with self.start_lock:
            if self.running:
                return
            self.gen += 1
            g = self.gen
            self.running = True
            self.fail = 0
            self.last_touch = time.time()
            threading.Thread(target=self.refresher, args=(g,), daemon=True).start()
            threading.Thread(target=self.downloader, args=(g,), daemon=True).start()

    def stop(self, purge=True):
        """停止续期、清空内存分片池、删掉整个缓存目录。"""
        self.running = False
        self.gen += 1          # 旧线程看到代际变化就退出，不再下载
        self.stop_at = 0.0
        with self.lock:
            self.segs.clear()
        if purge:
            self.purge()
        log(f"[{self.idx}]{self.name} 已停止缓存" + ("，缓存目录已删除" if purge else ""))

    def purge(self):
        """删除本频道整个分片目录（含残留文件）。"""
        try:
            if os.path.isdir(self.seg_dir):
                shutil.rmtree(self.seg_dir, ignore_errors=True)
        except Exception:
            pass

    def cache_bytes(self):
        total = 0
        try:
            for n in os.listdir(self.seg_dir):
                try:
                    total += os.path.getsize(os.path.join(self.seg_dir, n))
                except OSError:
                    pass
        except OSError:
            pass
        return total

    def has_ready(self):
        with self.lock:
            return any(i["local"] for i in self.segs.values())

    def wait_first(self, timeout=FIRST_SEG_WAIT):
        """等首个分片落盘，最多 timeout 秒。避免播放器第一次就拿到空清单卡住。"""
        end = time.time() + timeout
        while time.time() < end:
            if self.has_ready():
                return True
            if not self.running:
                break
            time.sleep(0.2)
        return self.has_ready()

    # 取新 token 得到 m3u8 地址
    def _playlist_url(self):
        # 不自动跟随跳转，自己读 Location：
        # 有些源站是直接 200 返回清单，原来用 geturl() 判断会误判成失败（返回 None）
        class _NoRedirect(urllib.request.HTTPRedirectHandler):
            def redirect_request(self, req, fp, code, msg, headers, newurl):
                return None

        opener = urllib.request.build_opener(_NoRedirect)
        req = urllib.request.Request(self.entry, headers={"User-Agent": self.ua})
        try:
            with opener.open(req, timeout=20) as r:
                loc = r.headers.get("Location")
                return urljoin(self.entry, loc) if loc else self.entry
        except urllib.error.HTTPError as e:
            loc = e.headers.get("Location") if e.headers else None
            if loc:
                return urljoin(self.entry, loc)
            return f"__ERR_{e.code}"
        except Exception as e:
            return f"__ERR_{type(e).__name__}"

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
                # 相对路径必须按清单地址拼，原来拼根域名会 404
                url = urljoin(base, line)
                mm = re.search(r"_(\d+)\.ts", line)
                out.append((int(mm.group(1)) if mm else bseq + i, url, dur))
                i += 1
        return out

    def refresher(self, g):
        while self.running and self.gen == g:
            # 注意：原版这里有一句 self.touch()，等于后台自己给自己续命，
            # 空闲回收永远不成立，所以看过的频道会一直缓存在后台。
            # 现在删掉它：只有播放器真来请求清单/切片才刷新空闲计时。
            pl = self._playlist_url()
            if pl and not pl.startswith("__ERR"):
                try:
                    req = urllib.request.Request(pl, headers={"User-Agent": self.ua})
                    with urllib.request.urlopen(req, timeout=15) as r:
                        text = r.read().decode("utf-8", "ignore")
                    items = self._parse(text, pl)
                    with self.lock:
                        new = 0
                        for seq, url, dur in items:
                            if seq not in self.segs:
                                self.segs[seq] = {"url": url, "dur": dur,
                                                  "local": None, "tries": 0}
                                new += 1
                        # 缓存上限只比播放窗口多留几个，避免磁盘被吃满
                        while len(self.segs) > WINDOW + 5:
                            old_seq, info = self.segs.popitem(last=False)
                            # 关键：淘汰时同步删除磁盘文件，否则磁盘会一直涨
                            lp = info.get("local")
                            if lp and os.path.exists(lp):
                                try:
                                    os.remove(lp)
                                except OSError:
                                    pass
                    self.fail = 0
                    log(f"[{self.idx}]{self.name} 续期OK 新增{new} 池{len(self.segs)}")
                except Exception as e:
                    self.fail += 1
                    log(f"[{self.idx}]{self.name} 拉列表失败 {e}")
            else:
                self.fail += 1
                log(f"[{self.idx}]{self.name} 取token失败 {pl}")
                if self.fail >= 3:
                    log(f"[{self.idx}]{self.name} 连续失败，暂停 30s")
                    for _ in range(30):
                        if not self.running or self.gen != g:
                            return
                        time.sleep(1)

            # 空闲回收：停线程 + 清内存分片池 + 删掉整个缓存目录
            if time.time() - self.last_touch > IDLE_SEC:
                log(f"[{self.idx}]{self.name} 空闲超时（{IDLE_SEC} 秒没有播放请求），停止缓存并删除切片目录")
                self.stop()
                break
            # 分段睡：停台/切台时能立刻退出，不用等满一个刷新周期
            for _ in range(int(REFRESH_INTERVAL)):
                if not self.running or self.gen != g:
                    return
                # 被切到别的台了：宽限到点就停线程 + 删掉这个台的缓存目录
                if self.stop_at and time.time() >= self.stop_at:
                    log(f"[{self.idx}]{self.name} 已切到其它频道，停止缓存并删除切片目录")
                    self.stop()
                    return
                # 停看超时：立刻停线程、清内存池、删整个切片目录
                if time.time() - self.last_touch > IDLE_SEC:
                    log(f"[{self.idx}]{self.name} 停看超过 {IDLE_SEC} 秒，停止缓存并删除切片目录")
                    self.stop()
                    return
                time.sleep(1)

    def downloader(self, g):
        os.makedirs(self.seg_dir, exist_ok=True)
        while self.running and self.gen == g:
            todo = []
            with self.lock:
                for s, i in self.segs.items():
                    if i["local"] is None:
                        todo.append((s, i["url"]))
            for s, u in todo:
                if not self.running or self.gen != g:
                    break
                p = os.path.join(self.seg_dir, f"{s}.ts")
                tmp = p + ".part"
                try:
                    req = urllib.request.Request(u, headers={"User-Agent": self.ua})
                    with urllib.request.urlopen(req, timeout=25) as r, open(tmp, "wb") as f:
                        shutil.copyfileobj(r, f)
                    os.replace(tmp, p)      # 先写 .part 再改原子改名，播放器不会读到半截文件
                    if os.path.getsize(p) > 1000:
                        with self.lock:
                            if s in self.segs:
                                self.segs[s]["local"] = p
                except Exception:
                    try:
                        if os.path.exists(tmp):
                            os.remove(tmp)
                    except OSError:
                        pass
                    # 失败不再无限重拉：超过次数就丢掉这一片
                    with self.lock:
                        it = self.segs.get(s)
                        if it is not None:
                            it["tries"] = it.get("tries", 0) + 1
                            if it["tries"] >= SEG_FAIL_MAX:
                                self.segs.pop(s, None)
            time.sleep(1.5)
        # 线程退出时如果是被停掉的，再兜底删一次目录（防止有残留文件）
        if not self.running:
            self.purge()

    def build_m3u8(self):
        with self.lock:
            ready = sorted([(s, i) for s, i in self.segs.items() if i["local"]])
        if not ready:
            return ("#EXTM3U\n#EXT-X-VERSION:3\n#EXT-X-TARGETDURATION:14\n"
                    "#EXT-X-MEDIA-SEQUENCE:0\n")
        ready = ready[-WINDOW:]
        first = ready[0][0]
        # 这里是滑窗（老分会淘汰），不能标 EVENT，否则播放器会认为分片丢了
        td = max(10, int(max(i["dur"] for _, i in ready) + 0.999))
        out = ["#EXTM3U", "#EXT-X-VERSION:3", f"#EXT-X-TARGETDURATION:{td}",
               f"#EXT-X-MEDIA-SEQUENCE:{first}"]
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
IDLE_SEC = 60              # 停看多少秒后停线程并删缓存（-i 可调）
LOCK = threading.Lock()


def _stop_others(keep_idx):
    """只缓存当前在看的那个频道：其余正在跑的台排队待停，宽限几秒后清盘。
    宽限是为了防播放器同时预取多个台时互相打架；期间若被请求就自动取消。"""
    now = time.time()
    with LOCK:
        items = list(CHANS.items())
    n = 0
    for i, c in items:
        if i != keep_idx and c.running and not c.stop_at:
            c.stop_at = now + SWITCH_GRACE
            n += 1
    if n:
        log(f"切台：{n} 个其它频道将在 {SWITCH_GRACE:.0f} 秒后停止并清理缓存")


def get_relay(idx, activate=True):
    """activate=False 只刷新空闲计时（如取切片）；True 表示播放器在播这个台。"""
    with LOCK:
        ch = CHANS.get(idx)
    if not ch:
        return None
    ch.touch()                     # 只有播放器真来请求才算“有人在看”
    if activate:
        if SINGLE_ACTIVE:
            _stop_others(idx)
        ch.start()
    return ch


class Handler(http.server.BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, body, ctype, headers=None):
        if isinstance(body, str):
            body = body.encode()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        for k, v in (headers or {}).items():
            self.send_header(k, v)
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
        # 单频道 m3u8
        m = re.match(r"^/ch/(\d+)/live\.m3u8$", path)
        if m:
            ch = get_relay(int(m.group(1)))
            if not ch:
                return self.send_error(404)
            # 第一次请求时切片可能还没到，等首片落盘再给清单，避免播放器拿到空清单卡缓冲
            if not ch.has_ready():
                ch.wait_first()
            return self._send(ch.build_m3u8(), "application/vnd.apple.mpegurl",
                              {"Cache-Control": "no-store, no-cache, must-revalidate"})
        # 切片
        m = re.match(r"^/ch/(\d+)/seg/(\d+)\.ts$", path)
        if m:
            idx, seq = int(m.group(1)), m.group(2)
            ch = get_relay(idx, activate=False)   # 取切片也算在看，刷新空闲计时
            if ch is None:
                return self.send_error(404)
            p = os.path.join(SEG_ROOT, str(idx), f"{seq}.ts")
            if os.path.exists(p):
                data = open(p, "rb").read()
                return self._send(data, "video/mp2t")
            return self.send_error(404)
        # 状态（大列表只显示正在跑的 + 摘要，避免输出上万行）
        if path == "/status":
            running = [(i, c) for i, c in CHANS.items() if c.running]
            total_mb = sum(c.cache_bytes() for _, c in running) / 1048576.0
            head = [f"频道总数: {len(CHANS)}   正在缓存: {len(running)}   "
                    f"缓存合计: {total_mb:.1f} MB   "
                    f"模式: {'只缓存当前频道' if SINGLE_ACTIVE else '允许多台同时缓存'}"]
            rows = [f"#{i} {c.name} | 分组={c.group} | 切片池={len(c.segs)} | "
                    f"失败={c.fail} | 上次请求={int(time.time()-c.last_touch)}秒前 | "
                    f"缓存={c.cache_bytes()/1048576.0:.1f}MB"
                    for i, c in running]
            if not running:
                rows = [f"(当前没有频道在播放；播放器请求某个频道才会启动缓存，"
                        f"停看 {IDLE_SEC} 秒后自动删除缓存)"]
            return self._send("\n".join(head + [""] + rows), "text/plain; charset=utf-8")
        self.send_error(404)


def sanitize_args(ap):
    """兼容 Android App / 内嵌 Python 环境里不可靠的参数传递。

    真实踩到的情况：
      · App 把 "-p 8080" 拆开，只把 "8080" 塞进来 → 被当成列表文件路径
      · App 把整串参数合成一个带空格的字符串 → argparse 认不出来
      · 参数里混进选项片段 → 被当成文件路径
    """
    raw = sys.argv[1:]

    # 情况 A：整个参数串被合并成一项，例如 "-p 8080 -f NL"
    if len(raw) == 1 and " " in raw[0]:
        log(f"参数被合并成一项 {raw[0]!r}，自动拆分")
        raw = raw[0].split()

    a = ap.parse_args(raw)

    # 情况 B：位置参数漏进来纯数字，例如 App 弄丢了 "-p" 只剩 "8080"
    if a.src and re.fullmatch(r"\d{2,5}", a.src.strip()):
        log(f"参数 {a.src!r} 是纯数字，判定为端口号（App 传参丢了 -p），按 -p {a.src} 处理")
        a.port = int(a.src)
        a.src = DEFAULT_PLAYLIST

    # 情况 C：位置参数像个选项片段
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


def main():
    global IDLE_SEC, SEG_ROOT, WINDOW, SINGLE_ACTIVE
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("src", nargs="?", default=DEFAULT_PLAYLIST,
                    help="m3u 来源：本地路径 / http(s) 地址 / - (stdin)；不填用内置远程列表")
    ap.add_argument("-p", "--port", type=int, default=8080)
    ap.add_argument("-o", "--out",
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "local_playlist.m3u"),
                    help="生成的本地列表路径（默认脚本同目录，Android 上别用 /tmp）")
    ap.add_argument("-u", "--ua", default=MAG_UA)
    ap.add_argument("-i", "--idle", type=int, default=60,
                    help="停看多少秒后停止缓存并删除切片目录，默认 60")
    ap.add_argument("-f", "--filter", default="")
    ap.add_argument("-s", "--segdir", default=SEG_ROOT, help="切片缓存目录，注意留足空间")
    ap.add_argument("-w", "--window", type=int, default=WINDOW, help="保留切片数，每片约10秒")
    ap.add_argument("-r", "--reload", type=int, default=30,
                    help="每隔多少分钟重新拉取远程列表，0=只拉一次")
    ap.add_argument("--multi", action="store_true",
                    help="允许同时缓存多个频道（默认只缓存当前在看的那个）")
    a = sanitize_args(ap)
    IDLE_SEC = a.idle
    SEG_ROOT = a.segdir
    WINDOW = a.window
    SINGLE_ACTIVE = not a.multi
    os.makedirs(SEG_ROOT, exist_ok=True)
    # 清掉上次异常退出（拔电/强杀）留下的分片，避免一启动就带着旧缓存
    for n in os.listdir(SEG_ROOT):
        p = os.path.join(SEG_ROOT, n)
        try:
            if os.path.isdir(p):
                shutil.rmtree(p, ignore_errors=True)
            else:
                os.remove(p)
        except OSError:
            pass

    text = load_playlist(a.src, a.ua)
    chans = parse_m3u(text)
    if a.filter:
        chans = [c for c in chans if a.filter in c[0]]
    if not chans:
        log("没解析到任何频道，检查列表格式（要有 #EXTINF 行和地址行）")
        sys.exit(1)

    for i, (name, group, logo, url) in enumerate(chans, 1):
        CHANS[i] = ChannelRelay(i, name, group, logo, url, a.ua)
    log(f"解析到 {len(CHANS)} 个频道")

    # 先抢端口，拿到真实监听端口后所有地址都按它写
    socketserver.ThreadingTCPServer.allow_reuse_address = True
    httpd, port = bind_server(a.port, Handler)
    httpd.daemon_threads = True

    # 生成本地 m3u 文件
    write_local_playlist(a.out, port)
    log(f"本地播放列表已写出 → {a.out}")
    log(f"服务地址 → http://127.0.0.1:{port}/playlist.m3u")
    log(f"状态查看 → http://127.0.0.1:{port}/status")
    log(f"局域网访问 → http://<本机IP>:{port}/playlist.m3u")
    if a.src.startswith("http"):
        log(f"远程列表每 {a.reload} 分钟自动重拉（0=不重拉）")

    # 定时重拉远程列表，刷新 token / 收录新频道
    if a.reload > 0 and a.src.startswith("http"):
        threading.Thread(target=reload_loop, args=(a.src, a.ua, a.reload, a.filter, a.out, port),
                         daemon=True).start()

    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        for c in CHANS.values():
            c.stop()          # 退出时也把缓存目录清干净
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
