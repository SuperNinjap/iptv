#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
IPTV m3u 播放列表批量中转器（按需缓存 · 自动清理 · 修复卡缓冲版）
==================================================================
解决四件事：
  1. 源站播放 token 只有约 30 秒寿命 → 后台自动续期，播放器无感
  2. 谁在看才缓存谁，没看的一律不动
  3. 播完即停、停即清盘，播放中也只留一个滑动窗口
  4. 播放器不再"卡在缓冲中"——第一次请求就等到分片，清单可续取

本版相对上一版的关键修正（都是导致卡缓冲的直接原因）：
  · 清单响应加 no-cache：播放器拿到空清单后必须重新来问，不能吃缓存
  · 首次请求最多等 10 秒拿到 2 个分片再回清单，不再秒回空清单
  · 对外清单只给最近 4 个分片（约 40 秒），播放器不会从几分钟前的地方起播
    磁盘保留 15 片，播放器正在读的片一定还在，不会 404 卡死
  · 主清单（多码率 master m3u8）自动下钻一层，取子清单再解析
  · 分片相对路径统一 urljoin(base, line)，base 取重定向后的真实地址
  · 分片被请求但还没下完时，短等 3 秒再回，减少播放器 404 报错
  · 后台续期不再自己给自己续命，只有播放器真实请求才刷新活跃时间

用法：
    python3 iptv_relay_修复卡缓冲.py                    # 用内置远程列表
    python3 iptv_relay_修复卡缓冲.py 你的列表.m3u        # 用本地文件
    python3 iptv_relay_修复卡缓冲.py -p 8080 -o local.m3u
    cat 你的列表.m3u | python3 iptv_relay_修复卡缓冲.py -

参数：
    src         列表来源：本地路径 / http(s) 地址 / - (stdin)，不填用内置远程列表
    -p/--port   本地端口，默认 8080（被占会自动往后找）
    -o/--out    生成的本地 m3u 路径，默认脚本同目录
    -u/--ua     请求用的 User-Agent，默认 MAG 机顶盒 UA
    -i/--idle   播放器多久没请求就停止缓存并清盘（秒），默认 60
    -f/--filter 只处理名字包含该关键字的频道
    -s/--segdir 切片缓存目录
    -w/--window 磁盘上保留多少个分片，默认 15
    -r/--reload 每隔多少分钟重新拉取远程列表，0 表示只拉一次，默认 30
"""

import argparse
import http.server
import math
import os
import re
import shutil
import socket
import socketserver
import sys
import threading
import time
import urllib.error
import urllib.request
from collections import OrderedDict
from urllib.parse import urljoin, urlsplit

MAG_UA = ("Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 "
          "(KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3")

REFRESH_INTERVAL = 12      # 清单刷新间隔：token 活约 30s，12s 换一次足够安全
WINDOW = 15                # 磁盘保留分片数（每片约 6~10 秒）
PLAYLIST_SEGS = 4          # 对外清单暴露的最近分片数，太多播放器会落后
IDLE_SEC = 60              # 播放器多久没请求 → 停止缓存 + 清盘
FIRST_WAIT = 10.0          # 首次请求清单时，最多等多久拿首个分片
FIRST_MIN_SEGS = 2         # 等够几个分片就立刻返回（不等满）
SEG_DL_LIMIT = 6           # 单轮最多补几个分片，防止一次爆下载
MAX_FAILS = 4              # 单个分片最多试几次，超了就放弃（不无限重试）
SEG_TIMEOUT = 15           # 单个分片下载超时（秒）
PL_TIMEOUT = 15            # 拉清单超时（秒）

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
SEG_ROOT = os.path.join(BASE_DIR, "segs")

DEFAULT_PLAYLIST = (
    "https://ghfast.top/https://raw.githubusercontent.com/SuperNinjap/iptv/main/USA.m3u"
)
CACHE_FILE = os.path.join(BASE_DIR, ".playlist_cache.m3u")


def log(*a):
    print(time.strftime("[%H:%M:%S]"), *a, flush=True)


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    """自己接管 3xx：直接读 Location，不去猜 geturl()。"""

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
        self.entry = self._to_entry(url)

        self.segs = OrderedDict()          # sid -> {url, dur, local, fails, key}
        self.keymap = OrderedDict()        # 分片 key -> sid（去重用）
        self.next_sid = 1

        self.lock = threading.Lock()
        self.pl_lock = threading.Lock()
        self.pl_time = 0.0                 # 上次成功/尝试拉清单的时间
        self.pl_base = None                # 清单真实地址（重定向后）
        self.pl_ok_ts = 0.0                # 上次成功时间

        self.running = False
        self.stop_evt = threading.Event()
        self.last_client = 0.0             # 只有播放器真实请求才更新
        self.play_pos = None
        self.fail = 0
        self.last_err = ""
        self.thread = None

        self.seg_dir = os.path.join(SEG_ROOT, str(idx))

    # ------------------------------------------------ 地址
    @staticmethod
    def _to_entry(u):
        """把播放地址改成要 m3u8 的形态。"""
        if "extension=" in u:
            return re.sub(r"extension=\w*", "extension=m3u8", u)
        if ".m3u8" in u:
            return u
        if re.search(r"\.ts(\?|$)", u, re.I):
            return re.sub(r"\.ts(\?|$)", r".m3u8\1", u, flags=re.I)
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
        self.running = True
        self.last_client = time.time()
        self.fail = 0
        self.pl_time = 0.0
        os.makedirs(self.seg_dir, exist_ok=True)
        self.thread = threading.Thread(target=self.worker, daemon=True)
        self.thread.start()

    def stop(self, reason="空闲"):
        """停线程 + 清内存池 + 删整目录（缓存不留在盘上）。"""
        was_running = self.running
        self.running = False
        self.stop_evt.set()
        self.play_pos = None
        with self.lock:
            self.segs.clear()
            self.keymap.clear()
        shutil.rmtree(self.seg_dir, ignore_errors=True)
        if was_running:
            log(f"[{self.idx}]{self.name} {reason}，已停止缓存并清空磁盘")

    # ------------------------------------------------ 源站清单
    def _read_list(self, url, depth=0):
        """拿一份播放清单。302 自己跟，直接 200 返回清单也认。"""
        if depth > 4:
            self.last_err = "__ERR_too_many_redirect"
            return None, self.last_err
        req = urllib.request.Request(url, headers={
            "User-Agent": self.ua,
            "Accept": "*/*",
            "Connection": "close",
        })
        try:
            with _OPENER.open(req, timeout=PL_TIMEOUT) as r:
                raw = r.read()
                body = raw.decode("utf-8", "ignore")
                final = r.geturl() or url
                if body.lstrip().upper().startswith("#EXTM3U") or "#EXTINF" in body[:8000]:
                    return final, body
                loc = r.headers.get("Location")
                if loc:
                    return self._read_list(urljoin(final, loc), depth + 1)
                self.last_err = "__ERR_not_playlist"
                return None, self.last_err
        except urllib.error.HTTPError as e:
            loc = e.headers.get("Location") if e.headers else None
            if loc:
                return self._read_list(urljoin(url, loc), depth + 1)
            self.last_err = f"__ERR_{e.code}"
            return None, self.last_err
        except Exception as e:
            self.last_err = f"__ERR_{type(e).__name__}"
            return None, self.last_err

    def _refresh(self):
        """拉一次清单并把分片收进池子。返回是否成功。"""
        with self.pl_lock:
            now = time.time()
            # 成功时按 worker 的节奏走；失败时退避，越错越慢，别打爆源站
            backoff = 3.0 if self.fail == 0 else min(30.0, 3.0 * self.fail)
            if now - self.pl_time < backoff:
                return False
            self.pl_time = now

            pl, text = self._read_list(self.entry)
            if not pl or not text or text.startswith("__ERR"):
                self.fail += 1
                if self.fail == 1 or self.fail % 5 == 0:
                    log(f"[{self.idx}]{self.name} 取地址失败 {text} {self.last_err}")
                return False

            items, subs = self._parse(text, pl)
            # 多码率主清单：往下钻一层拿子清单
            if not items and subs:
                sub = self._pick_variant(text, pl, subs)
                pl2, text2 = self._read_list(sub)
                if text2 and not text2.startswith("__ERR"):
                    items, subs2 = self._parse(text2, pl2)
                    if items:
                        pl = pl2

            if not items:
                self.fail += 1
                if self.fail == 1 or self.fail % 5 == 0:
                    log(f"[{self.idx}]{self.name} 清单里没解析到分片（主清单层数过深或格式不认识）")
                return False

            self.pl_base = pl
            self.pl_ok_ts = time.time()
            self.fail = 0
            added = self._ingest(items)
            if added:
                log(f"[{self.idx}]{self.name} 续期OK 新增{added} 池{len(self.segs)}")
            return True

    @staticmethod
    def _pick_variant(text, base, subs):
        """主清单里挑一路码率：取带宽最高的那路。"""
        best_url, best_bw = subs[0], -1
        last_bw = -1
        for line in text.splitlines():
            line = line.strip()
            if line.upper().startswith("#EXT-X-STREAM-INF"):
                m = re.search(r"BANDWIDTH=(\d+)", line)
                last_bw = int(m.group(1)) if m else 0
            elif line and not line.startswith("#"):
                u = urljoin(base, line)
                if u.split("?")[0].lower().endswith((".m3u8", ".m3u")) and last_bw > best_bw:
                    best_url, best_bw = u, last_bw
                last_bw = -1
        return best_url

    @staticmethod
    def _parse(text, base):
        """返回 (分片列表 [(序号, url, 时长)], 子清单列表)。"""
        m = re.search(r"#EXT-X-MEDIA-SEQUENCE:(\d+)", text)
        bseq = int(m.group(1)) if m else 0
        items, subs = [], []
        dur, i = 10.0, 0
        for line in text.splitlines():
            line = line.strip()
            if not line:
                continue
            if line.startswith("#EXTINF:"):
                try:
                    dur = float(line.split(":", 1)[1].split(",")[0])
                except Exception:
                    dur = 10.0
                continue
            if line.startswith("#"):
                continue
            u = urljoin(base, line)
            low = u.split("?")[0].lower()
            if low.endswith((".m3u8", ".m3u")):
                subs.append(u)
                continue
            items.append((bseq + i, u, dur))
            i += 1
        return items, subs

    @staticmethod
    def _seg_key(u):
        """分片去重用的 key：去掉 token 的路径。"""
        p = urlsplit(u)
        path = p.path
        if re.search(r"\d", path):
            return path
        return path + "?" + p.query

    def _ingest(self, items):
        """把清单里的分片收进池子；用本地连续编号，避免源站序号乱跳。"""
        added = 0
        with self.lock:
            for _hint, url, dur in items:
                key = self._seg_key(url)
                sid = self.keymap.get(key)
                if sid is not None and sid in self.segs:
                    self.segs[sid]["url"] = url
                    self.segs[sid]["dur"] = dur
                    continue
                sid = self.next_sid
                self.next_sid += 1
                self.keymap[key] = sid
                self.segs[sid] = {"url": url, "dur": dur, "local": None,
                                  "fails": 0, "key": key}
                added += 1
            # keymap 别无限涨
            while len(self.keymap) > max(WINDOW * 6, 60):
                self.keymap.popitem(last=False)
        return added

    # ------------------------------------------------ 下载
    def _download_one(self, sid, url):
        p = os.path.join(self.seg_dir, f"{sid}.ts")
        tmp = p + ".part"
        try:
            req = urllib.request.Request(url, headers={
                "User-Agent": self.ua,
                "Accept": "*/*",
                "Connection": "close",
            })
            with urllib.request.urlopen(req, timeout=SEG_TIMEOUT) as r, open(tmp, "wb") as f:
                shutil.copyfileobj(r, f, 65536)
            if os.path.getsize(tmp) < 1000:
                os.remove(tmp)
                raise ValueError("分片太小")
            os.replace(tmp, p)              # 原子替换，播放器读不到半截文件
        except Exception:
            try:
                if os.path.exists(tmp):
                    os.remove(tmp)
            except OSError:
                pass
            with self.lock:
                it = self.segs.get(sid)
                if it is not None:
                    it["fails"] = it.get("fails", 0) + 1
            return False

        keep = False
        with self.lock:
            it = self.segs.get(sid)
            if it is not None:
                it["local"] = p
                keep = True
        if not keep:                        # 下载途中已被淘汰 → 不留
            try:
                os.remove(p)
            except OSError:
                pass
            return False
        return True

    def _download_batch(self):
        with self.lock:
            pending = [(s, i["url"]) for s, i in self.segs.items()
                       if i["local"] is None and i.get("fails", 0) < MAX_FAILS]
        if not pending:
            return
        # 新分片优先下：直播最要紧的是最新的那几片
        pending.sort(key=lambda x: x[0], reverse=True)
        budget = time.time() + 6
        n = 0
        for s, u in pending:
            if not self.running or n >= SEG_DL_LIMIT or time.time() > budget:
                break
            self._download_one(s, u)
            n += 1

    # ------------------------------------------------ 缓存回收
    def prune(self):
        """播放中只留最近 WINDOW 个分片：字典裁 + 磁盘删，双保险。"""
        dropped = []
        with self.lock:
            while len(self.segs) > WINDOW:
                _, info = self.segs.popitem(last=False)
                self.keymap.pop(info.get("key"), None)
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
                # 5 秒内的新文件留给下载线程收尾，避免竞态误删
                if fn not in keep and age > 5:
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
    def ready_segs(self):
        with self.lock:
            return sorted([(s, i) for s, i in self.segs.items() if i["local"]])

    def ready_count(self):
        with self.lock:
            return sum(1 for i in self.segs.values() if i["local"])

    def wait_first(self, timeout=FIRST_WAIT):
        """等首批分片就绪；等够 FIRST_MIN_SEGS 个就立刻返回。"""
        start = time.time()
        while time.time() - start < timeout:
            if self.ready_count() >= FIRST_MIN_SEGS:
                return True
            if time.time() - start > 2 and self.pl_ok_ts == 0:
                # 后台还没拉回清单，这里主动催一次，别干等
                self._refresh()
            time.sleep(0.15)
        return self.ready_count() > 0

    def build_m3u8(self):
        ready = self.ready_segs()
        head = ["#EXTM3U", "#EXT-X-VERSION:3"]
        if not ready:
            # 给一个短 targetduration 的空清单：播放器会很快再回来问
            return "\n".join(head + ["#EXT-X-TARGETDURATION:4",
                                     "#EXT-X-MEDIA-SEQUENCE:0"]) + "\n"

        # 只取尾部连续的几个分片：避免中间缺口让播放器卡住
        sids = [s for s, _ in ready]
        sidset = set(sids)
        tail = [sids[-1]]
        cur = sids[-1]
        while len(tail) < PLAYLIST_SEGS:
            cur -= 1
            if cur in sidset:
                tail.append(cur)
            else:
                break
        tail.reverse()

        info = {s: i for s, i in ready}
        max_dur = max(info[s]["dur"] for s in tail)
        td = max(4, int(math.ceil(max_dur)))

        out = head + [f"#EXT-X-TARGETDURATION:{td}",
                      f"#EXT-X-MEDIA-SEQUENCE:{tail[0]}"]
        for s in tail:
            out.append(f"#EXTINF:{info[s]['dur']:.3f},")
            out.append(f"/ch/{self.idx}/seg/{s}.ts")
        return "\n".join(out) + "\n"

    # ------------------------------------------------ 后台线程
    def _refresh_interval(self):
        """按分片时长自适应：分片短就刷得勤一点，否则清单会给空窗。"""
        dur = 0.0
        with self.lock:
            recent = list(self.segs.values())[-PLAYLIST_SEGS:]
            for i in recent:
                dur += i.get("dur") or 10.0
        if dur <= 0:
            return REFRESH_INTERVAL
        return max(2.0, min(float(REFRESH_INTERVAL), dur / 2.0))

    def worker(self):
        os.makedirs(self.seg_dir, exist_ok=True)
        last_refresh = 0.0
        try:
            while self.running:
                now = time.time()
                need = (now - last_refresh >= self._refresh_interval()) or (self.pl_ok_ts == 0)
                if need:
                    if self._refresh():
                        last_refresh = time.time()
                self._download_batch()
                self.prune()
                if not self.alive():
                    self.stop("播放器已停止请求")
                    break
                time.sleep(0.25)
        except Exception as e:
            log(f"[{self.idx}]{self.name} 后台异常：{e}")
            self.stop("异常退出")


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

    def _send(self, body, ctype, cache=False):
        if isinstance(body, str):
            body = body.encode()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        if cache:
            self.send_header("Cache-Control", "public, max-age=60")
        else:
            # 清单绝对不能缓存：否则播放器会拿着空清单一直转圈
            self.send_header("Cache-Control", "no-cache, no-store, must-revalidate")
            self.send_header("Pragma", "no-cache")
            self.send_header("Expires", "0")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = self.path.split("?")[0]
        # 总播放列表
        if path in ("/", "/playlist.m3u", "/playlist.m3u8"):
            lines = ["#EXTM3U"]
            host = self.headers.get("Host", "127.0.0.1")
            for idx, ch in CHANS.items():
                g = f' group-title="{ch.group}"' if ch.group else ""
                lg = f' tvg-logo="{ch.logo}"' if ch.logo else ""
                lines.append(f"#EXTINF:-1{lg}{g},{ch.name}")
                lines.append(f"http://{host}/ch/{idx}/live.m3u8")
            return self._send("\n".join(lines) + "\n",
                              "application/vnd.apple.mpegurl")
        # 单频道 m3u8 —— 只有这里被请求，才算「有人在看这个台」
        m = re.match(r"^/ch/(\d+)/live\.m3u8$", path)
        if m:
            ch = get_relay(int(m.group(1)))
            if not ch:
                return self.send_error(404)
            if ch.ready_count() < FIRST_MIN_SEGS:
                ch.wait_first(FIRST_WAIT)   # 等首批分片，别回空清单让播放器转圈
            return self._send(ch.build_m3u8(), "application/vnd.apple.mpegurl")
        # 切片
        m = re.match(r"^/ch/(\d+)/seg/(\d+)\.ts$", path)
        if m:
            idx, seq = int(m.group(1)), int(m.group(2))
            ch = get_relay(idx, seq)
            if not ch:
                return self.send_error(404)
            p = os.path.join(ch.seg_dir, f"{seq}.ts")
            if not os.path.exists(p):
                # 刚下的分片可能还在路上，短等一会儿再回，别直接 404
                with ch.lock:
                    known = seq in ch.segs
                if known:
                    for _ in range(20):
                        if os.path.exists(p):
                            break
                        time.sleep(0.15)
            if os.path.exists(p):
                with open(p, "rb") as f:
                    data = f.read()
                return self._send(data, "video/mp2t", cache=True)
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
                            f"| 可播={c.ready_count()} | 失败={c.fail} "
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


def detect_lan_ip():
    """探测本机局域网 IP，写进播放列表，电视/手机也能直接用。"""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("223.5.5.5", 80))
        return s.getsockname()[0]
    except Exception:
        return "127.0.0.1"
    finally:
        try:
            s.close()
        except Exception:
            pass


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
    ap.add_argument("-w", "--window", type=int, default=WINDOW, help="磁盘保留切片数")
    ap.add_argument("-r", "--reload", type=int, default=30,
                    help="每隔多少分钟重新拉取远程列表，0=只拉一次")
    a = sanitize_args(ap)
    IDLE_SEC = a.idle
    SEG_ROOT = a.segdir
    WINDOW = max(6, a.window)
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

    lan = detect_lan_ip()
    write_local_playlist(a.out, port, lan)
    threading.Thread(target=janitor_loop, daemon=True).start()
    log(f"本地播放列表已写出 → {a.out}")
    log(f"本机播放 → http://127.0.0.1:{port}/playlist.m3u")
    log(f"局域网播放 → http://{lan}:{port}/playlist.m3u")
    log(f"状态查看 → http://127.0.0.1:{port}/status")
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


def write_local_playlist(path, port, host="127.0.0.1"):
    with open(path, "w", encoding="utf-8") as f:
        f.write("#EXTM3U\n")
        for i, c in CHANS.items():
            g = f' group-title="{c.group}"' if c.group else ""
            lg = f' tvg-logo="{c.logo}"' if c.logo else ""
            f.write(f"#EXTINF:-1{lg}{g},{c.name}\n")
            f.write(f"http://{host}:{port}/ch/{i}/live.m3u8\n")


def reload_loop(src, ua, minutes, flt, out, port):
    """定时重拉远程列表：更新地址、收录新频道，正在播的不动。"""
    lan = detect_lan_ip()
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
                        new_entry = ChannelRelay._to_entry(url)
                        if ch.entry != new_entry:
                            ch.entry = new_entry
                            updated += 1
            write_local_playlist(out, port, lan)
            log(f"列表已刷新：新增 {added}，更新 {updated}，总计 {len(CHANS)}")
        except Exception as e:
            log(f"列表重拉失败：{e}")


if __name__ == "__main__":
    main()
