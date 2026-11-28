#!/usr/bin/env python3
"""
IPTV m3u 播放列表批量中转器（原版 + 代理 / 相对路径修正）
================================
在「原版 + 多设备同时缓存」这一版上继续改，清单格式、窗口、EVENT、TARGETDURATION
一个字没动。这一版只解决两件事：

  1. 需要走代理的源，一直卡在第一个切片
  2. 入口 302 跳到别的服务器时，切片地址被拼错到入口域名上 → 全部 403

为什么之前会卡在第一个切片
--------------------------
源站（line.mag7070.eu 这类）返回的清单是相对路径：

    /hls/<hash>/855743_3003.ts

按规范，这个相对路径要拼在「真正返回清单的那个地址」上，也就是 302 之后的
http://67.159.12.58:80/live/play/.../855743。之前脚本用的是入口地址
（line.mag7070.eu）作基址，拼出来变成：

    http://line.mag7070.eu:80/hls/<hash>/855743_3003.ts   → 403 Forbidden

每一片都 403，重试 5 次后丢掉，本地一直没有切片，清单永远是空的，播放器就
一直停在第一个切片缓冲。走代理时更容易踩到：有些 HTTP 代理会把 302 自己跟掉，
客户端拿不到 Location，基址只能是入口域名。

本版怎么修的
------------
  · 用「实际响应的最终地址」r.geturl() 作基址，不再用入口地址
  · 清单每片同时记住原始相对路径，403/404 时用真实基址重新拼一次再试
  · 拿不到 302 时，直连探一次入口，把真实服务器地址补回来（只要入口域名能连）
  · 显式代理：--proxy http://127.0.0.1:7890，入口/清单/切片全部走同一个代理，
    裸 IP 也走（不依赖 PAC/规则，代理只认域名的分流不会漏掉切片）
  · 切片下载并发 2 路（--jobs 可调），慢代理下追得上源站出片速度
  · 403/404 自动重取清单换新地址，不直接把片丢掉
  · /diag/<频道号> 能看到卡在哪一步：代理、基址、每片状态、最近错误

用法
----
    python3 iptv_relay_原版_多设备_代理修正.py 你的列表.m3u -p 8080
    python3 iptv_relay_原版_多设备_代理修正.py 你的列表.m3u -p 8080 --proxy http://127.0.0.1:7890
    python3 iptv_relay_原版_多设备_代理修正.py 你的列表.m3u -p 8080 --no-proxy

-w / --single / --max-channels / -i 全部沿用上一版，默认多台设备同时缓存。
"""

import argparse
import concurrent.futures
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

# ---- 按需缓存相关（沿用上一版）----
SINGLE_ACTIVE = False
SWITCH_GRACE = 5.0
MAX_CHANNELS = 0
IDLE_GRACE = 15.0
FIRST_SEG_WAIT = 8.0       # 首次请求清单时最多等首片多久（原来 2 秒，慢代理下太短）
SEG_FAIL_MAX = 5           # 单个切片失败上限

# ---- 本版新增：网络层 ----
PROXY = ""                 # 显式代理，空=按环境变量/系统设置
PROXY_USER = ""
JOBS = 2                   # 每个频道同时下载几个切片
_open_lock = threading.Lock()
_OPENER = None             # 跟随重定向
_OPENER_NR = None          # 不跟随重定向（用来读 302 的 Location）
_OPENER_DIRECT = None      # 强制直连（不读环境代理）
_OPENER_DIRECT_NR = None   # 强制直连 + 不跟随重定向

SEG_ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "segs")

DEFAULT_PLAYLIST = (
    "https://ghfast.top/https://raw.githubusercontent.com/SuperNinjap/iptv/main/USA.m3u"
)
CACHE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".playlist_cache.m3u")


def log(*a):
    print(time.strftime("[%H:%M:%S]"), *a, flush=True)


# ---------------------------------------------------------------- 网络层
def _build_opener(proxy, follow=True, auth=""):
    handlers = []
    if proxy:
        # 显式给 http/https 都指到同一个代理：裸 IP 的切片也不会漏过去
        handlers.append(urllib.request.ProxyHandler({"http": proxy, "https": proxy}))
        if auth and ":" in auth:
            user, pw = auth.split(":", 1)
            pm = urllib.request.HTTPPasswordMgrWithDefaultRealm()
            pm.add_password(None, proxy, user, pw)
            handlers.append(urllib.request.ProxyBasicAuthHandler(pm))
    elif proxy is None:
        # None 表示读环境变量/系统设置（Windows 会读 IE 代理）
        handlers.append(urllib.request.ProxyHandler())
    else:
        # 空字符串 = 强制直连
        handlers.append(urllib.request.ProxyHandler({}))
    if not follow:
        class _NoRedirect(urllib.request.HTTPRedirectHandler):
            def redirect_request(self, req, fp, code, msg, headers, newurl):
                return None
        handlers.append(_NoRedirect())
    return urllib.request.build_opener(*handlers)


def init_net(proxy_arg="", no_proxy=False, auth=""):
    global PROXY, PROXY_USER, _OPENER, _OPENER_NR, _OPENER_DIRECT, _OPENER_DIRECT_NR
    if no_proxy:
        PROXY = ""
    elif proxy_arg:
        PROXY = proxy_arg if "://" in proxy_arg else "http://" + proxy_arg
    else:
        PROXY = (os.environ.get("HTTP_PROXY") or os.environ.get("http_proxy")
                 or os.environ.get("ALL_PROXY") or os.environ.get("all_proxy") or None)
    PROXY_USER = auth
    _OPENER = _build_opener(PROXY, True, auth)
    _OPENER_NR = _build_opener(PROXY, False, auth)
    # 直连用的 opener 明确不带代理，专给「探真实服务器地址」用
    _OPENER_DIRECT = _build_opener("", True)
    _OPENER_DIRECT_NR = _build_opener("", False)
    if PROXY:
        log(f"网络：走代理 {PROXY}" + ("（带认证）" if auth else "") +
            "；入口、清单、切片全部经它转发")
    elif no_proxy:
        log("网络：强制直连（--no-proxy）")
    else:
        auto = urllib.request.getproxies()
        log(f"网络：按系统/环境设置 {auto if auto else '直连'}")


def _open(req, timeout=20, follow=True, direct=False):
    if direct:
        op = _OPENER_DIRECT if follow else _OPENER_DIRECT_NR
    else:
        op = _OPENER if follow else _OPENER_NR
    return op.open(req, timeout=timeout)


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
            with _open(req, timeout=timeout) as r:
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
        # ---- 启停/清盘（沿用上一版）----
        self.gen = 0
        self.start_lock = threading.Lock()
        self.stop_at = 0.0
        # ---- 本版新增：基址 / 刷新 / 诊断 ----
        self.good_base = ""        # 302 之后探测到的真实基址
        self.list_base = ""        # 实际返回清单的地址（可能是入口）
        self.base_lock = threading.Lock()
        self.need_refresh = threading.Event()
        self.last_err = ""
        self.dl_speed = 0.0        # 最近一片的下载速度 KB/s
        self.base_try_at = 0.0     # 上次探测真实基址的时间（失败后冷却，别每片都探）
        self.hinted = False        # 只提示一次“这路可能得挂代理”

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
        if not SINGLE_ACTIVE:
            self.stop_at = 0.0

    # ---------------- 启停与清盘 ----------------
    def start(self):
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
        self.running = False
        self.gen += 1
        self.stop_at = 0.0
        with self.lock:
            self.segs.clear()
        if purge:
            self.purge()
        log(f"[{self.idx}]{self.name} 已停止缓存" + ("，缓存目录已删除" if purge else ""))

    def purge(self):
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

    def wait_first(self, timeout=None):
        end = time.time() + (FIRST_SEG_WAIT if timeout is None else timeout)
        while time.time() < end:
            if self.has_ready():
                return True
            if not self.running:
                break
            time.sleep(0.2)
        return self.has_ready()

    # 取新 token 得到 m3u8 地址；返回 "" 表示源站直接 200 给清单，没有 302
    def _playlist_url(self):
        req = urllib.request.Request(self.entry, headers={"User-Agent": self.ua})
        try:
            with _open(req, timeout=20, follow=False) as r:
                loc = r.headers.get("Location")
                return urljoin(self.entry, loc) if loc else ""
        except urllib.error.HTTPError as e:
            loc = e.headers.get("Location") if e.headers else None
            if loc:
                return urljoin(self.entry, loc)
            if e.code in (301, 302, 303, 307, 308):
                return f"__ERR_{e.code}"
            # 4xx/5xx：当成“没有 302”，让后面的请求去暴露真实错误
            return ""
        except Exception as e:
            self.last_err = f"取地址失败 {type(e).__name__}"
            return f"__ERR_{type(e).__name__}"

    def _parse(self, text, base):
        """返回 [(seq, url, dur, raw_line), ...]；raw 留着，基址错了能重拼。"""
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
                out.append((int(mm.group(1)) if mm else bseq + i, url, dur, line))
                i += 1
        return out

    def _real_base(self):
        """入口 302 被代理吃掉时，直连探一次真实服务器地址；拿不到就返回空。"""
        with self.base_lock:
            if self.good_base:
                return self.good_base
            if not self.list_base:
                return ""
            # 探测失败后 60 秒内不再试：用户直连不通时就别每片都干等 20 秒
            if time.time() - self.base_try_at < 60:
                return ""
            self.base_try_at = time.time()
            req = urllib.request.Request(self.entry, headers={"User-Agent": self.ua})
            # 先直连（入口域名一般能小请求连通，只有大流量被卡）
            for direct in (True, False):
                try:
                    with _open(req, timeout=10, follow=False, direct=direct) as r:
                        loc = r.headers.get("Location")
                    if loc:
                        self.good_base = urljoin(self.entry, loc)
                        log(f"[{self.idx}]{self.name} 探测到真实服务器：{self.good_base}")
                        return self.good_base
                except urllib.error.HTTPError as e:
                    loc = e.headers.get("Location") if e.headers else None
                    if loc:
                        self.good_base = urljoin(self.entry, loc)
                        log(f"[{self.idx}]{self.name} 探测到真实服务器：{self.good_base}")
                        return self.good_base
                    self.last_err = f"探测失败 HTTP {e.code}"
                except Exception as e:
                    self.last_err = f"探测失败 {type(e).__name__}"
            return ""

    def _candidate_urls(self, info):
        """同一片的候选地址：真实基址拼出来的优先，再退回它自带的地址。"""
        urls = []
        raw = info.get("raw") or ""
        if raw and not raw.startswith("http"):
            rb = self._real_base()
            if rb:
                cand = urljoin(rb, raw)
                if cand not in urls:
                    urls.append(cand)
        u = info.get("url")
        if u and u not in urls:
            urls.append(u)
        return urls

    def refresher(self, g):
        last_fetch = 0.0
        while self.running and self.gen == g:
            # 失败触发的重拉至少间隔 3 秒，别对源站打请求风暴
            wait = last_fetch + 3.0 - time.time()
            if wait > 0:
                time.sleep(wait)
            last_fetch = time.time()
            pl = self._playlist_url()
            target = self.entry if not pl or pl.startswith("__ERR") else pl
            if pl.startswith("__ERR"):
                self.fail += 1
                self.last_err = f"取地址失败 {pl}"
                log(f"[{self.idx}]{self.name} 取token失败 {pl}")
                if self.fail >= 3:
                    log(f"[{self.idx}]{self.name} 连续失败，暂停 30s")
                    for _ in range(30):
                        if not self.running or self.gen != g:
                            return
                        time.sleep(1)
            else:
                try:
                    req = urllib.request.Request(target, headers={"User-Agent": self.ua})
                    with _open(req, timeout=20) as r:
                        text = r.read().decode("utf-8", "ignore")
                        # ★ 关键修正：基址用“实际返回清单的地址”，不是入口地址
                        final = r.geturl() or target
                    self.list_base = final
                    items = self._parse(text, final)
                    with self.lock:
                        new = 0
                        for seq, url, dur, raw in items:
                            if seq not in self.segs:
                                self.segs[seq] = {"url": url, "raw": raw, "dur": dur,
                                                  "local": None, "tries": 0}
                                new += 1
                        while len(self.segs) > WINDOW + 5:
                            old_seq, info = self.segs.popitem(last=False)
                            lp = info.get("local")
                            if lp and os.path.exists(lp):
                                try:
                                    os.remove(lp)
                                except OSError:
                                    pass
                    self.fail = 0
                    self.last_err = ""
                    log(f"[{self.idx}]{self.name} 续期OK 新增{new} 池{len(self.segs)}")
                except Exception as e:
                    self.fail += 1
                    self.last_err = f"拉清单失败 {type(e).__name__} {e}"
                    log(f"[{self.idx}]{self.name} 拉列表失败 {e}")

            # 空闲回收（沿用上一版）
            if time.time() - self.last_touch > IDLE_SEC:
                log(f"[{self.idx}]{self.name} 停看超过 {IDLE_SEC} 秒，停止缓存并删除切片目录")
                self.stop()
                return

            for _ in range(int(REFRESH_INTERVAL)):
                if not self.running or self.gen != g:
                    return
                if self.stop_at and time.time() >= self.stop_at:
                    log(f"[{self.idx}]{self.name} 已切到其它频道，停止缓存并删除切片目录")
                    self.stop()
                    return
                if time.time() - self.last_touch > IDLE_SEC:
                    log(f"[{self.idx}]{self.name} 停看超过 {IDLE_SEC} 秒，停止缓存并删除切片目录")
                    self.stop()
                    return
                if self.need_refresh.is_set():
                    self.need_refresh.clear()
                    break
                time.sleep(1)

    def _fetch_seg(self, g, s, info):
        """下一片。返回 True 表示已落盘。403/404 会换基址重试并请求刷新清单。"""
        if not self.running or self.gen != g:
            return False
        p = os.path.join(self.seg_dir, f"{s}.ts")
        tmp = p + ".part"
        urls = self._candidate_urls(info)
        for k, u in enumerate(urls):
            if not self.running or self.gen != g:
                return False
            t0 = time.time()
            got = 0
            try:
                req = urllib.request.Request(u, headers={
                    "User-Agent": self.ua, "Accept": "*/*",
                })
                with _open(req, timeout=30) as r, open(tmp, "wb") as f:
                    while True:
                        b = r.read(65536)
                        if not b:
                            break
                        f.write(b)
                        got += len(b)
                if got > 1000:
                    os.replace(tmp, p)
                    with self.lock:
                        if s in self.segs:
                            self.segs[s]["local"] = p
                            self.segs[s]["tries"] = 0
                    used = max(0.01, time.time() - t0)
                    self.dl_speed = got / 1024.0 / used
                    return True
                self.last_err = f"第{s}片内容太短 {got}B"
            except urllib.error.HTTPError as e:
                self.last_err = f"第{s}片 HTTP {e.code}"
                try:
                    if os.path.exists(tmp):
                        os.remove(tmp)
                except OSError:
                    pass
                # 403/404：地址可能过期，或基址拼错 → 换候选重试 + 请刷新清单
                if e.code in (403, 404, 410):
                    continue
                break
            except Exception as e:
                self.last_err = f"第{s}片 {type(e).__name__} {e}"
                try:
                    if os.path.exists(tmp):
                        os.remove(tmp)
                except OSError:
                    pass
                continue
        self.need_refresh.set()
        return False

    def downloader(self, g):
        os.makedirs(self.seg_dir, exist_ok=True)
        pool = concurrent.futures.ThreadPoolExecutor(
            max_workers=max(1, JOBS), thread_name_prefix=f"dl{self.idx}")
        try:
            while self.running and self.gen == g:
                todo = []
                with self.lock:
                    for s, i in self.segs.items():
                        if i["local"] is None and i.get("tries", 0) < SEG_FAIL_MAX:
                            todo.append((s, dict(i)))
                if todo:
                    futs = [pool.submit(self._fetch_seg, g, s, i) for s, i in todo]
                    for (s, _i), fu in zip(todo, futs):
                        ok = False
                        try:
                            ok = fu.result()
                        except Exception as e:
                            self.last_err = f"第{s}片线程异常 {type(e).__name__}"
                        if not ok:
                            with self.lock:
                                it = self.segs.get(s)
                                if it is not None:
                                    it["tries"] = it.get("tries", 0) + 1
                            if not PROXY and not self.hinted and "403" not in (self.last_err or ""):
                                self.hinted = True
                                log(f"[{self.idx}]{self.name} 一直拿不到切片，"
                                    f"如果这路源本身要代理，加 --proxy http://127.0.0.1:端口 再试")
                    time.sleep(0.3)
                else:
                    time.sleep(1.0)
        finally:
            pool.shutdown(wait=False)
        if not self.running:
            self.purge()

    def build_m3u8(self):
        with self.lock:
            ready = sorted([(s, i) for s, i in self.segs.items() if i["local"]])
        if not ready:
            return ("#EXTM3U\n#EXT-X-VERSION:3\n#EXT-X-TARGETDURATION:14\n"
                    "#EXT-X-MEDIA-SEQUENCE:0\n#EXT-X-PLAYLIST-TYPE:EVENT\n")
        ready = ready[-WINDOW:]
        first = ready[0][0]
        out = ["#EXTM3U", "#EXT-X-VERSION:3", "#EXT-X-TARGETDURATION:14",
               f"#EXT-X-MEDIA-SEQUENCE:{first}", "#EXT-X-PLAYLIST-TYPE:EVENT"]
        prev = None
        for s, i in ready:
            if prev is not None and s != prev + 1:
                out.append("#EXT-X-DISCONTINUITY")
            out.append(f"#EXTINF:{i['dur']:.3f},")
            out.append(f"/ch/{self.idx}/seg/{s}.ts")
            prev = s
        return "\n".join(out) + "\n"

    def diag_text(self):
        with self.lock:
            items = list(self.segs.items())[-10:]
        lines = [
            f"频道 #{self.idx} {self.name}",
            f"入口: {self.entry}",
            f"清单地址: {self.list_base or '(还没拿到)'}",
            f"真实基址: {self.good_base or '(未跳转/还没探测)'}",
            f"代理: {PROXY or '直连/系统设置'}",
            f"运行: {'是' if self.running else '否'}  池: {len(self.segs)} 片  "
            f"磁盘: {self.cache_bytes()/1048576.0:.1f} MB",
            f"速度: {self.dl_speed:.0f} KB/s  最近错误: {self.last_err or '无'}",
            "",
            "最近 10 片:",
        ]
        for s, i in items:
            state = "已落盘" if i["local"] else "未落盘"
            lines.append(f"  {s}  {state}  失败{i.get('tries', 0)}次  {i.get('raw', '')[:70]}")
            lines.append(f"       实际地址: {i.get('url', '')[:110]}")
        return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- 管理
CHANS = {}
IDLE_SEC = 180
LOCK = threading.Lock()
TRIM_LOCK = threading.Lock()


def _mode_text():
    if SINGLE_ACTIVE:
        return "只缓存当前频道(--single)"
    if MAX_CHANNELS > 0:
        return f"多台设备同时缓存(上限{MAX_CHANNELS}个频道)"
    return "多台设备同时缓存(不限制频道数)"


def _stop_others(keep_idx):
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


def _trim_channels(keep_idx):
    if MAX_CHANNELS <= 0:
        return
    with TRIM_LOCK:
        with LOCK:
            running = [(i, c) for i, c in CHANS.items() if c.running and i != keep_idx]
        over = len(running) + 1 - MAX_CHANNELS
        if over <= 0:
            return
        idle = [(i, c) for i, c in running if time.time() - c.last_touch > IDLE_GRACE]
        if not idle:
            return
        idle.sort(key=lambda kv: kv[1].last_touch)
        for i, c in idle[:over]:
            log(f"同时缓存超过上限 {MAX_CHANNELS}，停掉没人看的 #{i}{c.name}")
            c.stop()


def get_relay(idx, activate=True):
    with LOCK:
        ch = CHANS.get(idx)
    if not ch:
        return None
    ch.touch()
    if activate:
        ch.stop_at = 0.0
        if SINGLE_ACTIVE:
            _stop_others(idx)
        ch.start()
        if not SINGLE_ACTIVE:
            _trim_channels(idx)
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
        if path in ("/", "/playlist.m3u", "/playlist.m3u8"):
            lines = ["#EXTM3U"]
            for idx, ch in CHANS.items():
                g = f' group-title="{ch.group}"' if ch.group else ""
                n = f' tvg-name="{ch.name}"' if ch.name else ""
                lines.append(f"#EXTINF:-1{n}{g},{ch.name}")
                lines.append(f"http://{self.headers.get('Host','127.0.0.1')}/ch/{idx}/live.m3u8")
            return self._send("\n".join(lines) + "\n", "application/vnd.apple.mpegurl")
        # 诊断页：卡在哪一步一眼看到
        m = re.match(r"^/diag/(\d+)$", path)
        if m:
            ch = get_relay(int(m.group(1)), activate=False)
            if not ch:
                return self.send_error(404)
            return self._send(ch.diag_text(), "text/plain; charset=utf-8",
                              {"Cache-Control": "no-store"})
        m = re.match(r"^/ch/(\d+)/live\.m3u8$", path)
        if m:
            ch = get_relay(int(m.group(1)))
            if not ch:
                return self.send_error(404)
            if not ch.has_ready():
                ch.wait_first()
            return self._send(ch.build_m3u8(), "application/vnd.apple.mpegurl",
                              {"Cache-Control": "no-store, no-cache, must-revalidate"})
        m = re.match(r"^/ch/(\d+)/seg/(\d+)\.ts$", path)
        if m:
            idx, seq = int(m.group(1)), m.group(2)
            ch = get_relay(idx, activate=True)
            if ch is None:
                return self.send_error(404)
            p = os.path.join(SEG_ROOT, str(idx), f"{seq}.ts")
            if os.path.exists(p):
                with open(p, "rb") as f:
                    data = f.read()
                return self._send(data, "video/mp2t")
            return self.send_error(404)
        if path == "/status":
            running = [(i, c) for i, c in CHANS.items() if c.running]
            total_mb = sum(c.cache_bytes() for _, c in running) / 1048576.0
            head = [f"频道总数: {len(CHANS)}   正在缓存: {len(running)}   "
                    f"缓存合计: {total_mb:.1f} MB   "
                    f"模式: {_mode_text()}   代理: {PROXY or '直连/系统设置'}"]
            rows = [f"#{i} {c.name} | 池={len(c.segs)} | 失败={c.fail} | "
                    f"上次请求={int(time.time()-c.last_touch)}秒前 | "
                    f"缓存={c.cache_bytes()/1048576.0:.1f}MB | "
                    f"速度={c.dl_speed:.0f}KB/s" + (f" | 错误={c.last_err}" if c.last_err else "")
                    for i, c in running]
            if not running:
                rows = [f"(当前没有频道在播放；播放器请求某个频道才会启动缓存，"
                        f"停看 {IDLE_SEC} 秒后自动删除缓存)"]
            return self._send("\n".join(head + [""] + rows), "text/plain; charset=utf-8")
        self.send_error(404)


def sanitize_args(ap):
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
    global IDLE_SEC, SEG_ROOT, WINDOW, SINGLE_ACTIVE, MAX_CHANNELS
    global FIRST_SEG_WAIT, JOBS
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("src", nargs="?", default=DEFAULT_PLAYLIST,
                    help="m3u 来源：本地路径 / http(s) 地址 / - (stdin)；不填用内置远程列表")
    ap.add_argument("-p", "--port", type=int, default=8080)
    ap.add_argument("-o", "--out",
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "local_playlist.m3u"),
                    help="生成的本地列表路径（默认脚本同目录，Android 上别用 /tmp）")
    ap.add_argument("-u", "--ua", default=MAG_UA)
    ap.add_argument("-i", "--idle", type=int, default=180,
                    help="每个频道停看多少秒后停缓存并删切片目录，默认 180")
    ap.add_argument("-f", "--filter", default="")
    ap.add_argument("-s", "--segdir", default=SEG_ROOT, help="切片缓存目录，注意留足空间")
    ap.add_argument("-w", "--window", type=int, default=WINDOW, help="保留切片数，每片约10秒")
    ap.add_argument("-r", "--reload", type=int, default=30,
                    help="每隔多少分钟重新拉取远程列表，0=只拉一次")
    ap.add_argument("--single", action="store_true",
                    help="只缓存当前在看的那个频道（默认关闭）")
    ap.add_argument("--max-channels", type=int, default=0,
                    help="同时缓存频道数上限，0=不限制（默认 0）")
    ap.add_argument("--proxy", default="",
                    help="http 代理，例 http://127.0.0.1:7890；入口/清单/切片全部走它")
    ap.add_argument("--proxy-user", default="", help="代理认证 user:pass（可选）")
    ap.add_argument("--no-proxy", action="store_true", help="强制直连，忽略环境/系统代理")
    ap.add_argument("--firstwait", type=float, default=FIRST_SEG_WAIT,
                    help="首次请求清单最多等首片多少秒，默认 8")
    ap.add_argument("--jobs", type=int, default=JOBS,
                    help="每个频道同时下载几片，默认 2；线路差可以调 1")
    a = sanitize_args(ap)
    IDLE_SEC = a.idle
    SEG_ROOT = a.segdir
    WINDOW = a.window
    SINGLE_ACTIVE = bool(a.single)
    MAX_CHANNELS = max(0, int(a.max_channels or 0))
    FIRST_SEG_WAIT = max(0.0, float(a.firstwait))
    JOBS = max(1, int(a.jobs))
    init_net(a.proxy, a.no_proxy, a.proxy_user)

    os.makedirs(SEG_ROOT, exist_ok=True)
    try:
        for n in os.listdir(SEG_ROOT):
            d = os.path.join(SEG_ROOT, n)
            if os.path.isdir(d):
                shutil.rmtree(d, ignore_errors=True)
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
    log(f"模式: {_mode_text()}；每个频道单独计时，停看 -i 秒后删它的缓存")

    socketserver.ThreadingTCPServer.allow_reuse_address = True
    httpd, port = bind_server(a.port, Handler)
    httpd.daemon_threads = True

    write_local_playlist(a.out, port)
    log(f"本地播放列表已写出 → {a.out}")
    log(f"服务地址 → http://127.0.0.1:{port}/playlist.m3u")
    log(f"状态查看 → http://127.0.0.1:{port}/status")
    log(f"卡住排查 → http://127.0.0.1:{port}/diag/频道号")
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
            c.running = False
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
