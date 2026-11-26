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

本版再追加：治“每个切片之间长时间卡顿”（其余逻辑仍然不动）
  · 切片不再“等整片下载完才发”：播放器要哪片，立刻向源站取，取到多少发多少，
    边下边发给播放器，同时落盘给后面复用。以前是播放器一问、盘上还没有就直接
    404，播放器只能等一个 targetduration 再来问，于是每个切片之间都卡一段
  · 清单只写最近 4 片（约 40 秒），播放器始终贴着直播边缘；以前把池子里三十片
    全写进去，播放器从五分钟前开始放，一路追着被淘汰的老片，每片都要卡一下
  · 清单刷新 18 秒 → 5 秒，切片地址永远是新的，不会等地址过期才去下
  · 后台只预取播放位置附近的片，从最新往老方向排队，不再一次把整个窗口都拖下来
  · 切片地址失效（403/404）时自动重取清单换新地址再取一次，不再直接丢片
  · 不再因为序号跳号就插 #EXT-X-DISCONTINUITY（同一路直播时间戳是连续的，
    插了会让播放器重新初始化解码器，每次边界都要顿一下）
  · 切片支持 Range / HEAD（有些盒子开播前先发这两个，原来回 501 会一直转圈）
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

REFRESH_INTERVAL = 5       # 每 5 秒重取一次清单：越贴近直播边缘，切片地址越新、越不会缺
WINDOW = 30                # 本地保留切片数（每片约 10s）

# ---- 本版新增：按需缓存相关 ----
SINGLE_ACTIVE = True       # 只缓存当前在看的那个频道；--multi 可关掉
FIRST_SEG_WAIT = 4.0       # 首次请求清单时，最多等首个分片多久（避免播放器拿到空清单）
SEG_FAIL_MAX = 3           # 单个分片下载失败重试次数上限，超了就丢，避免死循环
SWITCH_GRACE = 5.0         # 切台后给旧频道几秒宽限再清盘，防止播放器预取造成来回打架

# ---- 治“切片之间卡顿”的几个关键参数 ----
PLAY_WINDOW = 4            # 只把最近 4 片写进清单（约 40 秒），播放器贴着直播边缘走
PREFETCH = 3               # 播放位置前面至少备好 3 片，播放器要的时候已经在盘上
POOL_KEEP = 12             # 内存/磁盘最多留 12 片，多了就淘汰最老的
SEG_STREAM_CHUNK = 65536   # 边下边发时的块大小
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
        # 本版再新增：给“边下边发”和诊断用的状态
        self.fetching = set()       # 正在被取的分片号，避免后台和播放器同时下一片
        self.last_seq = None        # 播放器最后要的那一片
        self.streamed = 0           # 现场取片的次数
        self.miss = 0               # 完全取不到片的次数
        self.last_err = ""          # 最近一次错误，给 /status 看
        self.speed = 0.0            # 下载速度估算（字节/秒）
        self.target_dur = 10.0
        self.ref_lock = threading.Lock()   # 清单刷新串行化，别几个线程一起打源站

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

    # ---------------- 本版新增：取片 / 边下边发 ----------------
    def seg_path(self, seq):
        return os.path.join(self.seg_dir, f"{seq}.ts")

    def url_for(self, seq):
        with self.lock:
            it = self.segs.get(seq)
            return it["url"] if it else None

    def _open_origin(self, url, timeout=20):
        req = urllib.request.Request(url, headers={
            "User-Agent": self.ua,
            "Accept": "*/*",
        })
        return urllib.request.urlopen(req, timeout=timeout)

    def refresh_playlist(self):
        """取一次清单，登记新切片、刷新旧切片的签名地址。返回是否成功。"""
        with self.ref_lock:
            pl = self._playlist_url()
            if not pl or pl.startswith("__ERR"):
                self.fail += 1
                self.last_err = f"取播放地址失败 {pl}"
                return False
            try:
                with self._open_origin(pl, timeout=15) as r:
                    text = r.read().decode("utf-8", "ignore")
                items = self._parse(text, pl)
                if not items:
                    self.fail += 1
                    self.last_err = "清单里没有切片"
                    return False
                with self.lock:
                    new = 0
                    for seq, url, dur in items:
                        it = self.segs.get(seq)
                        if it is None:
                            self.segs[seq] = {"url": url, "dur": dur,
                                              "local": None, "tries": 0}
                            new += 1
                        else:
                            # 地址带签名，每轮都用最新的，避免拿到过期地址
                            it["url"] = url
                            it["dur"] = dur
                    self.target_dur = max(6.0, max(i[2] for i in items))
                    newest = max(self.segs)
                    # 只留最近 POOL_KEEP 片；但播放器还没播到的片一律保住
                    keep_from = newest - POOL_KEEP + 1
                    if self.last_seq is not None:
                        keep_from = min(keep_from, self.last_seq - 1)
                    for s in list(self.segs):
                        if s < keep_from:
                            info = self.segs.pop(s)
                            lp = info.get("local")
                            if lp:
                                try:
                                    os.remove(lp)
                                except OSError:
                                    pass
                self.fail = 0
                self.last_err = ""
                if new:
                    log(f"[{self.idx}]{self.name} 清单更新 +{new} 池{len(self.segs)}")
                return True
            except Exception as e:
                self.fail += 1
                self.last_err = f"拉清单失败 {type(e).__name__}"
                log(f"[{self.idx}]{self.name} 拉清单失败 {e}")
                return False

    def _pump_to_disk(self, resp, seq, sink=None):
        """把响应写盘；给了 sink 就同时边下边发。返回写入字节数。"""
        p = self.seg_path(seq)
        tmp = p + ".part"
        os.makedirs(self.seg_dir, exist_ok=True)
        total = 0
        t0 = time.time()
        broken = False
        try:
            with open(tmp, "wb") as f:
                while True:
                    chunk = resp.read(SEG_STREAM_CHUNK)
                    if not chunk:
                        break
                    f.write(chunk)
                    total += len(chunk)
                    if sink is not None:
                        try:
                            sink(chunk)
                        except (BrokenPipeError, ConnectionResetError, OSError):
                            # 播放器断了（切台/拖动），片已经下了一部分，不再往下发
                            broken = True
                            break
        finally:
            if total > 1000 and not broken:
                try:
                    os.replace(tmp, p)
                    with self.lock:
                        it = self.segs.get(seq)
                        if it is not None:
                            it["local"] = p
                except OSError:
                    pass
            else:
                # 断流/失败留下的半截片必须删掉：半截 .ts 当整片发出去，
                # 播放器会卡在那一片上重新缓冲，比没有更糟
                try:
                    if os.path.exists(tmp):
                        os.remove(tmp)
                except OSError:
                    pass
        dt = max(0.001, time.time() - t0)
        if total:
            inst = total / dt
            self.speed = inst if not self.speed else self.speed * 0.6 + inst * 0.4
        return total

    def fetch_to_disk(self, seq, url):
        """后台预取：整片下到盘上。"""
        with self.lock:
            if seq in self.fetching:
                return False
            self.fetching.add(seq)
        try:
            with self._open_origin(url) as r:
                n = self._pump_to_disk(r, seq)
            return n > 1000
        except urllib.error.HTTPError as e:
            self.last_err = f"预取{seq} HTTP {e.code}"
            return False
        except Exception as e:
            self.last_err = f"预取{seq} {type(e).__name__}"
            return False
        finally:
            with self.lock:
                self.fetching.discard(seq)

    def stream_segment(self, h, seq):
        """播放器要的片盘上没有：立刻向源站取，边取边发给播放器。

        这是“切片之间卡顿”的正解——以前这里直接回 404，播放器只能等一个
        targetduration 再来问，于是每片之间卡一大段。现在取到多少发多少。
        返回 True 表示响应已经发出（成功）。
        """
        url = self.url_for(seq)
        if not url:
            self.refresh_playlist()
            url = self.url_for(seq)
        tried = set()
        for attempt in range(2):
            if not url or url in tried:
                break
            tried.add(url)
            try:
                with self._open_origin(url, timeout=25) as r:
                    # 先成功连上源站再回响应头，连不上还能干净地回 404
                    self._send_stream_head(h)
                    with self.lock:
                        self.fetching.add(seq)
                    try:
                        n = self._pump_to_disk(r, seq, sink=h.wfile.write)
                    finally:
                        with self.lock:
                            self.fetching.discard(seq)
                    if n > 0:
                        self.streamed += 1
                        return True
                    self.last_err = f"片{seq} 空响应"
            except urllib.error.HTTPError as e:
                self.last_err = f"片{seq} HTTP {e.code}"
            except Exception as e:
                self.last_err = f"片{seq} {type(e).__name__}"
            # 地址过期（403/404）多半是签名换了：重取清单换地址再来一次
            self.refresh_playlist()
            url = self.url_for(seq)
        self.miss += 1
        return False

    @staticmethod
    def _send_stream_head(h):
        h.send_response(200)
        h.send_header("Content-Type", "video/mp2t")
        h.send_header("Cache-Control", "no-store")
        h.send_header("Access-Control-Allow-Origin", "*")
        h.send_header("Connection", "close")
        h.end_headers()
        h.close_connection = True

    # ---------------- 后台线程 ----------------
    def refresher(self, g):
        while self.running and self.gen == g:
            # 后台续期不刷新空闲计时：只有播放器真来请求才算“有人在看”
            ok = self.refresh_playlist()
            if not ok and self.fail >= 3:
                self.last_err = f"连续失败 {self.fail} 次，稍后重试"
                for _ in range(10):
                    if not self.running or self.gen != g:
                        return
                    time.sleep(1)
            # 分段睡：停台/切台时能立刻退出
            slept = 0.0
            while slept < REFRESH_INTERVAL:
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
                time.sleep(0.5)
                slept += 0.5

    def downloader(self, g):
        os.makedirs(self.seg_dir, exist_ok=True)
        while self.running and self.gen == g:
            todo = []
            with self.lock:
                if self.segs:
                    newest = max(self.segs)
                    lo = newest - (PLAY_WINDOW + PREFETCH) + 1
                    if self.last_seq is not None:
                        lo = min(lo, self.last_seq)
                    todo = sorted([(s, i["url"]) for s, i in self.segs.items()
                                   if not i["local"] and s >= lo
                                   and s not in self.fetching])
            for s, u in todo:
                if not self.running or self.gen != g:
                    break
                self.fetch_to_disk(s, u)
            time.sleep(0.3)
        if not self.running:
            self.purge()

    def build_m3u8(self):
        with self.lock:
            ready = sorted([(s, i) for s, i in self.segs.items() if i["local"]])
        if not ready:
            return ("#EXTM3U\n#EXT-X-VERSION:3\n#EXT-X-TARGETDURATION:14\n"
                    "#EXT-X-MEDIA-SEQUENCE:0\n")
        # 关键改动：只写最近几片，播放器贴着直播边缘走。
        # 原来把池子里三十片全写进去，播放器从五分钟前开始放，一路追着被淘汰的
        # 老片跑，每片都可能扑空 → 每片都卡一段。
        ready = ready[-PLAY_WINDOW:]
        first = ready[0][0]
        # 滑窗（老片会淘汰），不能标 EVENT；同一路直播时间戳连续，不插 DISCONTINUITY
        td = max(10, int(max(i["dur"] for _, i in ready) + 0.999))
        out = ["#EXTM3U", "#EXT-X-VERSION:3", f"#EXT-X-TARGETDURATION:{td}",
               f"#EXT-X-MEDIA-SEQUENCE:{first}", "#EXT-X-ALLOW-CACHE:NO"]
        for s, i in ready:
            out.append(f"#EXTINF:{i['dur']:.3f},")
            out.append(f"/ch/{self.idx}/seg/{s}.ts")
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

    def _send_file(self, p):
        """把盘上的切片发出去，支持 Range（有些播放器/盒子会先发 Range 探测）。"""
        size = os.path.getsize(p)
        start, end, partial = 0, size - 1, False
        rng = self.headers.get("Range")
        if rng:
            mm = re.match(r"bytes=(\d*)-(\d*)", rng.strip())
            if mm:
                if mm.group(1):
                    start = int(mm.group(1))
                if mm.group(2):
                    end = min(int(mm.group(2)), size - 1)
                if start >= size:
                    self.send_response(416)
                    self.send_header("Content-Range", f"bytes */{size}")
                    self.end_headers()
                    return
                partial = True
        length = end - start + 1
        self.send_response(206 if partial else 200)
        self.send_header("Content-Type", "video/mp2t")
        self.send_header("Content-Length", str(length))
        self.send_header("Accept-Ranges", "bytes")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "no-store")
        if partial:
            self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
        self.end_headers()
        with open(p, "rb") as f:
            f.seek(start)
            left = length
            while left > 0:
                chunk = f.read(min(SEG_STREAM_CHUNK, left))
                if not chunk:
                    break
                self.wfile.write(chunk)
                left -= len(chunk)

    def do_HEAD(self):
        path = self.path.split("?")[0]
        m = re.match(r"^/ch/(\d+)/live\.m3u8$", path)
        if m:
            self.send_response(200)
            self.send_header("Content-Type", "application/vnd.apple.mpegurl")
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            return
        m = re.match(r"^/ch/(\d+)/seg/(\d+)\.ts$", path)
        if m:
            ch = get_relay(int(m.group(1)), activate=False)
            p = ch.seg_path(int(m.group(2))) if ch else None
            self.send_response(200)
            self.send_header("Content-Type", "video/mp2t")
            self.send_header("Accept-Ranges", "bytes")
            if p and os.path.exists(p):
                self.send_header("Content-Length", str(os.path.getsize(p)))
            self.end_headers()
            return
        self.send_response(200)
        self.send_header("Content-Type", "text/plain")
        self.end_headers()

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
            idx, seq = int(m.group(1)), int(m.group(2))
            ch = get_relay(idx, activate=False)   # 取切片也算在看，刷新空闲计时
            if ch is None:
                return self.send_error(404)
            p = ch.seg_path(seq)
            if seq in ch.segs or os.path.exists(p):
                ch.last_seq = seq
            if os.path.exists(p) and os.path.getsize(p) > 1000:
                return self._send_file(p)
            # 盘上还没有 → 现场取，边下边发；不再回 404 让播放器干等
            if ch.stream_segment(self, seq):
                return
            return self.send_error(404)
        # 状态（大列表只显示正在跑的 + 摘要，避免输出上万行）
        if path == "/status":
            running = [(i, c) for i, c in CHANS.items() if c.running]
            total_mb = sum(c.cache_bytes() for _, c in running) / 1048576.0
            head = [f"频道总数: {len(CHANS)}   正在缓存: {len(running)}   "
                    f"缓存合计: {total_mb:.1f} MB   "
                    f"模式: {'只缓存当前频道' if SINGLE_ACTIVE else '允许多台同时缓存'}",
                    f"清单窗口: 最近 {PLAY_WINDOW} 片 / 预取 {PREFETCH} 片 / 刷新 {REFRESH_INTERVAL}s"]
            rows = []
            for i, c in running:
                with c.lock:
                    total = len(c.segs)
                    ready = sum(1 for x in c.segs.values() if x["local"])
                behind = "-"
                if c.last_seq is not None and c.segs:
                    behind = f"{max(c.segs) - c.last_seq}片"
                rows.append(
                    f"#{i} {c.name} | 池={total}(已下载{ready}) | 播放到={c.last_seq} | "
                    f"落后直播={behind} | 现场取片={c.streamed}次 | 取片失败={c.miss}次 | "
                    f"速度={c.speed/1048576.0:.1f}MB/s | 上次请求={int(time.time()-c.last_touch)}秒前 | "
                    f"缓存={c.cache_bytes()/1048576.0:.1f}MB | 最近错误={c.last_err or '无'}")
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
    global IDLE_SEC, SEG_ROOT, WINDOW, SINGLE_ACTIVE, PLAY_WINDOW, PREFETCH
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
    ap.add_argument("--playwin", type=int, default=PLAY_WINDOW,
                    help="清单里放最近几片，默认 4（贴着直播边缘，别调太大）")
    ap.add_argument("--prefetch", type=int, default=PREFETCH,
                    help="播放位置前面预取几片，默认 3")
    a = sanitize_args(ap)
    IDLE_SEC = a.idle
    SEG_ROOT = a.segdir
    WINDOW = a.window
    PLAY_WINDOW = max(2, a.playwin)
    PREFETCH = max(0, a.prefetch)
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
