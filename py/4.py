#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
IPTV 直播中转（按需直取版）
================================
和上一版的根本区别：不预缓存、不攒分片、不落盘。

播放器要清单 → 现场去源站拉一份新的清单，把里面的分片地址改成本地地址
播放器要分片 → 现场按需去源站取那一片，取到什么给什么，取完即弃

所以：
  · 不存在「分片还没攒够 → 给个空清单 → 播放器一直转圈」这条路
  · 不存在「源站一秒的抖动就把整个台卡死」
  · 不占磁盘、不占内存，看哪个台才动哪个台，关掉就什么都不留
  · token 过期 / 403 → 自动重拉清单换新签名再取，播放器不用重连

用法：
    python3 iptv_relay_按需直取.py 你的列表.m3u
    python3 iptv_relay_按需直取.py 你的列表.m3u -p 8080
    python3 iptv_relay_按需直取.py            # 用内置远程列表

播放器填：
    本机     http://127.0.0.1:8080/playlist.m3u
    电视手机 http://<电脑局域网IP>:8080/playlist.m3u   （启动时会打印出来）

看状态：http://127.0.0.1:8080/status
查问题：http://127.0.0.1:8080/diag/频道号   （一眼看出卡在哪一步）
"""

import argparse
import hashlib
import http.server
import json
import os
import re
import socket
import socketserver
import sys
import threading
import time
import urllib.error
import urllib.request
from collections import OrderedDict
from urllib.parse import urljoin, urlsplit

VERSION = "3.1"

MAG_UA = ("Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 "
          "(KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3")

PL_TIMEOUT = 10.0        # 拉清单超时
SEG_TIMEOUT = 20.0       # 拉分片超时
MANIFEST_TTL = 2.0       # 清单缓存时间（同一个台 2 秒内多次请求只打一次源站）
MAP_KEEP = 600.0         # 分片地址映射保留多久
MAP_MAX = 800            # 映射表上限
IDLE_SEC = 120           # 多久没请求算这个台不看了（只用于状态显示和清理映射）
MAX_SEG_BYTES = 64 << 20  # 单片最大 64MB，防跑飞

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_PLAYLIST = ("https://ghfast.top/https://raw.githubusercontent.com/"
                    "SuperNinjap/iptv/main/USA.m3u")

QUALITY = "best"          # best / 1080 / 720 / 480
GLOBAL_HEADERS = {}       # -H 全局附加请求头
VERBOSE = False
LOG_PATH = os.path.join(BASE_DIR, "relay.log")


# ------------------------------------------------------------------ 日志
_log_lock = threading.Lock()


def log(*a):
    msg = " ".join(str(x) for x in a)
    line = time.strftime("[%H:%M:%S] ") + msg
    with _log_lock:
        print(line, flush=True)
        if VERBOSE:
            try:
                if os.path.exists(LOG_PATH) and os.path.getsize(LOG_PATH) > 5 << 20:
                    os.replace(LOG_PATH, LOG_PATH + ".old")
                with open(LOG_PATH, "a", encoding="utf-8") as f:
                    f.write(line + "\n")
            except OSError:
                pass


# ------------------------------------------------------------------ HTTP
class _NoRedirect(urllib.request.HTTPRedirectHandler):
    """302 自己接管：源站跳转、直接 200 返清单两种情况都认。"""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise urllib.error.HTTPError(req.full_url, code, msg, headers, fp)


_OPENER = urllib.request.build_opener(_NoRedirect)


def http_get(url, headers, timeout, rng=None, method="GET"):
    """自己跟 3xx。返回 (status, resp_headers, body, final_url)。"""
    cur = url
    for _ in range(6):
        hdrs = dict(headers)
        if rng:
            hdrs["Range"] = rng
        try:
            req = urllib.request.Request(cur, headers=hdrs, method=method)
            with _OPENER.open(req, timeout=timeout) as r:
                body = r.read(MAX_SEG_BYTES)
                return r.status, dict(r.headers), body, r.geturl() or cur
        except urllib.error.HTTPError as e:
            hd = dict(e.headers or {})
            loc = hd.get("Location") or hd.get("location")
            if e.code in (301, 302, 303, 307, 308) and loc:
                cur = urljoin(cur, loc)
                continue
            try:
                body = e.read(MAX_SEG_BYTES) if e.fp else b""
            except Exception:
                body = b""
            return e.code, hd, body, cur
        except Exception as e:
            return 0, {}, str(e).encode(), cur
    return 508, {}, b"too many redirects", cur


def guess_ctype(url, ctype=None):
    if ctype and "octet-stream" not in ctype.lower() and ctype.strip():
        return ctype.split(";")[0].strip()
    p = urlsplit(url).path.lower()
    if p.endswith((".ts", ".m2ts")):
        return "video/mp2t"
    if p.endswith((".mp4", ".m4s", ".m4v")):
        return "video/mp4"
    if p.endswith((".aac",)):
        return "audio/aac"
    if p.endswith((".m3u8", ".m3u")):
        return "application/vnd.apple.mpegurl"
    return "application/octet-stream"


# ------------------------------------------------------------------ 列表解析
def _apply_vlcopt(ch, val):
    if "=" not in val:
        return
    k, v = val.split("=", 1)
    k, v = k.strip().lower(), v.strip()
    if k in ("http-user-agent", "user-agent", "http-useragent"):
        ch["ua"] = v
    elif k in ("http-referrer", "http-referer", "referer", "referrer"):
        ch["referer"] = v
    elif k == "http-origin":
        ch["origin"] = v
    elif k == "http-cookie":
        ch["headers"]["Cookie"] = v


def _apply_exthttp(ch, raw):
    try:
        obj = json.loads(raw)
    except Exception:
        return
    if not isinstance(obj, dict):
        return
    for k, v in obj.items():
        if not isinstance(v, str):
            continue
        kl = k.lower()
        if kl in ("user-agent", "user_agent"):
            ch["ua"] = v
        elif kl in ("referer", "referrer"):
            ch["referer"] = v
        elif kl == "origin":
            ch["origin"] = v
        else:
            ch["headers"][k] = v


def parse_m3u(text):
    """返回频道字典列表。会吃掉 #EXTVLCOPT / #EXTHTTP / #EXTGRP 里的请求头。"""
    out = []
    cur = None
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        up = line.upper()
        if up.startswith("#EXTM3U"):
            continue
        if up.startswith("#EXTINF"):
            cur = {"name": "", "group": "", "logo": "", "ua": "",
                   "referer": "", "origin": "", "headers": {}}
            m = re.search(r'tvg-logo="([^"]*)"', line, re.I)
            if m:
                cur["logo"] = m.group(1)
            m = re.search(r'group-title="([^"]*)"', line, re.I)
            if m:
                cur["group"] = m.group(1)
            cur["name"] = line.rsplit(",", 1)[-1].strip() or "未命名"
            continue
        if cur is not None:
            if up.startswith("#EXTGRP:"):
                cur["group"] = line.split(":", 1)[1].strip()
                continue
            if up.startswith("#EXTVLCOPT:"):
                _apply_vlcopt(cur, line.split(":", 1)[1])
                continue
            if up.startswith("#EXTHTTP:"):
                _apply_exthttp(cur, line.split(":", 1)[1])
                continue
            if up.startswith("#KODIPROP:") or up.startswith("#EXT-X-"):
                continue
        if line.startswith("#"):
            continue
        if cur is None:
            continue
        cur["url"] = line
        out.append(cur)
        cur = None
    return out


def to_entry(u):
    """把播放地址改成要 m3u8 的形态。"""
    low = u.lower()
    # 本身就是整份列表（Xtream 的 get.php、type=m3u_plus 那种）→ 一个字都别改
    if "get.php" in low or "type=m3u" in low or "output=m3u" in low:
        return u
    if "extension=" in u:
        return re.sub(r"extension=\w*", "extension=m3u8", u)
    if ".m3u8" in low:
        return u
    if re.search(r"\.ts(\?|$)", u, re.I):
        return re.sub(r"\.ts(\?|$)", r".m3u8\1", u, flags=re.I)
    sep = "&" if "?" in u else "?"
    return u + sep + "extension=m3u8"


def load_playlist(src, timeout=90):
    if src == "-":
        return sys.stdin.read()
    if os.path.exists(src):
        with open(src, encoding="utf-8", errors="ignore") as f:
            return f.read()
    req = urllib.request.Request(src, headers={"User-Agent": MAG_UA})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8", "ignore")


# ------------------------------------------------------------------ 频道
class SourceError(Exception):
    pass


class Channel:
    def __init__(self, idx, info, default_ua):
        self.idx = idx
        self.name = info["name"]
        self.group = info.get("group", "")
        self.logo = info.get("logo", "")
        self.raw_url = info["url"]
        self.entry = to_entry(self.raw_url)

        ua = info.get("ua") or default_ua or MAG_UA
        h = {"User-Agent": ua, "Accept": "*/*",
             "Accept-Encoding": "identity", "Connection": "close"}
        if info.get("referer"):
            h["Referer"] = info["referer"]
        if info.get("origin"):
            h["Origin"] = info["origin"]
        h.update(GLOBAL_HEADERS)
        h.update(info.get("headers") or {})
        self.headers = h

        self.lock = threading.Lock()
        self.manifest = None          # 已改写成 /s/ 地址的本地清单
        self.manifest_ts = 0.0
        self.manifest_url = None
        self.variant_url = None       # 主清单里选中的子清单
        self.seg_map = OrderedDict()  # key -> url
        self.ctype_map = {}           # key -> content-type
        self.last_client = 0.0
        self.seg_ok = 0
        self.seg_fail = 0
        self.last_err = ""

    # ------------------------------------------------ 源站交互
    def _fetch_manifest(self):
        """拉一份清单，跟随主清单，返回 (文本, 真实地址)。"""
        url = self.variant_url or self.entry
        st, hd, body, final = http_get(url, self.headers, PL_TIMEOUT)
        if st in (0, 508):
            raise SourceError(f"连不上源站（{body[:60].decode('utf-8', 'ignore')}）")
        if st >= 400:
            raise SourceError(f"源站返回 HTTP {st}")
        text = body.decode("utf-8", "ignore")
        if not text.lstrip().startswith("#EXTM3U"):
            raise SourceError(f"源站返回的不是 m3u8（HTTP {st}，"
                              f"开头：{text[:60].replace(chr(10), ' ')}）")

        # 主清单 → 选一路子清单
        if "#EXT-X-STREAM-INF" in text:
            sub = pick_variant(text, final)
            if sub:
                self.variant_url = sub
                st2, hd2, b2, f2 = http_get(sub, self.headers, PL_TIMEOUT)
                if st2 < 400:
                    t2 = b2.decode("utf-8", "ignore")
                    if t2.lstrip().startswith("#EXTM3U"):
                        return t2, f2
                raise SourceError(f"子清单取不到（HTTP {st2}）")

        if "#EXTINF" not in text:
            raise SourceError("清单里没有分片（可能是空窗口，稍后自动重试）")
        return text, final

    @staticmethod
    def _key_of(path, occ):
        h = hashlib.blake2s(path.encode("utf-8", "ignore"), digest_size=6).hexdigest()
        return f"{h}{occ}"

    def _rewrite(self, text, base):
        """把分片 / 密钥 / init 段改成本地地址，同时更新 key→url 映射。"""
        out = []
        occ = {}
        now = time.time()
        n_seg = 0
        byterange = "#EXT-X-BYTERANGE" in text
        # 有些源每个分片路径完全相同、只靠 ?seq= 区分。这种没法稳定编号，
        # 直接把原地址给播放器，避免串片。
        paths = [urlsplit(urljoin(base, l.strip())).path
                 for l in text.splitlines()
                 if l.strip() and not l.strip().startswith("#")]
        dup_path = len(paths) != len(set(paths))
        if dup_path and not getattr(self, "_dup_warned", False):
            self._dup_warned = True
            log(f"[{self.idx}]{self.name} 这个台分片路径重名，改走原始地址直给")
        for raw in text.splitlines():
            line = raw.rstrip()
            s = line.strip()
            if not s:
                out.append(line)
                continue
            if s.startswith("#EXT-X-KEY") or s.startswith("#EXT-X-MAP") or \
                    s.startswith("#EXT-X-SESSION-KEY"):
                m = re.search(r'URI="([^"]+)"', s)
                if m and not byterange:
                    real = urljoin(base, m.group(1))
                    p = urlsplit(real).path
                    occ[p] = occ.get(p, 0) + 1
                    k = self._key_of(p, occ[p])
                    with self.lock:
                        self.seg_map[k] = real
                        self.ctype_map[k] = guess_ctype(real)
                        self.seg_map.move_to_end(k)
                    ext = "mp4" if s.startswith("#EXT-X-MAP") else "bin"
                    s = s.replace(m.group(1), f"/ch/{self.idx}/a/{k}.{ext}")
                out.append(s)
                continue
            if s.startswith("#"):
                out.append(s)
                continue
            real = urljoin(base, s)
            n_seg += 1
            if byterange or dup_path:
                out.append(real)          # 按字节段切片的源，直接给原地址最稳
                continue
            p = urlsplit(real).path
            occ[p] = occ.get(p, 0) + 1
            k = self._key_of(p, occ[p])
            with self.lock:
                self.seg_map[k] = real
                self.ctype_map[k] = guess_ctype(real)
                self.seg_map.move_to_end(k)
            ext = real.split("?")[0].rsplit(".", 1)[-1].lower()
            if ext not in ("ts", "m4s", "mp4", "aac", "m4a", "m4v"):
                ext = "ts"
            out.append(f"/ch/{self.idx}/s/{k}.{ext}")

        # 映射表瘦身
        with self.lock:
            while len(self.seg_map) > MAP_MAX:
                self.seg_map.popitem(last=False)
        self._last_n = n_seg
        self._last_ts = now
        return "\n".join(out) + "\n"

    def manifest_text(self, force=False):
        """拿一份最新的、已改写成本地地址的清单。"""
        with self.lock:
            if not force and self.manifest and time.time() - self.manifest_ts < MANIFEST_TTL:
                return self.manifest
        text, final = self._fetch_manifest()
        local = self._rewrite(text, final)
        with self.lock:
            self.manifest = local
            self.manifest_url = final
            self.manifest_ts = time.time()
            self.last_err = ""
        return local

    def resolve(self, key):
        with self.lock:
            return self.seg_map.get(key)

    def get_segment(self, key, rng=None):
        """按 key 取分片。403/404 时重拉清单换新签名再试一次。"""
        url = self.resolve(key)
        if url is None:
            try:
                self.manifest_text(force=True)
            except SourceError as e:
                self.last_err = str(e)
                raise
            url = self.resolve(key)
            if url is None:
                raise SourceError("这个分片已经滚出直播窗口了")
        st, hd, body, final = http_get(url, self.headers, SEG_TIMEOUT, rng=rng)
        if st in (401, 403, 404, 410) or st == 0:
            # 签名/地址过期 → 重拉清单拿新地址，再取一次
            try:
                self.manifest_text(force=True)
            except SourceError:
                pass
            url2 = self.resolve(key) or url
            st, hd, body, final = http_get(url2, self.headers, SEG_TIMEOUT, rng=rng)
        if st >= 400 or st == 0:
            self.seg_fail += 1
            self.last_err = f"分片 HTTP {st}"
            raise SourceError(f"分片取不到（HTTP {st}）")
        if not body:
            self.seg_fail += 1
            self.last_err = "分片是空的"
            raise SourceError("分片是空的")
        self.seg_ok += 1
        ctype = hd.get("Content-Type") or self.ctype_map.get(key)
        return st, hd, body, guess_ctype(url, ctype)


def pick_variant(text, base):
    """主清单里挑一路。QUALITY=best 取最高，数字则取不超过它的最高一档。"""
    cands = []
    bw, res = 0, 0
    for line in text.splitlines():
        s = line.strip()
        if s.upper().startswith("#EXT-X-STREAM-INF"):
            m = re.search(r"BANDWIDTH=(\d+)", s)
            bw = int(m.group(1)) if m else 0
            m = re.search(r"RESOLUTION=(\d+)x(\d+)", s)
            res = int(m.group(2)) if m else 0
        elif s and not s.startswith("#"):
            cands.append((bw, res, urljoin(base, s)))
            bw, res = 0, 0
    if not cands:
        return None
    if QUALITY == "best":
        return max(cands, key=lambda c: (c[1], c[0]))[2]
    try:
        want = int(QUALITY)
    except ValueError:
        return max(cands, key=lambda c: (c[1], c[0]))[2]
    fit = [c for c in cands if c[1] and c[1] <= want]
    if fit:
        return max(fit, key=lambda c: (c[1], c[0]))[2]
    return min(cands, key=lambda c: (c[1] or 9999, c[0]))[2]


# ------------------------------------------------------------------ 管理
CHANS = {}
LOCK = threading.Lock()


def get_chan(idx, touch=True):
    with LOCK:
        ch = CHANS.get(idx)
    if ch and touch:
        ch.last_client = time.time()
    return ch


class Handler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "ZakaRelay/" + VERSION

    def log_message(self, *a):
        pass

    # ------------------------------------------------ 输出
    def _send(self, body, ctype, status=200, extra=None, cache=False):
        if isinstance(body, str):
            body = body.encode()
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "*")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        if cache:
            self.send_header("Cache-Control", "public, max-age=30")
        else:
            self.send_header("Cache-Control", "no-cache, no-store, must-revalidate")
            self.send_header("Pragma", "no-cache")
            self.send_header("Expires", "0")
        self.end_headers()
        if self.command != "HEAD":
            try:
                self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError):
                pass

    def _fail(self, code, msg, retry=None):
        extra = {"Retry-After": str(retry)} if retry else None
        return self._send(msg, "text/plain; charset=utf-8", code, extra)

    # ------------------------------------------------ 路由
    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, HEAD, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "*")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_HEAD(self):
        self.do_GET()

    def do_GET(self):
        path = self.path.split("?")[0]
        try:
            self._route(path)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:
            log(f"请求处理出错 {path}：{type(e).__name__} {e}")
            try:
                self._fail(500, f"中转出错：{type(e).__name__}")
            except Exception:
                pass

    def _route(self, path):
        # 总列表
        if path in ("/", "/playlist.m3u", "/playlist.m3u8", "/index.m3u8"):
            host = self.headers.get("Host", "127.0.0.1")
            lines = ["#EXTM3U", "#EXT-X-VERSION:3"]
            with LOCK:
                items = list(CHANS.items())
            for idx, ch in items:
                g = f' group-title="{ch.group}"' if ch.group else ""
                lg = f' tvg-logo="{ch.logo}"' if ch.logo else ""
                lines.append(f"#EXTINF:-1{lg}{g},{ch.name}")
                lines.append(f"http://{host}/ch/{idx}/live.m3u8")
            return self._send("\n".join(lines) + "\n",
                              "application/vnd.apple.mpegurl")

        # 单频道清单
        m = re.match(r"^/ch/(\d+)/(live|index)\.m3u8$", path)
        if m:
            ch = get_chan(int(m.group(1)))
            if not ch:
                return self._fail(404, "没有这个频道号")
            try:
                text = ch.manifest_text()
            except SourceError as e:
                ch.last_err = str(e)
                log(f"[{ch.idx}]{ch.name} 清单失败：{e}")
                # 取不到 m3u8 时，如果这是个原始流地址（不是列表），直接把原地址甩给播放器试直连
                if ch.entry != ch.raw_url:
                    log(f"[{ch.idx}]{ch.name} 改走原始地址直连")
                    return self._send("", "text/plain", status=302,
                                      extra={"Location": ch.raw_url})
                return self._fail(502, f"源站这边取不到这个台：{e}", retry=3)
            return self._send(text, "application/vnd.apple.mpegurl")

        # 分片
        m = re.match(r"^/ch/(\d+)/s/([0-9a-zA-Z]+)\.\w+$", path)
        if m:
            ch = get_chan(int(m.group(1)))
            if not ch:
                return self._fail(404, "没有这个频道号")
            key = m.group(2)
            rng = self.headers.get("Range")
            try:
                st, hd, body, ctype = ch.get_segment(key, rng=rng)
            except SourceError as e:
                log(f"[{ch.idx}]{ch.name} 分片失败：{e}")
                return self._fail(404, f"分片取不到：{e}")
            extra = {"Accept-Ranges": "bytes"}
            status = 200
            if st == 206:
                status = 206
                cr = hd.get("Content-Range")
                if cr:
                    extra["Content-Range"] = cr
            return self._send(body, ctype, status=status, extra=extra, cache=True)

        # 密钥 / init 段
        m = re.match(r"^/ch/(\d+)/a/([0-9a-zA-Z]+)\.\w+$", path)
        if m:
            ch = get_chan(int(m.group(1)))
            if not ch:
                return self._fail(404, "没有这个频道号")
            url = ch.resolve(m.group(2))
            if not url:
                try:
                    ch.manifest_text(force=True)
                except SourceError:
                    pass
                url = ch.resolve(m.group(2))
            if not url:
                return self._fail(404, "这个附加资源已失效")
            st, hd, body, final = http_get(url, ch.headers, SEG_TIMEOUT)
            if st >= 400 or not body:
                return self._fail(404, f"附加资源取不到（HTTP {st}）")
            return self._send(body, guess_ctype(url, hd.get("Content-Type")),
                              cache=True)

        # 状态
        if path == "/status":
            with LOCK:
                items = list(CHANS.items())
            now = time.time()
            active = [c for _, c in items if c.last_client and now - c.last_client < IDLE_SEC]
            rows = [f"Zaka 中转 v{VERSION}   频道 {len(items)}   近 {IDLE_SEC}s 内播放 {len(active)}"]
            for c in active:
                rows.append(
                    f"#{c.idx} {c.name} | 取片成功 {c.seg_ok} 失败 {c.seg_fail} "
                    f"| 清单 {max(0, int(now - c.manifest_ts))}s 前 "
                    f"| 上次请求 {max(0, int(now - c.last_client))}s 前"
                    + (f" | 最后错误：{c.last_err}" if c.last_err else ""))
            if len(rows) == 1:
                rows.append("（现在没有频道在播；播放器点开某个台后这里才有内容）")
            rows.append("")
            rows.append("查某个台为什么播不了：在地址后面加 /diag/频道号，比如 /diag/1")
            return self._send("\n".join(rows), "text/plain; charset=utf-8")

        # 诊断
        m = re.match(r"^/diag/(\d+)$", path)
        if m:
            ch = get_chan(int(m.group(1)), touch=False)
            if not ch:
                return self._fail(404, "没有这个频道号")
            return self._send(self._diag(ch), "text/plain; charset=utf-8")
        if path == "/diag":
            return self._send("用法：/diag/频道号，比如 /diag/1\n"
                              "频道号在 /playlist.m3u 里的顺序，或者 /status 里能看到。",
                              "text/plain; charset=utf-8")
        return self._fail(404, "没有这个地址")

    # ------------------------------------------------ 诊断
    def _diag(self, ch):
        out = [f"频道 #{ch.idx}  {ch.name}",
               f"原始地址：{ch.raw_url}",
               f"请求入口：{ch.entry}",
               f"请求头 UA：{ch.headers.get('User-Agent', '')[:80]}",
               f"Referer：{ch.headers.get('Referer', '(无)')}", ""]
        t0 = time.time()
        try:
            text, final = ch._fetch_manifest()
        except SourceError as e:
            out.append(f"[1] 拉清单  失败：{e}")
            out.append("")
            out.append("结论：卡在第一步，连清单都拿不到。")
            out.append("→ 4xx：多半要 Referer / 特定 UA / MAC，或者地址里的 token 已经失效（回列表里换新地址）")
            out.append("→ 超时：这台机器被墙或源站关机了")
            return "\n".join(out)
        dt = time.time() - t0

        segs = [l.strip() for l in text.splitlines()
                if l.strip() and not l.strip().startswith("#")]
        td = re.search(r"#EXT-X-TARGETDURATION:(\d+)", text)
        out.append(f"[1] 拉清单  OK  {dt*1000:.0f}ms  最终地址 {final}")
        out.append(f"    清单 {len(text)} 字节，分片 {len(segs)} 个，"
                   f"TARGETDURATION {td.group(1) if td else '?'}")
        if ch.variant_url:
            out.append(f"    主清单选了这一路：{ch.variant_url}")
        if not segs:
            out.append("结论：清单里没有分片，源站给的是空窗口（稍后会自己好，或这个台本身没信号）")
            return "\n".join(out)

        first = urljoin(final, segs[0])
        out.append(f"[2] 首个分片 {first}")
        t1 = time.time()
        st, hd, body, _ = http_get(first, ch.headers, SEG_TIMEOUT)
        dt1 = time.time() - t1
        out.append(f"    HTTP {st}  {len(body)/1024:.0f}KB  {dt1*1000:.0f}ms  "
                   f"类型 {hd.get('Content-Type', '?')}")
        if st >= 400 or not body:
            out.append("")
            out.append(f"结论：清单能拿到，但分片取不到（HTTP {st}）。")
            out.append("→ 403：分片要单独的签名 / 要带 Referer / 换 UA 试试"
                       "（列表里给这个台加一行 #EXTVLCOPT:http-referrer=…）")
            out.append("→ 404：地址已过期，源站换签名了，重开一次频道即可")
            return "\n".join(out)

        out.append("")
        out.append("[3] 改写后的首条：")
        try:
            local = ch._rewrite(text, final)
            for l in local.splitlines():
                if "/s/" in l:
                    out.append(f"    {l.strip()}")
                    break
        except Exception as e:
            out.append(f"    改写失败：{e}")
        out.append("")
        out.append("结论：这个台整条链路是通的，播放器直接打开下面这个地址试试：")
        out.append(f"    http://127.0.0.1:{self.server.server_address[1]}/ch/{ch.idx}/live.m3u8")
        return "\n".join(out)


# ------------------------------------------------------------------ 启动
def bind_server(port, handler):
    for p in range(port, port + 30):
        try:
            srv = socketserver.ThreadingTCPServer(("0.0.0.0", p), handler)
            srv.daemon_threads = True
            srv.allow_reuse_address = True
            if p != port:
                log(f"端口 {port} 被占用，改用 {p}")
            return srv, p
        except OSError:
            continue
    raise OSError(f"{port}~{port+29} 端口全被占用")


def detect_lan_ip():
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


def write_local_playlist(path, port, host):
    with open(path, "w", encoding="utf-8") as f:
        f.write("#EXTM3U\n")
        with LOCK:
            items = list(CHANS.items())
        for i, c in items:
            g = f' group-title="{c.group}"' if c.group else ""
            lg = f' tvg-logo="{c.logo}"' if c.logo else ""
            f.write(f"#EXTINF:-1{lg}{g},{c.name}\n")
            f.write(f"http://{host}:{port}/ch/{i}/live.m3u8\n")


def sanitize_args(ap):
    raw = sys.argv[1:]
    if len(raw) == 1 and " " in raw[0]:
        log(f"参数被合并成一项 {raw[0]!r}，自动拆分")
        raw = raw[0].split()
    a = ap.parse_args(raw)
    if a.src and re.fullmatch(r"\d{2,5}", a.src.strip()):
        log(f"参数 {a.src!r} 是纯数字，当成端口号处理")
        a.port = int(a.src)
        a.src = DEFAULT_PLAYLIST
    elif a.src and a.src.startswith("-"):
        a.src = DEFAULT_PLAYLIST
    return a


def main():
    global QUALITY, GLOBAL_HEADERS, VERBOSE, IDLE_SEC
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("src", nargs="?", default=DEFAULT_PLAYLIST,
                    help="m3u 来源：本地路径 / http(s) / - (stdin)")
    ap.add_argument("-p", "--port", type=int, default=8080)
    ap.add_argument("-o", "--out", default=os.path.join(BASE_DIR, "local_playlist.m3u"))
    ap.add_argument("-u", "--ua", default=MAG_UA, help="默认 UA")
    ap.add_argument("-H", "--header", action="append", default=[],
                    help='全局请求头，如 -H "Referer: http://xxx"')
    ap.add_argument("-q", "--quality", default="best",
                    help="多码率时选哪一路：best/1080/720/480")
    ap.add_argument("-i", "--idle", type=int, default=IDLE_SEC)
    ap.add_argument("-f", "--filter", default="")
    ap.add_argument("-r", "--reload", type=int, default=30, help="分钟，0=不重拉")
    ap.add_argument("-v", "--verbose", action="store_true", help="写运行日志 relay.log")
    # 兼容旧参数，别让老命令报错
    ap.add_argument("-s", "--segdir", default="")
    ap.add_argument("-w", "--window", type=int, default=0)
    a = sanitize_args(ap)

    VERBOSE = a.verbose
    QUALITY = str(a.quality)
    IDLE_SEC = max(20, a.idle)
    for h in a.header:
        if ":" in h:
            k, v = h.split(":", 1)
            GLOBAL_HEADERS[k.strip()] = v.strip()

    log(f"Zaka 直播中转 v{VERSION}（按需直取，不预缓存、不落盘）")
    text = load_playlist(a.src)
    chans = parse_m3u(text)
    if a.filter:
        chans = [c for c in chans if a.filter in c["name"]]
    if not chans:
        log("没解析到频道，检查列表格式（每段要有 #EXTINF 行 + 地址行）")
        sys.exit(1)
    for i, info in enumerate(chans, 1):
        CHANS[i] = Channel(i, info, a.ua)
    log(f"载入 {len(CHANS)} 个频道")

    httpd, port = bind_server(a.port, Handler)
    lan = detect_lan_ip()
    try:
        write_local_playlist(a.out, port, lan)
        log(f"已写出播放列表：{a.out}")
    except OSError as e:
        log(f"播放列表写出失败：{e}")

    log("─" * 46)
    log(f"本机播放：http://127.0.0.1:{port}/playlist.m3u")
    log(f"电视/手机：http://{lan}:{port}/playlist.m3u")
    log(f"看状态：http://127.0.0.1:{port}/status")
    log("─" * 46)

    if a.reload > 0 and a.src.startswith("http"):
        threading.Thread(target=reload_loop, args=(a.src, a.ua, a.reload, a.filter, a.out, port),
                         daemon=True).start()

    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        log("已停止")
    finally:
        try:
            httpd.server_close()
        except Exception:
            pass


def reload_loop(src, ua, minutes, flt, out, port):
    lan = detect_lan_ip()
    while True:
        time.sleep(minutes * 60)
        try:
            chans = parse_m3u(load_playlist(src))
            if flt:
                chans = [c for c in chans if flt in c["name"]]
            if not chans:
                log("重拉结果为空，跳过")
                continue
            added = updated = 0
            with LOCK:
                for i, info in enumerate(chans, 1):
                    ch = CHANS.get(i)
                    if ch is None:
                        CHANS[i] = Channel(i, info, ua)
                        added += 1
                    else:
                        new_entry = to_entry(info["url"])
                        if ch.entry != new_entry:
                            ch.entry = new_entry
                            ch.variant_url = None
                            ch.manifest = None
                            ch.manifest_ts = 0.0
                            updated += 1
            try:
                write_local_playlist(out, port, lan)
            except OSError:
                pass
            log(f"列表刷新：新增 {added}，更新 {updated}，共 {len(CHANS)}")
        except Exception as e:
            log(f"列表重拉失败：{e}")


if __name__ == "__main__":
    main()
