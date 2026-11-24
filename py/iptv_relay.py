#!/usr/bin/env python3
"""
IPTV 直播中转器 —— 解决"每播几十秒就停、要再点一下"的问题。

原理：源站签发的播放 token 只有约 30 秒寿命，到期返回 509。
本脚本在后台自动续期 token、抢先下载切片、重新拼装成本地滚动 m3u8，
播放器只读本地 m3u8，因此能无限连续播放。

用法：
    python3 iptv_relay.py "http://line.mag7070.eu/play/live.php?mac=...&stream=...&extension=m3u8&play_token=..."
然后在播放器里打开：  http://127.0.0.1:8080/live.m3u8
"""

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

MAG_UA = ("Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 "
          "(KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3")

# 服务器给 token 的寿命约 30s，提前到 18s 续，留足余量
REFRESH_INTERVAL = 18
# 本地保留的切片数（每片约 10s）
WINDOW = 30
LISTEN_PORT = 8080
SEG_DIR = "/tmp/iptv_segs"


def log(*a):
    print(time.strftime("[%H:%M:%S]"), *a, flush=True)


class Relay:
    def __init__(self, entry_url):
        # 强制走 m3u8 模式
        self.entry = re.sub(r"extension=\w*", "extension=m3u8", entry_url)
        if "extension=" not in self.entry:
            self.entry += "&extension=m3u8"
        self.segs = OrderedDict()      # seq(int) -> {"url": str, "dur": float, "local": str|None}
        self.lock = threading.Lock()
        self.token_fail = 0
        self.running = True

    # ---------- 取新 token 得到 m3u8 地址 ----------
    def get_playlist_url(self):
        req = urllib.request.Request(self.entry, headers={"User-Agent": MAG_UA})
        try:
            with urllib.request.urlopen(req, timeout=20) as r:
                return r.geturl() if r.geturl() != self.entry else r.headers.get("Location")
        except urllib.error.HTTPError as e:
            log(f"取 token 失败 HTTP {e.code}")
            return None
        except Exception as e:
            log(f"取 token 异常 {e}")
            return None

    # ---------- 解析 m3u8 ----------
    def parse_m3u8(self, text, base):
        m = re.search(r"#EXT-X-MEDIA-SEQUENCE:(\d+)", text)
        base_seq = int(m.group(1)) if m else 0
        root = re.match(r"(https?://[^/]+)", base)
        root = root.group(1) if root else ""
        out, dur, idx = [], None, 0
        for line in text.splitlines():
            line = line.strip()
            if line.startswith("#EXTINF:"):
                try:
                    dur = float(line.split(":")[1].split(",")[0])
                except Exception:
                    dur = 10.0
            elif line and not line.startswith("#") and ".ts" in line:
                url = line if line.startswith("http") else root + line
                mm = re.search(r"_(\d+)\.ts", line)
                seq = int(mm.group(1)) if mm else base_seq + idx
                out.append((seq, url, dur or 10.0))
                idx += 1
        return out

    # ---------- 主刷新循环 ----------
    def refresher(self):
        while self.running:
            start = time.time()
            pl = self.get_playlist_url()
            if pl:
                req = urllib.request.Request(pl, headers={"User-Agent": MAG_UA})
                try:
                    with urllib.request.urlopen(req, timeout=15) as r:
                        text = r.read().decode("utf-8", "ignore")
                    items = self.parse_m3u8(text, pl)
                    with self.lock:
                        new = 0
                        for seq, url, dur in items:
                            if seq not in self.segs:
                                self.segs[seq] = {"url": url, "dur": dur, "local": None}
                                new += 1
                        # 丢弃过老切片
                        while len(self.segs) > WINDOW * 2:
                            self.segs.popitem(last=False)
                    self.token_fail = 0
                    log(f"刷新成功 seq={[i[0] for i in items]} 新增={new} 池={len(self.segs)}")
                except Exception as e:
                    log(f"拉 m3u8 失败 {e}")
                    self.token_fail += 1
            else:
                self.token_fail += 1
                if self.token_fail > 5:
                    log("连续失败过多，退避 10s")
                    time.sleep(10)
            time.sleep(max(1, REFRESH_INTERVAL - (time.time() - start)))

    # ---------- 下载切片 ----------
    def downloader(self):
        os.makedirs(SEG_DIR, exist_ok=True)
        while self.running:
            todo = []
            with self.lock:
                for seq, info in self.segs.items():
                    if info["local"] is None:
                        todo.append((seq, info["url"]))
            for seq, url in todo:
                path = os.path.join(SEG_DIR, f"{seq}.ts")
                try:
                    req = urllib.request.Request(url, headers={"User-Agent": MAG_UA})
                    with urllib.request.urlopen(req, timeout=25) as r, open(path, "wb") as f:
                        shutil.copyfileobj(r, f)
                    if os.path.getsize(path) > 1000:
                        with self.lock:
                            if seq in self.segs:
                                self.segs[seq]["local"] = path
                except Exception as e:
                    log(f"切片 {seq} 下载失败 {e}")
            time.sleep(1.5)

    # ---------- 生成本地 m3u8 ----------
    def build_m3u8(self):
        with self.lock:
            ready = [(s, i) for s, i in self.segs.items() if i["local"]]
        if not ready:
            return "#EXTM3U\n#EXT-X-VERSION:3\n#EXT-X-TARGETDURATION:12\n#EXT-X-MEDIA-SEQUENCE:0\n"
        ready.sort(key=lambda x: x[0])
        ready = ready[-WINDOW:]
        first = ready[0][0]
        out = ["#EXTM3U", "#EXT-X-VERSION:3", "#EXT-X-TARGETDURATION:14",
               f"#EXT-X-MEDIA-SEQUENCE:{first}"]
        prev = None
        for seq, info in ready:
            if prev is not None and seq != prev + 1:
                out.append("#EXT-X-DISCONTINUITY")
            out.append(f"#EXTINF:{info['dur']:.3f},")
            out.append(f"/seg/{seq}.ts")
            prev = seq
        return "\n".join(out) + "\n"


def make_handler(relay):
    class H(http.server.BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def do_GET(self):
            if self.path.startswith("/live.m3u8") or self.path == "/":
                body = relay.build_m3u8().encode()
                self.send_response(200)
                self.send_header("Content-Type", "application/vnd.apple.mpegurl")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Access-Control-Allow-Origin", "*")
                self.end_headers()
                self.wfile.write(body)
            elif self.path.startswith("/seg/"):
                fn = self.path.split("/")[-1].split("?")[0]
                path = os.path.join(SEG_DIR, fn)
                if os.path.exists(path):
                    data = open(path, "rb").read()
                    self.send_response(200)
                    self.send_header("Content-Type", "video/mp2t")
                    self.send_header("Content-Length", str(len(data)))
                    self.end_headers()
                    self.wfile.write(data)
                else:
                    self.send_error(404)
            else:
                self.send_error(404)
    return H


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    relay = Relay(sys.argv[1])
    threading.Thread(target=relay.refresher, daemon=True).start()
    threading.Thread(target=relay.downloader, daemon=True).start()
    socketserver.ThreadingTCPServer.allow_reuse_address = True
    httpd = socketserver.ThreadingTCPServer(("0.0.0.0", LISTEN_PORT), make_handler(relay))
    log(f"中转已启动 → http://127.0.0.1:{LISTEN_PORT}/live.m3u8")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        relay.running = False
        log("已停止")


if __name__ == "__main__":
    main()
