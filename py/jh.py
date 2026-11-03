# coding=utf-8
# !/usr/bin/python
# ============================================================================
# 鉴黄师 —— OK影视 / 影视仓 / TVBox 通用 PY 源
# 由 hiker 版《鉴黄师_hiker_修复版.json》移植
#
# 线路说明：
#   ▶ 直连      直接给播放器现取的 m3u8 地址（每次点播放都重新解析）
#   ▶ 清单代理  本地把清单绝对化后再交给播放器（播放器拼相对地址丢签名时用）
#   ▶ 续签代理  播放器每个分片都经本地代理，代理侧按需重取清单拿新签名（不断流）
#
# init(extend) 可传 JSON，全部可选：
#   {"cookie":"cf_clearance=xxxx; ...", "jina_key":"jina_xxx",
#    "relay":"https://r.jina.ai/", "port":9978, "timeout":20}
#   cookie  : 手机浏览器打开站点后复制的整串 Cookie，有它直连成功率最高
#   jina_key: r.jina.ai 的免费 key，被站点防火墙拦时用来中转
#   port    : 本地 HTTP 服务端口，只有“续签代理”线路需要，默认 9978
# ============================================================================

import sys
import json
import re
import time
import base64
import urllib.parse
import urllib.request
import urllib.error
import html as htmlmod

try:
    import requests
    try:
        import urllib3
        urllib3.disable_warnings()
    except Exception:
        pass
except Exception:
    requests = None

sys.path.append('..')
try:
    from base.spider import Spider as _BaseSpider
except Exception:
    class _BaseSpider(object):
        pass


SITE = 'https://www.javrate.com'
RELAY = 'https://r.jina.ai/'
UA = ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 '
      '(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36')

CLASSES = [
    ('最新更新', '/movie/new'),
    ('无码A片', '/menu/uncensored'),
    ('日本A片', '/menu/censored'),
    ('国产AV', '/menu/chinese'),
    ('中文字幕', '/movie/subtitle'),
    ('最多人看', '/best'),
    ('全部女优', '/actor/list/1-0-1.html'),
    ('知名女优', '/actor/list/1-1-1.html'),
    ('无码女优', '/actor/list/1-2-1.html'),
    ('日本女优', '/actor/list/1-3-1.html'),
    ('国产女优', '/actor/list/1-4-1.html'),
    ('素人女优', '/actor/list/1-5-1.html'),
]

RE_CARD = re.compile(r'<div class="(?:mgn-item|mg-item mg-card)"')
RE_ACTOR_CARD = re.compile(r'<div class="actor-card"')
RE_LINK = re.compile(r'<a href="(/movie/detail/([a-f0-9\-]+)\.html)"[^>]*title="([^"]*)"')
RE_ACTOR_LINK = re.compile(r'<a href="(/actor/detail/([a-f0-9\-]+)\.html)"[^>]*title="([^"]*)"')
RE_IMG = re.compile(r'<img[^>]+src="([^"]+)"')
RE_IMG_DATA = re.compile(r'<img[^>]+data-src="([^"]+)"')
RE_YEAR = re.compile(r'mg[n]?-badge--?year[^>]*>([^<]+)')
RE_SUB = re.compile(r'mg[n]?-badge--?subtitle[^>]*>([^<]+)')
RE_ACTRESS = re.compile(r'mg[n]?-actress[^>]*>\s*<a[^>]*>([^<]+)')
RE_ACTRESS_BOX = re.compile(r'mg[n]?-actress[^>]*>(.*?)</div>', re.S)
RE_ACTOR_RIGHT = re.compile(r'<div class="right">\s*([^<]+)')

SRC_PATTERNS = [
    re.compile(r'var\s+source\s*=\s*["\']([^"\']+)["\']'),
    re.compile(r'var\s+now\s*=\s*["\']([^"\']+)["\']'),
    re.compile(r'var\s+(?:m3u8|url|video_url|file|src)\s*=\s*["\']([^"\']+)["\']'),
    re.compile(r'"m3u8"\s*:\s*"([^"]+)"'),
    re.compile(r'"(?:url|file|video)"\s*:\s*"(https?://[^"]+?\.m3u8[^"]*)"'),
    re.compile(r'<source[^>]+src="([^"]+)"'),
    re.compile(r'(https?://[^"\'\s]+?\.m3u8[^"\'\s]*)'),
]


def _b64e(s):
    if not isinstance(s, str):
        s = str(s)
    return base64.urlsafe_b64encode(s.encode('utf-8')).decode('utf-8').rstrip('=')


def _b64d(s):
    s = str(s or '')
    s += '=' * (-len(s) % 4)
    try:
        return base64.urlsafe_b64decode(s.encode('utf-8')).decode('utf-8', 'ignore')
    except Exception:
        return ''


def _clean(s):
    if not s:
        return ''
    s = htmlmod.unescape(str(s))
    return re.sub(r'\s+', ' ', s).strip()


class Spider(_BaseSpider):

    # ------------------------------------------------------------------ 基础
    def getName(self):
        return '鉴黄师'

    def isVideoFormat(self, url):
        return '.m3u8' in str(url or '')

    def manualVideoCheck(self):
        return False

    def destroy(self):
        try:
            if self.sess:
                self.sess.close()
        except Exception:
            pass
        return 'destroy'

    def init(self, extend=''):
        self.ext = {}
        try:
            if isinstance(extend, dict):
                self.ext = dict(extend)
            elif extend:
                txt = str(extend).strip()
                if txt.startswith('{'):
                    self.ext = json.loads(txt)
                elif '=' in txt:
                    for kv in txt.split('&'):
                        if '=' in kv:
                            k, v = kv.split('=', 1)
                            self.ext[k.strip()] = urllib.parse.unquote(v.strip())
        except Exception:
            self.ext = {}

        self.cookie = str(self.ext.get('cookie', '') or '')
        self.jina_key = str(self.ext.get('jina_key', '') or '')
        self.relay = str(self.ext.get('relay', RELAY) or RELAY)
        try:
            self.port = int(self.ext.get('port', 9978) or 9978)
        except Exception:
            self.port = 9978
        try:
            self.timeout = int(self.ext.get('timeout', 20) or 20)
        except Exception:
            self.timeout = 20

        self.sess = None
        if requests:
            try:
                self.sess = requests.Session()
            except Exception:
                self.sess = None

        self.base_headers = {
            'User-Agent': UA,
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
            'Referer': SITE + '/',
        }
        if self.cookie:
            self.base_headers['Cookie'] = self.cookie

        self.port = self._probe_port(self.port)
        self._page_cache = {}
        self._pl_cache = {}
        self._direct_bad_until = 0
        return None

    @staticmethod
    def _probe_port(default):
        """探测 App 的本地 HTTP 端口（续签代理要用），探不到就用默认值"""
        import socket
        ports = [default, 9978, 9979, 8080, 8090, 9999, 9917, 9906]
        seen = []
        for p in ports:
            if p in seen:
                continue
            seen.append(p)
            try:
                sk = socket.create_connection(('127.0.0.1', int(p)), timeout=0.25)
                sk.close()
                return int(p)
            except Exception:
                continue
        return int(default)

    # ------------------------------------------------------------------ HTTP
    def _raw(self, url, headers=None, binary=False, timeout=None):
        """最底层请求：只发一次，不做过盾判断"""
        h = dict(self.base_headers)
        if headers:
            h.update(headers)
        to = timeout or self.timeout
        if not url:
            return b'' if binary else ''
        if self.sess is not None:
            try:
                r = self.sess.get(url, headers=h, timeout=to, verify=False)
                if binary:
                    # 分片/密钥必须校验状态码，签名过期会回 403，不能当成数据
                    if r.status_code < 200 or r.status_code >= 300:
                        return b''
                    return r.content or b''
                return r.content.decode('utf-8', 'ignore') if r.content else ''
            except Exception:
                return b'' if binary else ''
        # 没 requests 时用 urllib
        try:
            req = urllib.request.Request(url, headers=h)
            with urllib.request.urlopen(req, timeout=to) as resp:
                data = resp.read()
            return data if binary else data.decode('utf-8', 'ignore')
        except Exception:
            return b'' if binary else ''

    @staticmethod
    def _is_bad(txt):
        if not txt or len(txt) < 300:
            return True
        for k in ('Just a moment', 'cf-challenge', 'cf-browser-verification',
                  'Enable JavaScript and cookies', '"code":401', 'AuthenticationRequiredError',
                  'Access denied', 'Attention Required'):
            if k in txt:
                return True
        return False

    def _via_relay(self, url, want_html=True, no_cache=False):
        """走 r.jina.ai 中转（它能渲染过站点的防火墙）"""
        if not url:
            return ''
        target = self.relay + url
        h = {'User-Agent': UA, 'X-Return-Format': 'html' if want_html else 'text'}
        if no_cache:
            h['X-No-Cache'] = 'true'     # 播放地址只有几十秒有效期，绝不能吃缓存
        if self.jina_key:
            h['Authorization'] = 'Bearer ' + self.jina_key
        txt = self._raw(target, headers=h, timeout=max(self.timeout, 25))
        return txt or ''

    def _page(self, url, fresh=False):
        """抓页面：直连优先，被防火墙拦了走中转；结果短时缓存"""
        if not url:
            return ''
        now = time.time()
        if not fresh:
            hit = self._page_cache.get(url)
            # 抓成功的缓存 2 分钟；抓空的只留 12 秒，别让一次失败把后面两分钟都堵死
            if hit and now - hit[0] < (120 if hit[1] else 12):
                return hit[1]

        txt = ''
        if now >= self._direct_bad_until:
            txt = self._raw(url)
            if self._is_bad(txt):
                self._direct_bad_until = now + 300   # 直连 5 分钟内不再白等
            else:
                self._page_cache[url] = (now, txt)
                return txt

        txt2 = self._via_relay(url, no_cache=fresh)
        if not self._is_bad(txt2):
            self._page_cache[url] = (now, txt2)
            return txt2

        self._page_cache[url] = (now, txt or '')
        return txt or ''

    # ------------------------------------------------------------------ 工具
    @staticmethod
    def _blocks(html, pattern, size=6000):
        if not html:
            return []
        starts = [m.start() for m in re.finditer(pattern, html)]
        out = []
        for i, s in enumerate(starts):
            end = starts[i + 1] if i + 1 < len(starts) else min(len(html), s + size)
            out.append(html[s:end])
        return out

    @staticmethod
    def _norm(u):
        if not u:
            return ''
        u = _clean(u).replace('\\/', '/')
        if u.startswith('//'):
            return 'https:' + u
        if u.startswith('/'):
            return SITE + u
        return u

    @staticmethod
    def _abs(base, rel):
        if not rel:
            return ''
        rel = rel.replace('\\/', '/').strip()
        if rel.startswith('http'):
            return rel
        if rel.startswith('//'):
            return 'https:' + rel
        m = re.match(r'^(https?://[^/]+)', base or '')
        host = m.group(1) if m else ''
        if rel.startswith('/'):
            return host + rel
        return base[:base.rfind('/') + 1] + rel

    @staticmethod
    def _host(u):
        m = re.match(r'^(https?://[^/]+)', u or '')
        return m.group(1).lower() if m else ''

    @staticmethod
    def _query(u):
        i = (u or '').find('?')
        return u[i + 1:] if i >= 0 else ''

    @staticmethod
    def _add_query(u, q):
        if not q or not u or '?' in u:
            return u
        return u + ('' if '#' in u else '?') + q

    def _abs_q(self, base, rel, playlist):
        """相对地址转绝对，同域分片补上清单里的签名参数"""
        u = self._abs(base, rel)
        if not u:
            return ''
        if self._host(u) != self._host(playlist):
            return u
        return self._add_query(u, self._query(playlist))

    # ------------------------------------------------------------------ 列表解析
    def _cards(self, html):
        out = []
        for b in self._blocks(html, RE_CARD):
            a = RE_LINK.search(b)
            if not a:
                continue
            im = RE_IMG.search(b) or RE_IMG_DATA.search(b)
            pic = self._norm(im.group(1)) if im else ''
            rem = []
            m = RE_YEAR.search(b)
            if m:
                rem.append(_clean(m.group(1)))
            m = RE_SUB.search(b)
            if m:
                rem.append(_clean(m.group(1)))
            acts = []
            am = RE_ACTRESS_BOX.search(b)
            if am:
                acts = [_clean(x) for x in re.findall(r'<a[^>]*>([^<]+)</a>', am.group(1))][:8]
            if not acts:
                acts = [_clean(x) for x in RE_ACTRESS.findall(b)][:8]
            if acts:
                rem.append(','.join(acts))
            out.append({
                'title': _clean(a.group(3)) or a.group(2),
                'img': pic,
                'desc': ' '.join([x for x in rem if x]),
                'url': SITE + a.group(1),
            })
        return out

    def _actor_cards(self, html):
        out = []
        for b in self._blocks(html, RE_ACTOR_CARD):
            a = RE_ACTOR_LINK.search(b)
            if not a:
                continue
            im = RE_IMG.search(b) or RE_IMG_DATA.search(b)
            pic = self._norm(im.group(1)) if im else ''
            m = RE_ACTOR_RIGHT.search(b)
            out.append({
                'title': _clean(a.group(3)) or a.group(2),
                'img': pic,
                'desc': _clean(m.group(1)) if m else '',
                'url': SITE + a.group(1),
            })
        return out

    # ------------------------------------------------------------------ 首页/分类
    def homeContent(self, filter):
        return {
            'class': [{'type_id': u, 'type_name': n} for n, u in CLASSES],
            'filters': {},
        }

    def homeVideoContent(self):
        return {'list': self._list_of('/movie/new', 1)}

    def _cat_url(self, tid, pg):
        cls = tid or '/movie/new'
        if cls.startswith('/actor/'):
            if pg <= 1:
                return SITE + cls
            return SITE + re.sub(r'-\d+\.html$', '-%d.html' % pg, cls)
        if pg <= 1:
            return SITE + cls
        return SITE + cls.rstrip('/') + '/%d-2-1/' % pg

    def _list_of(self, tid, pg):
        html = self._page(self._cat_url(tid, pg))
        if 'actor' in (tid or '') and '/actor/list/' in (tid or ''):
            cards = self._actor_cards(html)
        else:
            cards = self._cards(html)
        return [{
            'vod_id': c['url'],
            'vod_name': c['title'],
            'vod_pic': c['img'],
            'vod_remarks': c['desc'],
        } for c in cards]

    def categoryContent(self, tid, pg, filter, extend):
        try:
            pg = int(pg or 1)
        except Exception:
            pg = 1
        data = self._list_of(tid, pg)
        return {
            'list': data,
            'page': pg,
            'pagecount': 999,
            'limit': len(data) or 60,
            'total': 9999,
        }

    # ------------------------------------------------------------------ 搜索
    def searchContent(self, key, quick, pg='1'):
        kw = (key or '').strip()
        if not kw:
            return {'list': []}
        html = self._page(SITE + '/search/' + urllib.parse.quote(kw))
        cards = self._cards(html)[:40]
        return {'list': [{
            'vod_id': c['url'],
            'vod_name': c['title'],
            'vod_pic': c['img'],
            'vod_remarks': c['desc'],
        } for c in cards]}

    # ------------------------------------------------------------------ 详情
    def _embeds(self, html):
        out = []
        if not html:
            return out
        for m in re.finditer(r'"embedUrl"\s*:\s*"([^"]+)"', html):
            u = self._norm(m.group(1))
            if u and u not in out:
                out.append(u)
        for m in re.finditer(r'<iframe[^>]+src="([^"]+)"', html):
            u = self._norm(m.group(1))
            if u and u not in out:
                out.append(u)
        return out

    def _srcs_of(self, page_html):
        out = []
        if not page_html:
            return out
        for pat in SRC_PATTERNS:
            m = pat.search(page_html)
            if not m:
                continue
            u = self._norm(m.group(1))
            if not u or u in out:
                continue
            if not any(k in u for k in ('m3u8', 'mp4', 'playlist', 'index')):
                continue
            out.append(u)
        return out

    def _resolve_source(self, detail_url):
        """从详情页一路挖到真实播放地址（每次都重新取，签名最新）"""
        html = self._page(detail_url)
        if not html:
            return '', '', ''
        poster = ''
        m = (re.search(r'property="og:image"[^>]+content="([^"]+)"', html) or
             re.search(r'content="([^"]+)"[^>]+property="og:image"', html))
        if m:
            poster = self._norm(m.group(1))
        src = ''
        direct = self._srcs_of(html)
        if direct:
            src = direct[0]
        for e in ([] if src else self._embeds(html)[:4]):
            ep = self._page(e, fresh=True) if 'javrate.com' in e else self._raw(e)
            lst = self._srcs_of(ep)
            if lst:
                src = lst[0]
                break
        return src, poster, html

    def detailContent(self, array):
        ids = array
        if isinstance(ids, str):
            ids = [ids]
        did = (ids[0] if ids else '') or ''
        if did and not did.startswith('http'):
            did = SITE + '/movie/detail/' + did.replace('.html', '') + '.html'

        # 女优页：把她的作品列成播放列表
        if '/actor/detail/' in did:
            html = self._page(did, fresh=True)
            works = self._cards(html)
            name = ''
            m = re.search(r'<title>([^<]+)</title>', html or '')
            if m:
                name = _clean(m.group(1).split('|')[0])
            eps = ['%s$%s' % (w['title'].replace('$', ' ').replace('#', ' '), w['url'])
                   for w in works]
            return {'list': [{
                'vod_id': did,
                'vod_name': name or '女优作品',
                'vod_pic': works[0]['img'] if works else '',
                'vod_content': '共 %d 部作品' % len(works),
                'vod_play_from': '作品',
                'vod_play_url': '#'.join(eps),
            }]}

        html = self._page(did)
        poster = ''
        m = (re.search(r'property="og:image"[^>]+content="([^"]+)"', html or '') or
             re.search(r'content="([^"]+)"[^>]+property="og:image"', html or ''))
        if m:
            poster = self._norm(m.group(1))

        desc = ''
        m = re.search(r'name="description"[^>]+content="([^"]+)"', html or '')
        if m:
            desc = _clean(m.group(1))

        title = ''
        m = re.search(r'<title>([^<]+)</title>', html or '')
        if m:
            title = _clean(m.group(1).split('|')[0])

        actors = []
        for m in re.finditer(r'href="/actor/detail/[^"]+"[^>]*>([^<]+)<', html or ''):
            n = _clean(m.group(1))
            if n and n != '更多' and n not in actors:
                actors.append(n)
            if len(actors) >= 5:
                break

        stills = []
        for m in re.finditer(r'data-photo-url="([^"]+)"', html or ''):
            u = self._norm(m.group(1))
            if u and u not in stills:
                stills.append(u)
            if len(stills) >= 10:
                break

        src, _, _ = self._resolve_source(did)

        line_info = ''
        if src:
            info = self._analyze(src)
            if info:
                line_info = '%d段 / %s' % (info['segs'], self._fmt(info['dur']))
                if info['end'] and 0 < info['dur'] < 180:
                    line_info += ' ⚠️疑似试看'
                if not info['end']:
                    line_info += ' · 滚动源'
            else:
                line_info = 'm3u8'

        vod = {
            'vod_id': did,
            'vod_name': title or '影片',
            'vod_pic': poster,
            'vod_actor': ' / '.join(actors),
            'vod_content': desc or '暂无简介',
            'vod_remarks': line_info,
        }
        # 三条线路：id 统一给“详情页地址”，播放时现解析，签名永远新鲜
        vod['vod_play_from'] = '▶直连$$$▶清单代理$$$▶续签代理'
        vod['vod_play_url'] = '$$$'.join(['立即播放$' + did] * 3)
        if not src:
            vod['vod_remarks'] = '点击播放时再取地址'
        if stills:
            vod['vod_content'] = (vod['vod_content'] or '') + '\n\n剧照：\n' + '\n'.join(stills[:6])
        return {'list': [vod]}

    # ------------------------------------------------------------------ 播放
    def playerContent(self, flag, id, vipFlags=None):
        did = id or ''
        if did and not did.startswith('http'):
            did = SITE + '/movie/detail/' + did.replace('.html', '') + '.html'

        src, _, _ = self._resolve_source(did)
        if not src:
            return {'parse': 0, 'playUrl': '', 'url': '', 'header': ''}

        head = json.dumps({'User-Agent': UA, 'Referer': SITE + '/'})
        f = flag or ''

        if '清单' in f:
            url = self._proxy_base() + '&type=pl&u=%s&d=%s' % (_b64e(src), _b64e(did))
        elif '续签' in f:
            url = self._proxy_base() + '&type=rl&u=%s&d=%s' % (_b64e(src), _b64e(did))
        else:
            url = src

        return {'parse': 0, 'playUrl': url, 'url': url, 'header': head}

    # ------------------------------------------------------------------ 清单处理
    def _load_playlist(self, src):
        """取主清单→最高码率子清单，返回 (target, text)"""
        master = self._raw(src, headers={'Referer': SITE + '/'})
        if not master or '#EXTM3U' not in master:
            return src, ''
        if '#EXT-X-STREAM-INF' in master:
            best = None
            lines = master.split('\n')
            for i, ln in enumerate(lines):
                ln = ln.strip()
                if not ln.startswith('#EXT-X-STREAM-INF'):
                    continue
                m = re.search(r'BANDWIDTH=(\d+)', ln)
                bw = int(m.group(1)) if m else 0
                j = i + 1
                while j < len(lines) and not lines[j].strip():
                    j += 1
                if j >= len(lines):
                    break
                nx = lines[j].strip()
                if nx.startswith('#'):
                    continue
                if not best or bw > best[0]:
                    best = (bw, nx)
            if not best:
                return src, ''
            target = self._abs_q(src, best[1], src)
            pl = self._raw(target, headers={'Referer': SITE + '/'})
            if not pl or '#EXTM3U' not in pl:
                return src, ''
            return target, pl
        return src, master

    def _analyze(self, src):
        target, pl = self._load_playlist(src)
        if not pl:
            return None
        segs, dur, end = 0, 0.0, False
        for ln in pl.split('\n'):
            ln = ln.strip()
            if not ln:
                continue
            if ln.startswith('#EXTINF:'):
                m = re.search(r'#EXTINF:([0-9.]+)', ln)
                if m:
                    dur += float(m.group(1) or 0)
            elif ln.startswith('#EXT-X-ENDLIST'):
                end = True
            elif not ln.startswith('#'):
                segs += 1
        return {'segs': segs, 'dur': dur, 'end': end, 'target': target, 'pl': pl}

    @staticmethod
    def _fmt(s):
        s = int(round(s or 0))
        if s <= 0:
            return '时长未知'
        h, m, ss = s // 3600, (s % 3600) // 60, s % 60
        if h:
            return '%d小时%d分' % (h, m)
        if m:
            return '%d分%d秒' % (m, ss)
        return '%d秒' % ss

    def _seg_cache(self, src, did=''):
        """清单缓存 10 秒：续签的最小粒度，避免每个分片都去拉一次清单"""
        now = time.time()
        hit = self._pl_cache.get(src)
        if hit and now - hit[0] < 10:
            return hit[1]
        info = self._analyze(src)
        if (not info) and did:
            # 旧签名已失效：回到详情页→播放页重新取一条新地址
            fresh, _, _ = self._resolve_source(did)
            if fresh and fresh != src:
                info = self._analyze(fresh)
        if not info:
            return None
        self._pl_cache[src] = (now, info)
        return info

    def _proxy_base(self):
        return 'http://127.0.0.1:%d/proxy?do=py' % self.port

    def _rewrite_playlist(self, src, resign, did=''):
        """把清单里的地址全部绝对化；resign=True 时关键资源和分片都走本地代理重取"""
        info = self._seg_cache(src, did)
        if not info:
            return ''
        target, pl = info['target'], info['pl']
        # 滚动源（边播边长）没有稳定分片序号，走序号代理会错位，退回普通绝对化
        if resign and not info['end']:
            resign = False
        base = target[:target.rfind('/') + 1]
        out = []
        idx = 0
        uidx = 0
        for raw_ln in pl.split('\n'):
            ln = raw_ln.strip()
            if not ln:
                continue
            if ln.startswith('#'):
                m = re.search(r'URI="([^"]+)"', ln)
                if m:
                    real = self._abs_q(base, m.group(1), target)
                    if resign:
                        ln = ln.replace(m.group(1),
                                        self._proxy_base() + '&type=uri&i=%d&u=%s&d=%s' % (uidx, _b64e(src), _b64e(did)))
                    else:
                        ln = ln.replace(m.group(1), real)
                    uidx += 1
                out.append(ln)
            else:
                real = self._abs_q(base, ln, target)
                if resign:
                    out.append(self._proxy_base() + '&type=seg&i=%d&u=%s&d=%s' % (idx, _b64e(src), _b64e(did)))
                else:
                    out.append(real)
                idx += 1
        return '\n'.join(out)

    # ------------------------------------------------------------------ 代理
    @staticmethod
    def _pget(param, key, default=''):
        if not isinstance(param, dict):
            return default
        v = param.get(key)
        if isinstance(v, (list, tuple)):
            v = v[0] if v else default
        return v if v not in (None, '') else default

    def localProxy(self, param):
        typ = self._pget(param, 'type', '')
        try:
            if typ == 'pl':
                src = _b64d(self._pget(param, 'u'))
                did = _b64d(self._pget(param, 'd'))
                body = self._rewrite_playlist(src, resign=False, did=did)
                if body:
                    return [200, 'application/vnd.apple.mpegurl', body]
                return [404, 'text/plain', 'playlist empty']

            if typ == 'rl':
                src = _b64d(self._pget(param, 'u'))
                did = _b64d(self._pget(param, 'd'))
                body = self._rewrite_playlist(src, resign=True, did=did)
                if body:
                    return [200, 'application/vnd.apple.mpegurl', body]
                return [404, 'text/plain', 'playlist empty']

            if typ == 'seg':
                src = _b64d(self._pget(param, 'u'))
                did = _b64d(self._pget(param, 'd'))
                i = int(self._pget(param, 'i', '0') or 0)
                for attempt in (0, 1):
                    info = self._seg_cache(src, did)
                    if info:
                        target, pl = info['target'], info['pl']
                        base = target[:target.rfind('/') + 1]
                        urls = [ln.strip() for ln in pl.split('\n')
                                if ln.strip() and not ln.strip().startswith('#')]
                        if i < len(urls):
                            real = self._abs_q(base, urls[i], target)
                            data = self._raw(real, headers={'Referer': SITE + '/'}, binary=True)
                            if data:
                                return [200, 'video/mp2t', data]
                    # 签名过期或拉取失败：丢掉缓存，回源取一条新地址再试一次
                    self._pl_cache.pop(src, None)
                return [404, 'text/plain', 'segment failed']

            if typ == 'uri':
                src = _b64d(self._pget(param, 'u'))
                did = _b64d(self._pget(param, 'd'))
                i = int(self._pget(param, 'i', '0') or 0)
                info = self._seg_cache(src, did)
                if not info:
                    return [404, 'text/plain', 'playlist lost']
                target, pl = info['target'], info['pl']
                base = target[:target.rfind('/') + 1]
                uris = re.findall(r'URI="([^"]+)"', pl)
                if i >= len(uris):
                    return [404, 'text/plain', 'uri index out of range']
                real = self._abs_q(base, uris[i], target)
                data = self._raw(real, headers={'Referer': SITE + '/'}, binary=True)
                if not data:
                    self._pl_cache.pop(src, None)
                    return [404, 'text/plain', 'uri empty']
                return [200, 'application/octet-stream', data]

            if typ == 'u':
                real = _b64d(self._pget(param, 'u'))
                data = self._raw(real, headers={'Referer': SITE + '/'}, binary=True)
                if data:
                    return [200, 'application/octet-stream', data]
                return [404, 'text/plain', 'empty']
        except Exception as e:
            return [500, 'text/plain', str(e)]
        return [404, 'text/plain', 'unknown']
