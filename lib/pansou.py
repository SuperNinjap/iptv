# coding=utf-8
#!/usr/bin/python
import sys
import json
import requests
import time
import re
from datetime import datetime
from typing import Optional, Dict, Any, List

sys.path.append('..')
from base.spider import Spider

class Spider(Spider):
    PAN_CONFIG = {
        'ali': {'api_type': 'aliyun', 'name': '阿里', 'keywords': ['alipan.com', 'aliyundrive.com']},
        'quark': {'api_type': 'quark', 'name': '夸克', 'keywords': ['pan.quark.cn']},
        'uc': {'api_type': 'uc', 'name': 'UC', 'keywords': ['drive.uc.cn']},
        'xunlei': {'api_type': 'xunlei', 'name': '迅雷', 'keywords': ['xunlei', 'thunder']},
        'a123': {'api_type': '123', 'name': '123', 'keywords': ['123684.com', '123685.com', '123912.com', '123pan.com', '123pan.cn', '123592.com']},
        'a189': {'api_type': 'tianyi', 'name': '天翼', 'keywords': ['cloud.189.cn']},
        'a139': {'api_type': 'mobile', 'name': '移动', 'keywords': ['caiyun.139.com']},
        'a115': {'api_type': '115', 'name': '115', 'keywords': ['115cdn.com','115.com', 'anxia.com']}
    }
    
    PAN_NAMES = {k: v['name'] for k, v in PAN_CONFIG.items()}
    REVERSE_PAN_MAP = {v['api_type']: k for k, v in PAN_CONFIG.items()}
    URL_PAN_KEYWORDS = {k: v['keywords'] for k, v in PAN_CONFIG.items()}
    
    DEFAULT_BASE_URL = "https://so.252035.xyz"
    HEADERS = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
        "Content-Type": "application/json"
    }
    SEARCH_PAGE_SIZE = 100
    REQUEST_TIMEOUT = 30  # 增加请求超时时间

    def __init__(self):
        super().__init__()
        self.base_url = self.DEFAULT_BASE_URL
        self.proxy = ''
        self.pan_priority = ''
        self.tokens = {}
        self.session = requests.Session()
        self.session.headers.update(self.HEADERS)
        
    def getName(self):
        return "盘搜"

    def init(self, extend):
        try:
            extend_dict = json.loads(extend) if extend else {}
            self.base_url = extend_dict.get('server', self.DEFAULT_BASE_URL).strip('/')
            self.proxy = extend_dict.get('proxy', '')
            self.pan_priority = extend_dict.get('pan_priority', '')
            self.tokens = extend_dict.get('tokens', {})
        except (json.JSONDecodeError, TypeError):
            self.base_url = self.DEFAULT_BASE_URL
            self.proxy = ''
            self.pan_priority = ''
            self.tokens = {}
        
        if self.proxy:
            self.session.proxies = {"http": self.proxy, "https": self.proxy}

    def homeContent(self, filter):
        return {'class': [{"type_id": "1", "type_name": "盘搜|聚合搜索"}], 'list': []}

    def homeVideoContent(self):
        return {}

    def categoryContent(self, cid, page, filter, ext):
        return {
            'list': [{"vod_id": "1", "vod_name": "请在搜索框中输入关键词搜索", "vod_pic": "", "vod_remarks": "盘搜"}],
            'page': 1, 'pagecount': 1, 'limit': 1, 'total': 1
        }

    def detailContent(self, did):
        result = {'list': []}
        if not did or not did[0]:
            return result
        
        resource_url = did[0]
        pan_type = self._extract_pan_type_from_url(resource_url)
        pan_name = self.PAN_NAMES.get(pan_type, '网盘资源')
        
        result['list'].append({
            "vod_id": resource_url,
            "vod_name": f"{pan_name}资源",
            "vod_pic": "",
            "vod_play_from": "盘搜",
            "vod_play_url": f"盘搜${resource_url}",
            "vod_content": f"网盘类型: {pan_name}\n资源链接: {resource_url}"
        })
        return result

    def searchContent(self, key, quick, pg="1"):
        return self._perform_search(key, pg)

    def searchContentPage(self, key, quick, page):
        return self._perform_search(key, page)

    def _perform_search(self, keywords, page_str):
        try:
            page = int(page_str)
        except (ValueError, TypeError):
            page = 1
            
        result = {'list': [], 'page': page, 'pagecount': 1, 'limit': self.SEARCH_PAGE_SIZE, 'total': 0}

        if not keywords:
            return result
        
        try:
            # 发起搜索请求，增加超时时间
            search_response = self.session.post(
                f"{self.base_url}/api/search",
                json={"kw": keywords},
                timeout=self.REQUEST_TIMEOUT
            )
            search_response.raise_for_status()
            
            search_data = search_response.json()
            if search_data.get('code') != 0:
                return result
            
            # 解析搜索结果
            all_results = self._parse_and_sort_results(search_data)
            
            # 简单分页处理
            total_count = len(all_results)
            start_index = (page - 1) * self.SEARCH_PAGE_SIZE
            paged_results = all_results[start_index : start_index + self.SEARCH_PAGE_SIZE]
            
            result.update({
                'list': paged_results,
                'total': total_count,
                'pagecount': max(1, (total_count + self.SEARCH_PAGE_SIZE - 1) // self.SEARCH_PAGE_SIZE)
            })
            
        except Exception as e:
            # 记录错误信息（在实际使用中可以输出到日志）
            pass
        
        return result

    def _parse_and_sort_results(self, data):
        # 解析pan_priority参数，获取要显示的网盘类型
        enabled_pan_types = []
        if self.pan_priority:
            enabled_pan_types = [pan.strip() for pan in self.pan_priority.split(',') if pan.strip()]
        
        all_items = []
        merged_data = data.get('data', {}).get('merged_by_type', {})
        
        for cloud_type, items in merged_data.items():
            pan_type = self.REVERSE_PAN_MAP.get(cloud_type, cloud_type)
            
            # 如果设置了pan_priority，只显示指定的网盘类型
            if enabled_pan_types and pan_type not in enabled_pan_types:
                continue
                
            for item in items:
                url = item.get('url')
                if not url: 
                    continue

                pan_name = self.PAN_NAMES.get(pan_type, pan_type)
                
                dt_obj = self._to_datetime(item.get('datetime'))
                time_str = dt_obj.strftime("%m-%d %H:%M") if dt_obj else ""
                
                # 从搜索结果中获取source值
                source = item.get('source', '盘搜')
                remarks = f"{pan_name}|{time_str}|{source}"
                
                all_items.append({
                    "vod_id": url,
                    "vod_name": item.get('note', ''),
                    "vod_pic": "",
                    "vod_remarks": remarks,
                    "_timestamp": dt_obj.timestamp() if dt_obj else 0,
                    "_pan_type": pan_type
                })
        
        # 排序逻辑
        if enabled_pan_types:
            # 设置了pan_priority：先按pan_priority顺序，再按时间排序
            pan_priority_order = {pan: idx for idx, pan in enumerate(enabled_pan_types)}
            all_items.sort(key=lambda x: (
                pan_priority_order.get(x['_pan_type'], 999),
                -x['_timestamp']
            ))
        else:
            # 没有设置pan_priority：只按时间排序
            all_items.sort(key=lambda x: -x['_timestamp'])
        
        # 清理临时字段
        for item in all_items:
            item.pop('_timestamp', None)
            item.pop('_pan_type', None)
            
        return all_items

    def playerContent(self, flag, pid, vipFlags):
        result = {"parse": 0, "header": self.HEADERS, "url": ""}
        if not pid:
            return result
        
        if pid.startswith('push:'):
            result['url'] = pid
        else:
            url = pid.strip()
            if not url.startswith(('http://', 'https://')):
                url = 'https://' + url
            result['url'] = f"push:{url}"
            
        return result

    def _to_datetime(self, time_str):
        if not time_str or time_str == "0001-01-01T00:00:00Z":
            return None
        try:
            time_str_clean = time_str.replace('Z', '+00:00')
            return datetime.fromisoformat(time_str_clean)
        except (ValueError, TypeError):
            try:
                return datetime.strptime(time_str, '%Y-%m-%d %H:%M:%S')
            except (ValueError, TypeError):
                return None

    def _extract_pan_type_from_url(self, url):
        if not url:
            return "unknown"
        url_lower = url.lower()
        for pan_type, keywords in self.URL_PAN_KEYWORDS.items():
            if any(keyword in url_lower for keyword in keywords):
                return pan_type
        return "unknown"

    def localProxy(self, params): 
        pass
        
    def isVideoFormat(self, url): 
        pass
        
    def manualVideoCheck(self): 
        pass