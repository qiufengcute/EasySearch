from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout,
                              QHBoxLayout, QLineEdit, QPushButton, QLabel,
                              QScrollArea, QStackedWidget, QTableWidget,
                              QTableWidgetItem, QHeaderView, QComboBox,
                              QAbstractItemView, QMessageBox)
from PySide6.QtCore import (Qt, QTimer, QThread, Signal, QUrl, QByteArray, 
                              QBuffer, QLoggingCategory)
from urllib.parse import quote_plus
from PySide6.QtGui import QFont, QDesktopServices, QIcon
from urllib.parse import urlparse
from urllib.parse import urlunparse, parse_qsl, urlencode, unquote
import sys
import os
import json
import requests
import time
from datetime import datetime
from typing import Any, Optional
import base64


def get_source_path(relative_path: str) -> str:
    try:
        base_path = sys._MEIPASS  # type: ignore
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)


def icon_to_base64(icon: QIcon, size: tuple[int, int] = (32, 32)) -> str:
    """将QIcon转换为Base64字符串"""
    pixmap = icon.pixmap(*size)
    
    # 将QPixmap转换为Base64
    byte_array = QByteArray()
    buffer = QBuffer(byte_array)
    buffer.open(QBuffer.WriteOnly)
    pixmap.save(buffer, "PNG")  # 保存为PNG格式
    buffer.close()
    
    # 编码为Base64
    base64_data = base64.b64encode(byte_array.data()).decode('utf-8')
    return f"data:image/png;base64,{base64_data}"


def normalize_publish_date(value: Any) -> Optional[datetime]:
    """把各种 publish_date 格式归一化为 datetime。

    支持输入类型：
    - datetime -> 直接返回
    - int/float -> 当作时间戳（秒或毫秒）解析
    - str -> 支持 ISO 格式、"YYYY-MM-DD" 等，或数字字符串（秒/毫秒）
    解析失败则返回 None。
    """
    if value is None:
        return None
    # 已经是 datetime
    if isinstance(value, datetime):
        return value

    # 数字类型：秒或毫秒时间戳
    try:
        if isinstance(value, (int, float)):
            ts = float(value)
            # 如果是毫秒级（> 1e12）则除以1000
            if ts > 1e12:
                ts = ts / 1000.0
            return datetime.fromtimestamp(ts)
        # 字符串形式的数字时间戳
        if isinstance(value, str):
            s = value.strip()
            if not s:
                return None
            # 纯数字的字符串 -> 当作时间戳
            if s.isdigit():
                iv = int(s)
                ts = float(iv)
                if iv > 1e12:
                    ts = ts / 1000.0
                return datetime.fromtimestamp(ts)
            # 尝试 ISO 格式解析
            try:
                return datetime.fromisoformat(s)
            except Exception:
                pass
            # 常见日期格式 YYYY-MM-DD 或 YYYY/MM/DD
            for fmt in ("%Y-%m-%d", "%Y/%m/%d", "%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M:%S"):
                try:
                    return datetime.strptime(s, fmt)
                except Exception:
                    pass
    except Exception:
        return None
    return None


def canonicalize_url(url: Optional[str]) -> str:
    """规范化 URL，用于去重比较。

    - scheme 和 netloc 小写
    - 移除 fragment
    - 去掉常见跟踪参数（utm_*, fbclid, gclid）
    - 对 query 参数排序并重新编码
    - 规范化 path（去掉多余的尾部斜杠，保留根路径"/")
    返回一个可比较的字符串（空字符串表示无效或空输入）。
    """
    if not url:
        return ''
    try:
        up = urlparse(url)
    except Exception:
        return url or ''

    scheme = (up.scheme or 'http').lower()
    netloc = (up.netloc or '').lower()
    # 移除默认端口
    if netloc.endswith(':80') and scheme == 'http':
        netloc = netloc[:-3]
    if netloc.endswith(':443') and scheme == 'https':
        netloc = netloc[:-4]

    # 规范化 path
    path = unquote(up.path or '')
    if path != '/' and path.endswith('/'):
        path = path.rstrip('/')

    # 过滤 query 中的跟踪参数
    try:
        qsl = parse_qsl(up.query, keep_blank_values=True)
        filtered = [(k, v) for (k, v) in qsl if not (k.startswith('utm_') or k in ('fbclid', 'gclid'))]
        # 排序以便可比
        filtered.sort()
        query = urlencode(filtered, doseq=True)
    except Exception:
        query = ''

    # 不保留 fragment
    frag = ''

    try:
        new = urlunparse((scheme, netloc, path or '', '', query or '', frag))
        return new
    except Exception:
        return (up.geturl() if hasattr(up, 'geturl') else url) or ''


class ICONCacheManager:
    def __init__(self, max_size=500):
        self.cache = {}
        self.max_size = max_size

    def add_icon(self, url: str, icon_data: QIcon):
        self.cache[url] = {"icon":icon_data, "timestamp": time.time()}
        if len(self.cache) > self.max_size:
            # 删除最旧的图标
            oldest_url = min(self.cache.items(), key=lambda item: item[1]["timestamp"])[0]
            del self.cache[oldest_url]

    def get_icon(self, url: str) -> Optional[QIcon]:
        entry = self.cache.get(url)
        if entry:
            return entry["icon"]
        return None


class SearchAPIManager:
    def __init__(self):
        self.iconcache = ICONCacheManager()
        self.blacklist = ["csdn.net"]
        self.whitelist = []
        self.authoritative_sites = ["github.com", "stackoverflow.com"]
        self.search_engines = {}
        self.theme_mode = "light"
        # 尝试从磁盘加载已保存设置
        try:
            self.load_settings()
        except Exception:
            pass
    
    def calculate_weight(self, result):
        """计算搜索结果权重"""
        weight = 0.0
        
        # 获取域名
        domain = ""
        try:
            parsed_url = urlparse(result["url"])
            domain = parsed_url.netloc.lower()
        except:
            pass
        
        # 黑名单检查
        if any(blocked in domain for blocked in self.blacklist):
            return -999  # 直接删除
        
        # 白名单权重
        if any(allowed in domain for allowed in self.whitelist):
            weight += 1.5
        
        # 权威网站权重
        if any(auth in domain for auth in self.authoritative_sites):
            weight += 1.0
        
        # 时间权重：支持 publish_date 为 datetime、数字（秒/毫秒）或字符串
        publish_date = result.get("publish_date")
        try:
            # 尝试归一化为 datetime 对象（如果可能）
            pub_dt = normalize_publish_date(publish_date)
        except Exception:
            pub_dt = None

        if pub_dt:
            try:
                # 如果 publish_date 是时区感知的（aware），则让当前时间也为相同的 tz
                if getattr(pub_dt, 'tzinfo', None) is not None and pub_dt.tzinfo.utcoffset(pub_dt) is not None:
                    now = datetime.now(tz=pub_dt.tzinfo)
                else:
                    now = datetime.now()
                days_ago = (now - pub_dt).days
            except Exception:
                days_ago = None

            if days_ago is not None:
                if days_ago == 0:
                    weight += 0.5
                elif days_ago == 1:
                    weight += 0.4
                elif days_ago == 2:
                    weight += 0.3
                elif days_ago == 3:
                    weight += 0.2
                elif days_ago == 4:
                    weight += 0.1
                elif days_ago >= 30:
                    weight -= 0.5
        
        return weight
    
    def search(self, query):
        # 这个方法作为回退保留（以前的模拟搜索）。
        time.sleep(0.1)
        return []

    def get_settings_path(self):
        appdata = os.getenv('APPDATA') or os.path.expanduser('~')
        folder = os.path.join(appdata, 'EasySearch')
        os.makedirs(folder, exist_ok=True)
        return os.path.join(folder, 'settings.json')

    def load_settings(self):
        path = self.get_settings_path()
        if not os.path.exists(path):
            return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                data = json.load(f)
        except Exception:
            return

        # 黑名单
        try:
            if isinstance(data.get('blacklist'), list):
                self.blacklist = data.get('blacklist')
        except Exception:
            self.blacklist = ["csdn.net"]
        # 白名单
        try:
            if isinstance(data.get('whitelist'), list):
                self.whitelist = data.get('whitelist')
        except Exception:
            self.whitelist = []

        # 搜索引擎设置（合并已有默认），并支持新字段：results_path, json_title, json_url, json_snippet, json_publish_date
        se = data.get('search_engines') or {}
        if isinstance(se, dict):
            for k, v in se.items():
                try:
                    if k in self.search_engines and isinstance(v, dict):
                        # 更新已有的配置
                        self.search_engines[k].update({
                            'enabled': bool(v.get('enabled', self.search_engines[k].get('enabled', True))),
                            'api_url': v.get('api_url', self.search_engines[k].get('api_url', '')) or '',
                            'api_key': v.get('api_key', self.search_engines[k].get('api_key', '')) or '',
                            'results_path': v.get('results_path', self.search_engines[k].get('results_path', '')) or '',
                            'json_title': v.get('json_title', self.search_engines[k].get('json_title', 'title')),
                            'json_url': v.get('json_url', self.search_engines[k].get('json_url', '')),
                            'json_snippet': v.get('json_snippet', self.search_engines[k].get('json_snippet', '')),
                            'json_publish_date': v.get('json_publish_date', self.search_engines[k].get('json_publish_date', '')),
                            'json_keyheader': v.get('json_keyheader', self.search_engines[k].get('json_keyheader', ''))
                        })
                    else:
                        # 新的引擎配置
                        if isinstance(v, dict):
                            self.search_engines[k] = {
                                'enabled': bool(v.get('enabled', True)),
                                'api_url': v.get('api_url', '') or '',
                                'api_key': v.get('api_key', '') or '',
                                'results_path': v.get('results_path', '') or '',
                                'json_title': v.get('json_title', ''),
                                'json_url': v.get('json_url', ''),
                                'json_snippet': v.get('json_snippet', ''),
                                'json_publish_date': v.get('json_publish_date', ''),
                                'json_keyheader': v.get('json_keyheader', '')
                            }
                except Exception:
                    # 某项有错，跳过用默认
                    self.search_engines[k] = {
                        'enabled': True,
                        'api_url': '',
                        'api_key': '',
                        'results_path': '',
                        'json_title': 'title',
                        'json_url': 'url',
                        'json_snippet': 'snippet',
                        'json_publish_date': 'publish_date',
                        'json_keyheader': ''
                    }

        # 主题
        tm = data.get('theme_mode')
        if tm in ('light', 'dark', 'system'):
            self.theme_mode = tm

    def save_settings(self):
        path = self.get_settings_path()
        data = {
            'blacklist': list(self.blacklist),
            'whitelist': list(self.whitelist),
            'search_engines': self.search_engines,
            'theme_mode': self.theme_mode
        }
        try:
            with open(path, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception:
            # 保存失败时忽略（不影响主流程）
            pass

    def log_error(self, message: str) -> str:
        """把错误信息写入到 %APPDATA%/EasySearch/Logs 下，返回日志文件路径。"""
        try:
            appdata = os.getenv('APPDATA') or os.path.expanduser('~')
            folder = os.path.join(appdata, 'EasySearch', 'Logs')
            os.makedirs(folder, exist_ok=True)
            fname = datetime.now().strftime("%Y_%m_%d_%H_%M_%S_EasySearch_ErrorLog.log")
            path = os.path.join(folder, fname)
            with open(path, 'w', encoding='utf-8') as f:
                f.write(f"[{datetime.now().isoformat()}]\n")
                f.write(message)
                f.write('\n')
            return path
        except Exception:
            return ''


class SearchWorker(QThread):
    """在后台线程中运行搜索并通过信号返回结果"""
    results_ready = Signal(list)
    # 当后台搜索出现错误时发出，参数为错误描述字符串
    error_occurred = Signal(str)

    def __init__(self, api_manager, query, parent=None):
        super().__init__(parent)
        self.api_manager = api_manager
        self.query = query

    def run(self):
        # 对每个启用的搜索引擎按其配置的 URL 发起请求，谁先返回就先 emit
        engines = list(self.api_manager.search_engines.items())
        for name, cfg in engines:
            if not cfg.get('enabled'):
                continue
            api_url = cfg.get('api_url') or ''
            api_key = cfg.get('api_key', '')
            results_path = cfg.get('results_path', '') or ''
            # json 字段映射
            json_title_key = cfg.get('json_title', '')
            json_url_key = cfg.get('json_url', '')
            json_snippet_key = cfg.get('json_snippet', '')
            json_publish_key = cfg.get('json_publish_date', '')
            json_header_key = cfg.get('json_keyheader', '')
            if not api_url:
                continue
            # 构建请求 URL：支持包含 {query} 和 {apikey} 占位符
            # 构建请求 URL：支持包含 {query} 和 {apikey} 占位符
            try:
                req_url = api_url
                # 支持多种占位符，避免只识别 {query} 导致重复追加参数
                query_placeholders = ['{query}', '{q}', '{keyword}', '{search}']
                apikey_placeholders = ['{apikey}', '{api_key}', '{key}']

                replaced_query = False
                for ph in query_placeholders:
                    if ph in req_url:
                        req_url = req_url.replace(ph, quote_plus(self.query))
                        replaced_query = True

                for ph in apikey_placeholders:
                    if ph in req_url:
                        req_url = req_url.replace(ph, quote_plus(api_key))

                # 如果没有任何占位符被替换，且 URL 查询串中也没有 q/keyword/query/search 等参数，则再追加参数
                if not replaced_query:
                    parsed = urlparse(req_url)
                    existing_q = (parsed.query or '').lower()
                    if not any(k in existing_q for k in ('q=', 'keyword=', 'query=', 'search=')):
                        sep = '&' if '?' in req_url else '?'
                        req_url = f"{req_url}{sep}q={quote_plus(self.query)}"

                # 设置请求头API Key（如果配置了 header key）
                header = {}
                if json_header_key:
                    header = {json_header_key: api_key}

                try:
                    resp = requests.get(req_url, timeout=(15,20), headers=header)
                except Exception as e:
                    # 网络或请求错误 -> 发出错误信号并继续下一个引擎
                    try:
                        self.error_occurred.emit(f"引擎 {name} 请求失败: {repr(e)}")
                    except Exception:
                        pass
                    continue

                # 试着解析 JSON
                results = []
                j = None
                try:
                    j = resp.json()
                except Exception:
                    j = None

                # 如果配置了 results_path，则按路径取值（支持 .a.b 语法）
                def _get_by_path(obj, path):
                    if not path:
                        return obj
                    if path == '.' or path == '':
                        return obj
                    # 去掉开头的点
                    if path.startswith('.'):
                        path = path[1:]
                    parts = [p for p in path.split('.') if p]
                    cur = obj
                    try:
                        for p in parts:
                            if isinstance(cur, dict):
                                cur = cur.get(p)
                            elif isinstance(cur, list):
                                # 不支持数字索引的复杂情况，返回空
                                return None
                            else:
                                return None
                        return cur
                    except Exception:
                        return None

                items = []
                if j is not None:
                    if results_path:
                        val = _get_by_path(j, results_path)
                        if isinstance(val, list):
                            items = val
                        elif isinstance(val, dict):
                            items = [val]
                        else:
                            items = []
                    else:
                        # 兼容常见返回格式
                        if isinstance(j, dict):
                            if 'results' in j and isinstance(j['results'], list):
                                items = j['results']
                            elif 'items' in j and isinstance(j['items'], list):
                                items = j['items']
                            else:
                                items = [j]
                        elif isinstance(j, list):
                            items = j
                        else:
                            items = []
                else:
                    items = []

                for it in items:
                    # 规范化字段并支持按配置的 json key 提取
                    title = ''
                    url = ''
                    snippet = ''
                    publish_date = None
                    try:
                        if isinstance(it, dict):
                            title = it.get(json_title_key) or it.get('title') or ''
                            url = it.get(json_url_key) or it.get('url') or ''
                            snippet = it.get(json_snippet_key) or it.get('snippet') or ''
                            pd = it.get(json_publish_key) or it.get('publish_date')
                            if pd is not None:
                                try:
                                    publish_date = normalize_publish_date(pd)
                                except Exception:
                                    publish_date = None
                        else:
                            title = str(it)
                            snippet = str(it)
                            url = ''
                    except Exception as e:
                        # 如果解析单条记录出问题，记录并跳过该条
                        try:
                            self.error_occurred.emit(f"引擎 {name} 解析结果项出错: {repr(e)}")
                        except Exception:
                            pass
                        continue

                    # 只有 title 字段缺失或为空时才兜底
                    result_title = title if title else f"{name} result"
                    norm_url = canonicalize_url(url or '')
                    # 获取ICON
                    icon = self.api_manager.iconcache.get_icon(url)
                    if not icon:
                        icon_url = norm_url.split("/")[0] + "//" + norm_url.split("/")[2] + "/favicon.ico"
                        try:
                            icon_resp = requests.get(icon_url, timeout=(15,10))
                            if icon_resp.status_code == 200:
                                from PySide6.QtGui import QPixmap
                                from PySide6.QtCore import QByteArray
                                pixmap = QPixmap()
                                pixmap.loadFromData(QByteArray(icon_resp.content))
                                icon = QIcon(pixmap)
                                self.api_manager.iconcache.add_icon(url, icon)
                            else:
                                icon = None
                        except Exception:
                            icon = None
                    result = {'title': result_title, 'url': url or '', 'norm_url': norm_url, 'snippet': snippet or '', 'source': name, 'publish_date': publish_date, 'icon': icon}
                    # 计算权重
                    result['weight'] = self.api_manager.calculate_weight(result)
                    # 白名单标记
                    try:
                        domain = ''
                        if url:
                            domain = urlparse(url).netloc.lower()
                        result['is_whitelist'] = any(w in domain for w in self.api_manager.whitelist)
                    except Exception:
                        result['is_whitelist'] = False
                    results.append(result)

                # 发回该引擎的结果（可能为空）
                if results:
                    self.results_ready.emit(results)
            except Exception as e:
                # 发生未知错误，发出错误信号并继续
                try:
                    self.error_occurred.emit(f"引擎 {name} 未知错误: {repr(e)}")
                except Exception:
                    pass
                continue

    def stop(self):
        self.terminate()

class LoadingDots(QLabel):
    def __init__(self):
        super().__init__()
        self.setAlignment(Qt.AlignCenter)
        self.dots = 0
        self.timer = QTimer(self)
        self.setFixedSize(60, 30)
        self.hide()
        
        # 明确设置定时器属性并连接
        self.timer.setInterval(300)
        self.timer.setSingleShot(False)  # 确保是重复定时器
        
        # 使用不同的连接方式
        self.timer.timeout.connect(self.on_timeout)
        
        # 初始化完成
        
    def start_animation(self):
        self.show()
        self.dots = 0
        self.update_dots()
        
        # 确保定时器状态
        if self.timer.isActive():
            self.timer.stop()
            
        self.timer.start()
        
    def stop_animation(self):
        if self.timer.isActive():
            self.timer.stop()
        self.dots = 0
        self.update_dots()
        self.hide()
        
    def on_timeout(self):
        self.dots = (self.dots + 1) % 3
        self.update_dots()
    
    def update_dots(self):
        dots_text = []
        for i in range(3):
            if i == self.dots:
                dots_text.append("●")
            else:
                dots_text.append("○")
        text = "".join(dots_text)
        self.setText(text)
        # 更新显示

class SearchResultWidget(QWidget):
    def __init__(self, result_data, theme="light"):
        super().__init__()
        self.result_data = result_data
        self.theme = theme
        self.setup_ui()
        
    def setup_ui(self):
        layout = QVBoxLayout()
        layout.setContentsMargins(15, 10, 15, 10)
        layout.setSpacing(5)

        # 标题行
        title_layout = QHBoxLayout()

        # 图标（模拟）
        icon_label = QLabel("🔍")
        icon_label.setFixedSize(20, 20)
        title_layout.addWidget(icon_label)

        # 标题（蓝色） — 使用显式的 inline 样式并保存为实例属性
        self.title_label = QLabel()
        self.title_label.setText(f"<img src={icon_to_base64(self.result_data.get('icon')) if self.result_data.get('icon', None) else icon_to_base64(QIcon(get_source_path('defaulticon')))} width='32' height='32'> {str(self.result_data.get("title", ""))}")
        title_font = QFont()
        title_font.setPointSize(14)
        self.title_label.setFont(title_font)
        # 使用明确的 inline stylesheet 来确保颜色优先级高
        self.title_label.setStyleSheet("color: #00FFFF; font-size:14px; background: transparent;")
        title_layout.addWidget(self.title_label)
        title_layout.addStretch()
        layout.addLayout(title_layout)

        # URL和权重
        url_layout = QHBoxLayout()
        # URL（灰色） — 显式 inline 样式
        self.url_label = QLabel(str(self.result_data.get("url", "")))
        self.url_label.setStyleSheet("color: #767676; font-size:12px; background: transparent;")
        url_layout.addWidget(self.url_label)
        url_layout.addStretch()

        # 权重显示
        weight_label = QLabel(f"权重: {self.result_data.get('weight', 0.0):.1f}")
        weight_label.setStyleSheet("color: #666; font-size: 11px;")
        url_layout.addWidget(weight_label)

        layout.addLayout(url_layout)

        # 简介
        snippet_label = QLabel(str(self.result_data.get("snippet", "")))
        snippet_label.setStyleSheet("color: #545454; font-size: 13px;" if self.theme == "light" else "color: #bdc1c6; font-size: 13px;")
        snippet_label.setWordWrap(True)
        layout.addWidget(snippet_label)

        # 来源和时间
        info_layout = QHBoxLayout()

        # 来源
        source_label = QLabel(f"来源: {self.result_data.get('source', '')}")
        source_label.setStyleSheet("color: #767676; font-size: 11px;" if self.theme == "light" else "color: #9aa0a6; font-size: 11px;")
        info_layout.addWidget(source_label)

        info_layout.addStretch()

        # 更新时间
        publish_date = self.result_data.get("publish_date", None)
        time_text = "未知"
        if isinstance(publish_date, datetime):
            try:
                # 若 publish_date 是时区感知（aware），则用相同时区获取当前时间
                if getattr(publish_date, 'tzinfo', None) is not None and publish_date.tzinfo.utcoffset(publish_date) is not None:
                    now = datetime.now(tz=publish_date.tzinfo)
                else:
                    now = datetime.now()
                time_diff = now - publish_date
                if time_diff.days == 0:
                    time_text = "今天"
                elif time_diff.days == 1:
                    time_text = "昨天"
                elif time_diff.days < 7:
                    time_text = f"{time_diff.days}天前"
                else:
                    time_text = publish_date.strftime("%Y-%m-%d")
            except Exception:
                time_text = "未知"

        time_label = QLabel(f"更新时间: {time_text}")
        time_label.setStyleSheet("color: #767676; font-size: 11px;" if self.theme == "light" else "color: #9aa0a6; font-size: 11px;")
        info_layout.addWidget(time_label)

        # 白名单徽标
        if self.result_data.get('is_whitelist', False):
            badge = QLabel("白名单")
            badge.setStyleSheet("background: gold; color: black; border-radius: 4px; padding: 2px 8px; font-weight: bold; font-size: 11px;")
            info_layout.addWidget(badge)

        layout.addLayout(info_layout)

        self.setLayout(layout)
        self.update_theme()
        # 让整个 SearchResultWidget 可点击：子部件不接收鼠标，以便父 widget 接收点击
        for child in (icon_label, getattr(self, 'title_label', None), getattr(self, 'url_label', None), snippet_label, source_label, time_label, weight_label):
            try:
                if child is not None:
                    child.setAttribute(Qt.WA_TransparentForMouseEvents, True)
            except Exception:
                pass
        self.setCursor(Qt.PointingHandCursor)

    def mousePressEvent(self, event):
        # 在父 widget 接收点击时打开 URL
        url = str(self.result_data.get("url", ""))
        if url:
            try:
                QDesktopServices.openUrl(QUrl(url))
            except Exception:
                pass
        super().mousePressEvent(event)
        
    def update_theme(self):
        if self.theme == "light":
            self.setStyleSheet("""
                SearchResultWidget {
                    border: 1px solid #e0e0e0;
                    border-radius: 8px;
                    background-color: white;
                    margin: 5px 0px;
                }
                SearchResultWidget:hover {
                    border-color: #4285f4;
                }
            """)
        else:
            self.setStyleSheet("""
                SearchResultWidget {
                    border: 1px solid #5f6368;
                    border-radius: 8px;
                    background-color: #303134;
                    margin: 5px 0px;
                }
                SearchResultWidget:hover {
                    border-color: #8ab4f8;
                }
            """)

class SettingsWindow(QMainWindow):
    def __init__(self, api_manager, parent=None):
        super().__init__(parent)
        self.api_manager = api_manager
        self.current_nav_key = "basic"
        self.setup_ui()
        self.apply_theme_to_settings(api_manager.theme_mode)

    def setup_ui(self):
        self.setWindowTitle("设置 - EasySearch")
        self.setWindowIcon(QIcon(get_source_path("icon.ico")))
        self.setFixedSize(800, 600)
        
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QHBoxLayout(central_widget)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)
        
        # 左侧导航栏
        self.sidebar = QWidget()
        self.sidebar.setFixedWidth(200)
        sidebar_layout = QVBoxLayout(self.sidebar)
        sidebar_layout.setContentsMargins(0, 20, 0, 20)
        sidebar_layout.setSpacing(0)
        
        # 设置标题
        settings_title = QLabel("设置")
        settings_title.setObjectName("settings_title")
        settings_title.setStyleSheet("""
            QLabel#settings_title {
                font-size: 18px;
                font-weight: bold;
                padding: 15px 20px;
            }
        """)
        sidebar_layout.addWidget(settings_title)
        
        # 导航按钮
        self.nav_buttons = {}
        nav_items = [
            ("基础设置", "basic"),
            ("黑白名单", "blacklist"),
            ("搜索引擎API", "search_api"),
            ("关于", "about")
        ]
        
        for text, key in nav_items:
            btn = QPushButton(text)
            btn.setFixedHeight(45)
            btn.setObjectName("nav_button")
            btn.setProperty('nav_key', key)
            btn.clicked.connect(self.on_nav_click)
            sidebar_layout.addWidget(btn)
            self.nav_buttons[key] = btn
        
        sidebar_layout.addStretch()
        main_layout.addWidget(self.sidebar)
        
        # 右侧内容区域
        self.content_stack = QStackedWidget()
        self.content_stack.setObjectName("content_stack")
        
        # 创建各个设置页面
        self.basic_page = self.create_basic_page()
        self.blacklist_page = self.create_blacklist_page()
        self.search_api_page = self.create_search_api_page()
        self.about_page = self.create_about_page()
        
        self.content_stack.addWidget(self.basic_page)
        self.content_stack.addWidget(self.blacklist_page)
        self.content_stack.addWidget(self.search_api_page)
        self.content_stack.addWidget(self.about_page)
        
        main_layout.addWidget(self.content_stack)
        
        # 默认选中基础设置
        self.update_nav_style()
        
    def create_basic_page(self):
        widget = QWidget()
        layout = QVBoxLayout(widget)
        layout.setContentsMargins(30, 30, 30, 30)
        
        title = QLabel("基础设置")
        title.setObjectName("page_title")
        title.setStyleSheet("""
            QLabel#page_title {
                font-size: 24px;
                font-weight: bold;
                margin-bottom: 20px;
            }
        """)
        layout.addWidget(title)
        
        # 主题设置
        theme_label = QLabel("主题模式")
        theme_label.setObjectName("section_title")
        theme_label.setStyleSheet("""
            QLabel#section_title {
                font-size: 16px;
                font-weight: bold;
                margin-top: 20px;
            }
        """)
        layout.addWidget(theme_label)
        
        self.theme_combo = QComboBox()
        self.theme_combo.addItems(["浅色模式", "深色模式", "跟随系统"])
        # 设置当前主题
        if self.api_manager.theme_mode == "light":
            self.theme_combo.setCurrentText("浅色模式")
        elif self.api_manager.theme_mode == "dark":
            self.theme_combo.setCurrentText("深色模式")
        else:
            self.theme_combo.setCurrentText("跟随系统")
            
        self.theme_combo.setObjectName("theme_combo")
        self.theme_combo.currentTextChanged.connect(self.on_theme_changed)
        layout.addWidget(self.theme_combo)
        
        layout.addStretch()
        return widget
    
    def create_blacklist_page(self):
        widget = QWidget()
        layout = QVBoxLayout(widget)
        layout.setContentsMargins(30, 30, 30, 30)
        
        title = QLabel("黑白名单设置")
        title.setObjectName("page_title")
        layout.addWidget(title)
        
        # 黑名单表格
        blacklist_label = QLabel("黑名单 - 这些网站将不会出现在搜索结果中")
        blacklist_label.setObjectName("section_title")
        layout.addWidget(blacklist_label)
        
        self.blacklist_table = QTableWidget(0, 1)
        self.blacklist_table.setHorizontalHeaderLabels(["域名"])
        self.blacklist_table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.blacklist_table.setEditTriggers(QAbstractItemView.DoubleClicked | QAbstractItemView.EditKeyPressed)
        
        # 填充现有黑名单
        for domain in self.api_manager.blacklist:
            row = self.blacklist_table.rowCount()
            self.blacklist_table.insertRow(row)
            self.blacklist_table.setItem(row, 0, QTableWidgetItem(domain))
        
        # 添加和删除按钮
        blacklist_btn_layout = QHBoxLayout()
        add_blacklist_btn = QPushButton("+ 添加")
        delete_blacklist_btn = QPushButton("- 删除选中")
        add_blacklist_btn.clicked.connect(self.add_blacklist_item)
        delete_blacklist_btn.clicked.connect(self.delete_blacklist_item)
        
        blacklist_btn_layout.addWidget(add_blacklist_btn)
        blacklist_btn_layout.addWidget(delete_blacklist_btn)
        blacklist_btn_layout.addStretch()
        
        layout.addWidget(self.blacklist_table)
        layout.addLayout(blacklist_btn_layout)
        
        # 白名单表格
        whitelist_label = QLabel("白名单 - 这些网站的搜索结果会被优先显示")
        whitelist_label.setObjectName("section_title")
        layout.addWidget(whitelist_label)
        
        self.whitelist_table = QTableWidget(0, 1)
        self.whitelist_table.setHorizontalHeaderLabels(["域名"])
        self.whitelist_table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.whitelist_table.setEditTriggers(QAbstractItemView.DoubleClicked | QAbstractItemView.EditKeyPressed)
        
        # 填充现有白名单
        for domain in self.api_manager.whitelist:
            row = self.whitelist_table.rowCount()
            self.whitelist_table.insertRow(row)
            self.whitelist_table.setItem(row, 0, QTableWidgetItem(domain))
        
        # 添加和删除按钮
        whitelist_btn_layout = QHBoxLayout()
        add_whitelist_btn = QPushButton("+ 添加")
        delete_whitelist_btn = QPushButton("- 删除选中")
        add_whitelist_btn.clicked.connect(self.add_whitelist_item)
        delete_whitelist_btn.clicked.connect(self.delete_whitelist_item)
        
        whitelist_btn_layout.addWidget(add_whitelist_btn)
        whitelist_btn_layout.addWidget(delete_whitelist_btn)
        whitelist_btn_layout.addStretch()
        
        layout.addWidget(self.whitelist_table)
        layout.addLayout(whitelist_btn_layout)
        
        # 自动保存：响应表格变化即可，不再需要保存按钮
        # 连接表格变化信号（注意在填充完成后再启用）
        self.blacklist_table.blockSignals(True)
        self.whitelist_table.blockSignals(True)
        self.blacklist_table.itemChanged.connect(self.on_blacklist_table_changed)
        self.whitelist_table.itemChanged.connect(self.on_whitelist_table_changed)
        self.blacklist_table.blockSignals(False)
        self.whitelist_table.blockSignals(False)
        
        layout.addStretch()
        return widget
    
    def create_search_api_page(self):
        widget = QWidget()
        layout = QVBoxLayout(widget)
        layout.setContentsMargins(30, 30, 30, 30)

        title = QLabel("搜索引擎API设置")
        title.setObjectName("page_title")
        layout.addWidget(title)

        info = QLabel("配置您喜欢的搜索引擎API密钥和URL（APIURL需包含{query}占位符 可选{apikey}占位符）")
        layout.addWidget(info)

        # API表格（名称、APIURL、APIKEY、结果路径、title、url、snippet、publish_date、APIKEY头名）
        self.api_table = QTableWidget(len(self.api_manager.search_engines), 9)
        self.api_table.setHorizontalHeaderLabels(["名称", "APIURL", "APIKEY", "结果列表路径", "title键", "url键", "snippet键", "publish_date键", "APIKEY头名"])
        self.api_table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.api_table.setEditTriggers(QAbstractItemView.AllEditTriggers)

        # 填充数据
        for row, (engine, config) in enumerate(self.api_manager.search_engines.items()):
            name_item = QTableWidgetItem(engine)
            apiurl_item = QTableWidgetItem(config.get("api_url", ""))
            apikey_item = QTableWidgetItem(config.get("api_key", ""))
            results_path_item = QTableWidgetItem(config.get('results_path', ''))
            json_title_item = QTableWidgetItem(config.get('json_title', ''))
            json_url_item = QTableWidgetItem(config.get('json_url', ''))
            json_snippet_item = QTableWidgetItem(config.get('json_snippet', ''))
            json_publish_item = QTableWidgetItem(config.get('json_publish_date', ''))
            json_keyheader_item = QTableWidgetItem(config.get('json_keyheader', ''))
            self.api_table.setItem(row, 0, name_item)
            self.api_table.setItem(row, 1, apiurl_item)
            self.api_table.setItem(row, 2, apikey_item)
            self.api_table.setItem(row, 3, results_path_item)
            self.api_table.setItem(row, 4, json_title_item)
            self.api_table.setItem(row, 5, json_url_item)
            self.api_table.setItem(row, 6, json_snippet_item)
            self.api_table.setItem(row, 7, json_publish_item)
            self.api_table.setItem(row, 8, json_keyheader_item)

        layout.addWidget(self.api_table)

        # 添加和删除按钮
        api_btn_layout = QHBoxLayout()
        add_api_btn = QPushButton("+ 添加")
        delete_api_btn = QPushButton("- 删除选中")
        add_api_btn.clicked.connect(self.add_api_item)
        delete_api_btn.clicked.connect(self.delete_api_item)
        api_btn_layout.addWidget(add_api_btn)
        api_btn_layout.addWidget(delete_api_btn)
        api_btn_layout.addStretch()
        layout.addLayout(api_btn_layout)

        # 自动保存：响应表格变化，不需要保存按钮
        self.api_table.blockSignals(True)
        self.api_table.itemChanged.connect(self.on_api_table_changed)
        self.api_table.blockSignals(False)

        layout.addStretch()
        return widget

    def add_api_item(self):
        row = self.api_table.rowCount()
        self.api_table.insertRow(row)
        name_item = QTableWidgetItem("")
        apiurl_item = QTableWidgetItem("")
        apikey_item = QTableWidgetItem("")
        results_path_item = QTableWidgetItem("")
        json_title_item = QTableWidgetItem("title")
        json_url_item = QTableWidgetItem("url")
        json_snippet_item = QTableWidgetItem("snippet")
        json_publish_item = QTableWidgetItem("publish_date")
        json_keyheader_item = QTableWidgetItem("")
        self.api_table.setItem(row, 0, name_item)
        self.api_table.setItem(row, 1, apiurl_item)
        self.api_table.setItem(row, 2, apikey_item)
        self.api_table.setItem(row, 3, results_path_item)
        self.api_table.setItem(row, 4, json_title_item)
        self.api_table.setItem(row, 5, json_url_item)
        self.api_table.setItem(row, 6, json_snippet_item)
        self.api_table.setItem(row, 7, json_publish_item)
        self.api_table.setItem(row, 8, json_keyheader_item)
        self.on_api_table_changed()

    def delete_api_item(self):
        current_row = self.api_table.currentRow()
        if current_row >= 0:
            self.api_table.removeRow(current_row)
            self.on_api_table_changed()
    
    def create_about_page(self):
        widget = QWidget()
        layout = QVBoxLayout(widget)
        layout.setContentsMargins(30, 30, 30, 30)
        
        title = QLabel("关于 EasySearch")
        title.setObjectName("page_title")
        layout.addWidget(title)
        
        about_text = QLabel("""
        <h3>EasySearch 简易搜索</h3>
        <p>一个简洁高效的本地搜索引擎工具</p>
        <br>
        <p><b>版本:</b> 1.0.0</p>
        <p><b>开发者:</b> Qiufeng</p>
        <p><b>许可证:</b> MIT</p>
        <br>
        <p>专注于提供干净、无干扰的搜索体验，</p>
        <p>支持多搜索引擎聚合和智能过滤。</p>
        """)
        about_text.setWordWrap(True)
        layout.addWidget(about_text)
        
        layout.addStretch()
        return widget
    
    def add_blacklist_item(self):
        row = self.blacklist_table.rowCount()
        self.blacklist_table.insertRow(row)
        self.blacklist_table.setItem(row, 0, QTableWidgetItem(""))
        # 自动保存
        self.on_blacklist_table_changed()
        
    def delete_blacklist_item(self):
        current_row = self.blacklist_table.currentRow()
        if current_row >= 0:
            self.blacklist_table.removeRow(current_row)
            # 自动保存
            self.on_blacklist_table_changed()
    
    def add_whitelist_item(self):
        row = self.whitelist_table.rowCount()
        self.whitelist_table.insertRow(row)
        self.whitelist_table.setItem(row, 0, QTableWidgetItem(""))
        # 自动保存
        self.on_whitelist_table_changed()
    
    def delete_whitelist_item(self):
        current_row = self.whitelist_table.currentRow()
        if current_row >= 0:
            self.whitelist_table.removeRow(current_row)
            # 自动保存
            self.on_whitelist_table_changed()

    def on_blacklist_table_changed(self):
        # 从表格重建黑名单并保存
        new_list = []
        for row in range(self.blacklist_table.rowCount()):
            item = self.blacklist_table.item(row, 0)
            if item and item.text().strip():
                new_list.append(item.text().strip())
        self.api_manager.blacklist = new_list
        try:
            self.api_manager.save_settings()
        except Exception:
            pass

    def on_whitelist_table_changed(self):
        new_list = []
        for row in range(self.whitelist_table.rowCount()):
            item = self.whitelist_table.item(row, 0)
            if item and item.text().strip():
                new_list.append(item.text().strip())
        self.api_manager.whitelist = new_list
        try:
            self.api_manager.save_settings()
        except Exception:
            pass

    def on_api_table_changed(self):
        # 从 api_table 重建 search_engines 配置并保存
        se = {}
        for row in range(self.api_table.rowCount()):
            engine_item = self.api_table.item(row, 0)
            api_url_item = self.api_table.item(row, 1)
            api_key_item = self.api_table.item(row, 2)
            results_path_item = self.api_table.item(row, 3)
            json_title_item = self.api_table.item(row, 4)
            json_url_item = self.api_table.item(row, 5)
            json_snippet_item = self.api_table.item(row, 6)
            json_publish_item = self.api_table.item(row, 7)
            json_keyheader_item = self.api_table.item(row, 8)
            if not engine_item:
                continue
            engine = engine_item.text()
            api_url = api_url_item.text() if api_url_item else ''
            api_key = api_key_item.text() if api_key_item else ''
            results_path = results_path_item.text() if results_path_item else ''
            json_title = json_title_item.text() if json_title_item else 'title'
            json_url = json_url_item.text() if json_url_item else 'url'
            json_snippet = json_snippet_item.text() if json_snippet_item else 'snippet'
            json_publish = json_publish_item.text() if json_publish_item else 'publish_date'
            json_keyheader = json_keyheader_item.text() if json_keyheader_item else ''
            se[engine] = {
                'enabled': True,
                'api_url': api_url,
                'api_key': api_key,
                'results_path': results_path,
                'json_title': json_title,
                'json_url': json_url,
                'json_snippet': json_snippet,
                'json_publish_date': json_publish,
                'json_keyheader': json_keyheader
            }

        # 覆盖并保存
        self.api_manager.search_engines = se
        try:
            self.api_manager.save_settings()
        except Exception:
            pass

    def _cleanup_worker(self, worker):
        """在线程结束时清理 worker 对象，确保不会提前销毁仍在运行的线程。"""
        try:
            # 等待线程完全结束（已结束则立即返回）
            worker.wait(1000)
        except Exception:
            pass
        try:
            if worker in self._workers:
                self._workers.remove(worker)
        except Exception:
            pass
        try:
            worker.deleteLater()
        except Exception:
            pass
    
    def save_blackwhite_list(self):
        # 已改为自动保存，不再使用此方法
        pass
    
    def save_api_settings(self):
        # 已改为自动保存，不再使用此方法
        pass
    
    def on_nav_click(self):
        button = self.sender()
        new_nav_key = button.property('nav_key')
        
        if new_nav_key != self.current_nav_key:
            self.current_nav_key = new_nav_key
            self.update_nav_style()
            
            page_index = {
                "basic": 0, "blacklist": 1, "search_api": 2, "about": 3
            }[new_nav_key]
            self.content_stack.setCurrentIndex(page_index)
    
    def update_nav_style(self):
        for key, btn in self.nav_buttons.items():
            if key == self.current_nav_key:
                btn.setStyleSheet("""
                    QPushButton {
                        text-align: left;
                        padding: 12px 20px;
                        border: none;
                        background-color: #1a73e8;
                        color: white;
                        font-size: 14px;
                        border-radius: 0px;
                    }
                """)
            else:
                btn.setStyleSheet("""
                    QPushButton {
                        text-align: left;
                        padding: 12px 20px;
                        border: none;
                        background-color: transparent;
                        color: #666;
                        font-size: 14px;
                        border-radius: 0px;
                    }
                    QPushButton:hover {
                        background-color: #e8f0fe;
                        color: #1a73e8;
                    }
                """)
    
    def on_theme_changed(self, theme_text):
        if theme_text == "浅色模式":
            theme = "light"
        elif theme_text == "深色模式":
            theme = "dark"
        else:  # 跟随系统
            theme = "system"
        self.api_manager.theme_mode = theme_text if theme_text in ["浅色模式", "深色模式", "跟随系统"] else theme
        if self.parent():
            self.parent().apply_theme(theme)
        self.apply_theme_to_settings(theme)
        # 主题更改后自动保存设置
        try:
            self.api_manager.save_settings()
        except Exception:
            pass
    
    def apply_theme_to_settings(self, theme):
        if theme == "light":
            self.setStyleSheet("""
                QMainWindow {
                    background-color: white;
                }
                QWidget#sidebar {
                    background-color: #f8f9fa;
                    border-right: 1px solid #e0e0e0;
                }
                QLabel#settings_title {
                    color: #333;
                }
                QLabel#page_title, QLabel#section_title {
                    color: #333;
                }
                QStackedWidget#content_stack {
                    background-color: white;
                }
                QTableWidget {
                    background-color: white;
                    color: black;
                }
            """)
        else:
            self.setStyleSheet("""
                QMainWindow {
                    background-color: #202124;
                }
                QWidget#sidebar {
                    background-color: #303134;
                    border-right: 1px solid #5f6368;
                }
                QLabel#settings_title {
                    color: #e8eaed;
                }
                QLabel#page_title, QLabel#section_title {
                    color: #e8eaed;
                }
                QStackedWidget#content_stack {
                    background-color: #303134;
                }
                QTableWidget {
                    background-color: #303134;
                    color: #e8eaed;
                }
            """)
        # 刷新API表格启用列样式
        if hasattr(self, 'api_table'):
            for row in range(self.api_table.rowCount()):
                enabled_item = self.api_table.item(row, 3)
                if enabled_item:
                    if theme == "dark":
                        enabled_item.setBackground(Qt.black)
                        enabled_item.setForeground(Qt.white)
                    else:
                        enabled_item.setBackground(Qt.white)
                        enabled_item.setForeground(Qt.black)

class EasySearchWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.api_manager = SearchAPIManager()
        self.search_results = []
        self.current_page = 0
        self.results_per_page = 10
        self._workers = []
        self.setup_ui()
        
    def setup_ui(self):
        self.setWindowTitle("EasySearch")
        self.setWindowIcon(QIcon(get_source_path("icon.ico")))
        self.setMinimumSize(1000, 700)
        
        # 创建中央部件
        self.central_widget = QWidget()
        self.setCentralWidget(self.central_widget)
        self.main_layout = QVBoxLayout(self.central_widget)
        self.main_layout.setContentsMargins(50, 30, 50, 20)
        self.main_layout.setSpacing(0)
        
        # 顶部搜索区域
        self.setup_top_area()
        
        # 主内容区域
        self.setup_content_area()
        
        # 底部区域
        self.setup_bottom_area()
        
        # 应用主题
        self.apply_theme(self.api_manager.theme_mode)
        
    def setup_top_area(self):
        # 顶部容器 - 始终居中上方
        self.top_container = QWidget()
        self.top_container.setFixedHeight(120)
        top_layout = QVBoxLayout(self.top_container)
        top_layout.setAlignment(Qt.AlignCenter)
        
        # Logo和标题
        self.logo_label = QLabel()
        self.logo_label.setText(f"<img src='{get_source_path('icon.ico')}' width='24' height='24'> EasySearch")
        self.logo_label.setStyleSheet("""
            QLabel {
                font-size: 36px;
                font-weight: bold;
                color: #4285f4;
                margin-bottom: 10px;
            }
        """)
        self.logo_label.setAlignment(Qt.AlignCenter)
        top_layout.addWidget(self.logo_label)
        
        # 搜索框区域
        search_layout = QHBoxLayout()
        search_layout.setAlignment(Qt.AlignCenter)
        
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("输入搜索内容...")
        self.search_input.setFixedSize(400, 40)
        self.search_input.setStyleSheet("""
            QLineEdit {
                border: 2px solid #dfe1e5;
                border-radius: 20px;
                padding: 0px 15px;
                font-size: 14px;
                background-color: white;
                color: black;
            }
            QLineEdit:focus {
                border-color: #4285f4;
            }
        """)
        self.search_input.returnPressed.connect(self.perform_search)
        
        self.search_btn = QPushButton("🔍")
        self.search_btn.setFixedSize(40, 40)
        self.search_btn.setStyleSheet("""
            QPushButton {
                background-color: #4285f4;
                border: none;
                border-radius: 20px;
                color: white;
                font-size: 16px;
            }
            QPushButton:hover {
                background-color: #3367d6;
            }
        """)
        self.search_btn.clicked.connect(self.perform_search)
        
        search_layout.addWidget(self.search_input)
        search_layout.addWidget(self.search_btn)
        
        top_layout.addLayout(search_layout)
        
        self.main_layout.addWidget(self.top_container)
        
        # 设置按钮
        self.settings_btn = QPushButton("⚙️")
        self.settings_btn.setFixedSize(40, 40)
        self.settings_btn.setStyleSheet("""
            QPushButton {
                background-color: transparent;
                border: 2px solid #dfe1e5;
                border-radius: 20px;
                font-size: 16px;
            }
            QPushButton:hover {
                background-color: #f8f9fa;
            }
        """)
        self.settings_btn.clicked.connect(self.open_settings)
        
        # 将设置按钮添加到窗口
        self.settings_btn.setParent(self.central_widget)
        
    def setup_content_area(self):
        # 搜索结果区域
        self.results_scroll = QScrollArea()
        self.results_scroll.setWidgetResizable(True)
        self.results_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.results_scroll.setStyleSheet("""
            QScrollArea {
                border: none;
                background-color: transparent;
            }
        """)
        
        self.results_container = QWidget()
        self.results_layout = QVBoxLayout(self.results_container)
        self.results_layout.setAlignment(Qt.AlignTop)
        self.results_layout.setSpacing(10)
        self.results_layout.setContentsMargins(0, 0, 0, 0)
        
        self.results_scroll.setWidget(self.results_container)
        self.main_layout.addWidget(self.results_scroll)
        
    def setup_bottom_area(self):
        self.bottom_container = QWidget()
        bottom_layout = QVBoxLayout(self.bottom_container)
        bottom_layout.setAlignment(Qt.AlignCenter)
        
        # 加载指示器（水平居中，位于分页控件上方）
        self.loading_dots = LoadingDots()
        self.loading_dots.setStyleSheet("font-size: 20px; color: #4285f4;")
        bottom_layout.addWidget(self.loading_dots, 0, Qt.AlignHCenter)
        
        # 分页控件
        self.pagination_container = QWidget()
        pagination_layout = QHBoxLayout(self.pagination_container)
        pagination_layout.setAlignment(Qt.AlignCenter)
        
        self.prev_btn = QPushButton("上一页")
        self.next_btn = QPushButton("下一页")
        
        for btn in [self.prev_btn, self.next_btn]:
            btn.setFixedSize(80, 35)
            btn.setStyleSheet("""
                QPushButton {
                    background-color: #f8f9fa;
                    border: 1px solid #dadce0;
                    border-radius: 4px;
                    padding: 8px 16px;
                    color: #3c4043;
                }
                QPushButton:hover {
                    background-color: #f1f3f4;
                }
                QPushButton:disabled {
                    color: #9aa0a6;
                }
            """)
        
        self.prev_btn.clicked.connect(self.prev_page)
        self.next_btn.clicked.connect(self.next_page)
        
        self.page_label = QLabel("第 1 页")
        self.page_label.setStyleSheet("color: #5f6368; margin: 0px 15px;")
        
        pagination_layout.addWidget(self.prev_btn)
        pagination_layout.addWidget(self.page_label)
        pagination_layout.addWidget(self.next_btn)
        
        bottom_layout.addWidget(self.pagination_container)
        self.pagination_container.hide()
        
        self.main_layout.addWidget(self.bottom_container)
        
    def resizeEvent(self, event):
        self.settings_btn.move(self.central_widget.width() - 60, 20)
        super().resizeEvent(event)
        
    def perform_search(self):
        query = self.search_input.text().strip()
        if not query:
            return
            
        self.clear_results()
        self.loading_dots.start_animation()
        self.pagination_container.hide()
        # 如果已有正在运行的 worker，尝试先停止（短等待）
        # 在后台线程运行搜索，注意不要在运行时销毁仍在运行的线程。
        worker = SearchWorker(self.api_manager, query, parent=None)
        self._workers.append(worker)
        # 信号用于接收结果（带上 worker 引用以便识别）
        worker.results_ready.connect(lambda results, w=worker: self.on_worker_results(results, w))
        # 连接错误信号以在主线程弹窗显示并写日志
        worker.error_occurred.connect(lambda msg, w=worker: self.on_worker_error(msg, w))
        # 线程结束时做清理，确保不会被销毁时仍在运行
        def _on_finished(w=worker):
            try:
                if w in self._workers:
                    self._workers.remove(w)
            except Exception:
                pass
            try:
                # 搜索全部完成后停止动画并显示分页
                try:
                    self.loading_dots.stop_animation()
                except Exception:
                    pass
                try:
                    self.pagination_container.show()
                except Exception:
                    pass
                # 如果有结果，显示第一页
                try:
                    if len(self.search_results) > 0:
                        self.show_results_page(0)
                except Exception:
                    pass
            except Exception:
                pass
            try:
                w.deleteLater()
            except Exception:
                pass
        worker.finished.connect(_on_finished)
        # 记住当前可取消引用的 worker（用于 UI 交互）
        self.search_worker = worker
        worker.start()

    def on_worker_results(self, results, worker):
        """当某个后台 worker 发回结果时调用（在主线程执行）。"""
        # 将新到达的结果追加并立即渲染（先到先渲染）
        # results 是一个列表
        if not isinstance(results, list):
            return
        # 先把已有结果的规范化 URL 收集好用于去重判断
        existing_urls = set()
        for r in self.search_results:
            nu = r.get('norm_url') if isinstance(r, dict) else ''
            if not nu:
                nu = canonicalize_url(r.get('url') if isinstance(r, dict) else None)
            if nu:
                existing_urls.add(nu)

        # 收集此次从单个引擎返回的非重复新结果
        new_results = []
        for r in results:
            nu = r.get('norm_url') if isinstance(r, dict) else ''
            if not nu:
                nu = canonicalize_url(r.get('url') if isinstance(r, dict) else None)
                try:
                    if isinstance(r, dict):
                        r['norm_url'] = nu
                except Exception:
                    pass

            # 如果有规范化 URL 并且已存在，则跳过
            if nu and nu in existing_urls:
                continue

            new_results.append(r)
            if nu:
                existing_urls.add(nu)

        # 合并所有新结果（一次性），然后排序并刷新页面/分页
        if new_results:
            self.search_results.extend(new_results)

            def _sort_key(item):
                w = item.get('weight', 0.0)
                pub = item.get('publish_date')
                ts = 0.0
                if isinstance(pub, datetime):
                    try:
                        ts = pub.timestamp()
                    except Exception:
                        ts = 0.0
                return (w, ts)

            # 按权重和发布时间排序（降序）
            self.search_results.sort(key=_sort_key, reverse=True)

            # 刷新当前页面并显示分页控件
            try:
                self.show_results_page(self.current_page)
            except Exception:
                pass
            try:
                self.pagination_container.show()
            except Exception:
                pass
        if getattr(self, 'search_worker', None) is worker:
            self.search_worker = None

    def on_worker_error(self, message: str, worker):
        """在主线程显示错误弹窗并把错误保存到日志。"""
        try:
            log_path = self.api_manager.log_error(message)
        except Exception:
            log_path = ''

        # 简单分类常见错误
        lower = message.lower()
        if 'timed out' in lower or 'timeout' in lower:
            user_msg = '请求超时：可能是网络或 API 不可用。'
        elif 'connectionerror' in lower or 'connection' in lower or '无法连接' in message:
            user_msg = '无法连接到服务器：请检查网络或 API 地址。'
        elif '401' in lower or '403' in lower or 'unauthorized' in lower:
            user_msg = '鉴权失败：请检查 API Key 或权限。'
        else:
            user_msg = f'发生错误：{message}'

        if log_path:
            user_msg += f"\n\n错误日志已保存至：{log_path}"

        try:
            QMessageBox.critical(self, '搜索错误', user_msg)
        except Exception:
            pass
        # 出错时立即停止动画并显示分页（便于用户查看错误与已有结果）
        try:
            self.loading_dots.stop_animation()
        except Exception:
            pass
        try:
            self.pagination_container.show()
        except Exception:
            pass
        
    def open_settings(self):
        self.settings_window = SettingsWindow(self.api_manager, self)
        self.settings_window.show()
        
    def clear_results(self):
        for i in reversed(range(self.results_layout.count())):
            widget = self.results_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
                
    def show_results_page(self, page):
        self.current_page = page
        self.clear_results()
        
        start_idx = page * self.results_per_page
        end_idx = start_idx + self.results_per_page
        page_results = self.search_results[start_idx:end_idx]
        
        for result in page_results:
            result_widget = SearchResultWidget(result, self.api_manager.theme_mode)
            self.results_layout.addWidget(result_widget)
            
        total_pages = (len(self.search_results) + self.results_per_page - 1) // self.results_per_page
        self.page_label.setText(f"第 {page + 1} 页 / 共 {total_pages} 页")
        self.prev_btn.setEnabled(page > 0)
        self.next_btn.setEnabled(page < total_pages - 1)

    def add_results(self, results):
        """Append and render result objects without clearing existing widgets."""
        for result in results:
            try:
                result_widget = SearchResultWidget(result, self.api_manager.theme_mode)
                self.results_layout.addWidget(result_widget)
            except Exception as e:
                # 渲染异常也弹窗并写日志
                log_path = self.api_manager.log_error(f"渲染结果异常: {repr(e)}\n数据: {result}")
                msg = f"渲染结果时发生错误：{e}\n\n错误日志已保存至：{log_path}"
                try:
                    QMessageBox.critical(self, '渲染错误', msg)
                except Exception:
                    pass
        # 更新分页标签
        total_pages = (len(self.search_results) + self.results_per_page - 1) // self.results_per_page
        current_page = (len(self.search_results)-1) // self.results_per_page if len(self.search_results)>0 else 0
        self.page_label.setText(f"第 {current_page + 1} 页 / 共 {total_pages} 页")
        self.prev_btn.setEnabled(current_page > 0)
        self.next_btn.setEnabled(current_page < total_pages - 1)
        
    def prev_page(self):
        if self.current_page > 0:
            self.show_results_page(self.current_page - 1)
            
    def next_page(self):
        total_pages = (len(self.search_results) + self.results_per_page - 1) // self.results_per_page
        if self.current_page < total_pages - 1:
            self.show_results_page(self.current_page + 1)
            
    def apply_theme(self, theme):
        self.api_manager.theme_mode = theme
        if theme == "light":
            self.setStyleSheet("""
        total_results = len(self.search_results)
        total_pages = (total_results + self.results_per_page - 1) // self.results_per_page
        # 页码边界修正
        if page < 0:
            page = 0
        if page >= total_pages:
            page = total_pages - 1 if total_pages > 0 else 0
        self.current_page = page
        self.clear_results()
        start_idx = page * self.results_per_page
        end_idx = min(start_idx + self.results_per_page, total_results)
        page_results = self.search_results[start_idx:end_idx]
        for result in page_results:
            result_widget = SearchResultWidget(result, self.api_manager.theme_mode)
            self.results_layout.addWidget(result_widget)
        self.page_label.setText(f"第 {page + 1} 页 / 共 {total_pages} 页")
        self.prev_btn.setEnabled(page > 0)
        self.next_btn.setEnabled(page < total_pages - 1)
                QPushButton:hover {
                    background-color: #f8f9fa;
                }
            """)
        else:
            self.setStyleSheet("""
                QMainWindow, QWidget {
                    background-color: #202124;
                    color: #e8eaed;
                }
            """)
            self.settings_btn.setStyleSheet("""
                QPushButton {
                    background-color: transparent;
                    border: 2px solid #5f6368;
                    border-radius: 20px;
                    font-size: 16px;
                    color: #e8eaed;
                }
                QPushButton:hover {
                    background-color: #303134;
                }
            """)
        
        for i in range(self.results_layout.count()):
            widget = self.results_layout.itemAt(i).widget()
            if isinstance(widget, SearchResultWidget):
                widget.theme = theme
                widget.update_theme()
    
    def closeEvent(self, event):
        # 关闭窗口时尝试停止所有后台线程
        for worker in self._workers:
            try:
                worker.stop()
            except Exception:
                pass
        super().closeEvent(event)

if __name__ == "__main__":
    app = QApplication(sys.argv)
    QLoggingCategory.setFilterRules("""
qt.text.font.db.warning=false
qt.text.font.db.debug=false
qt.text.font.db.info=false
""")
    
    window = EasySearchWindow()
    window.show()
    
    sys.exit(app.exec())
