#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
蓝奏云批量上传工具 (GUI)

依赖:
    pip install requests requests-toolbelt
    GUI 使用 Python 内置 tkinter，无需额外安装
    说明: 不依赖已停更的 lanzou-api 库——其上传接口 fileup.php 已废弃返回 404；
    本程序用 requests 自实现全部接口：浏览/建目录走 doupload.php，上传走 html5up.php。

功能:
    - 填写并保存已登录的 Cookie (phpdisk_info / ylogin)，放在「设置」弹窗中
    - 启动时 / 修改 Cookie 时自动检测 Cookie 是否有效
    - 程序内浏览蓝奏云目录，选择上传目标目录
    - 保持本地目录结构，上传到目标目录内
    - 「设置」弹窗内可开关: 自动忽略系统隐藏文件 (.DS_Store 等)，默认开启
    - Cookie / 开关 / 最近目标目录 / 目录描述 均保存到 JSON 配置文件；云盘目标目录下次打开自动恢复
    - 本地来源目录每次启动需手动选择（不自动恢复），云盘目标目录持久化复用
    - 上传前校验: 目录层级(目标深度 + 本地新建层级) <= 4 层、单文件 <= 100MB
    - 上传时显示: 当前文件、已上传数量与大小、剩余数量与大小、进度条、近 30 秒平均速度
    - 失败自动重试(指数退避)；区分「瞬时错误」(网络/限流，可重试)与「永久错误」(类型不支持等，不重试)
    - 按远程目录分组上传；同一目录内每批 ≤ 100 个文件，批间停顿，降低被限流概率(蓝奏云网页上传器单次上限即 100)
    - 断点续传: 重新开始时自动跳过上次已完成的文件，仅补传失败/未传的
    - 每次任务生成独立 JSON 日志(含每文件状态/错误)，便于程序读取查漏补缺
"""

import os
import re
import sys
import json
import time
import queue
import random
import mimetypes
import threading
import subprocess
from collections import deque, namedtuple, OrderedDict
from datetime import datetime

try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox, scrolledtext
except ImportError:
    sys.exit("错误: 当前 Python 未包含 tkinter，请使用完整版 Python 运行本程序。")

import requests
import urllib3
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

try:
    from requests_toolbelt import MultipartEncoder, MultipartEncoderMonitor
except ImportError:
    sys.exit("错误: 缺少依赖 requests-toolbelt，请先执行: pip install requests-toolbelt")

HERE = os.path.dirname(os.path.abspath(__file__))


def _get_data_dir():
    """返回程序持久化数据目录：
    - 未打包（源码运行）：程序所在目录（兼容现有行为）。
    - 打包后（PyInstaller .app / .exe）：系统用户应用数据目录，
      避免写入只读的 bundle / Program Files 导致 PermissionError。
    """
    if getattr(sys, "frozen", False):
        if sys.platform == "darwin":
            base = os.path.expanduser("~/Library/Application Support")
        elif sys.platform == "win32":
            base = os.environ.get("APPDATA") or os.path.expanduser("~")
        else:
            base = os.environ.get("XDG_CONFIG_HOME") or os.path.expanduser("~/.config")
        return os.path.join(base, "lanzou_uploader")
    return HERE


DATA_DIR = _get_data_dir()
CONFIG_PATH = os.path.join(DATA_DIR, "config.json")
LOGS_DIR = os.path.join(DATA_DIR, "logs")

MAX_DEPTH = 4                      # 蓝奏云目录层级上限(根目录算第 0 层)
MAX_FILE_BYTES = 100 * 1024 * 1024  # 单文件大小上限 100MB
HIDDEN_IGNORE = {".DS_Store", "Thumbs.db", "Desktop.ini", ".localized", "__MACOSX"}

# ===== 文件名 / 目录名 规范（蓝奏云）=====
# 允许上传的文件后缀（小写，不含点）。来源：官方/社区一致清单(单文件≤100MB 前提下)。
# 不在此清单的后缀视为「不允许的文件类型」（上传/分享会被拒或异常），如 .pps/.swf/无后缀等。
ALLOWED_EXT = {
    "doc", "docx", "zip", "rar", "apk", "ipa", "txt", "exe", "7z", "e", "z", "ct", "ke",
    "cetrainer", "db", "tar", "pdf", "w3x", "epub", "mobi", "azw", "azw3", "osk", "osz",
    "xpa", "cpk", "lua", "jar", "dmg", "ppt", "pptx", "xls", "xlsx", "mp3", "iso", "img",
    "gho", "ttf", "ttc", "txf", "dwg", "bat", "imazingapp", "dll", "crx", "xapk", "conf",
    "deb", "rp", "rpm", "rplib", "mobileconfig", "appimage", "lolgezi", "flac",
}
BAD_EXT_REPLACE = "zip"             # 「不允许的文件类型」自动改成的扩展名（通用且服务端允许）
# 文件名 / 目录名安全长度上限（过长会导致后缀丢失/被服务端拒绝，见 lanzou-api 回收站过长丢后缀 bug）
MAX_FILENAME_LEN = 200
MAX_DIRNAME_LEN = 100
# 文件名 / 目录名非法字符（Windows 保留字符）。空格现已允许，不做处理；
# 但目录名中的空格为兼容分享链接转为下划线。
ILLEGAL_NAME_CHARS = set('\\/:*?"<>|')
# 自动转为普通空格的非常规空白（lanzou-api 也会做此归一）
NAME_SPACE_NORMALIZE = {"\xa0", "\u3000"}

# 重试策略
RETRY_MAX = 3                      # 单个文件最多重试次数(不含首次)
RETRY_BASE_DELAY = 4.0             # 首次重试等待秒数(指数退避基数)
RETRY_MAX_DELAY = 60.0             # 退避上限
INTER_FILE_DELAY = 0.3             # 每个文件之间的最小间隔，降低请求频率被限流概率

# 分批上传：蓝奏云网页上传器单次选择上限为 100 个，这里对齐该习惯，
# 在「同一个远程目录内」每批最多上传 BATCH_SIZE 个文件，批与批之间随机停顿 2~10 秒，
# 既贴合手动上传体验，也大幅降低批量快速上传触发「请求过于频繁」等瞬时限流的概率。
# 注：蓝奏云官方并未规定单文件夹文件数量上限（单文件夹可容纳大量文件），
# 分批只是为了控速，而非规避文件夹容量限制；停顿时间不计入平均速度计算。
BATCH_SIZE = 100
BATCH_PAUSE_MIN = 2.0              # 批间最短停顿(秒)
BATCH_PAUSE_MAX = 10.0             # 批间最长停顿(秒)

# 内置候选 UA：2026 主流浏览器，互不相同。蓝奏云对老 UA（如 Chrome/75）会反爬拦截
# （返回空 HTML），必须用现代 UA，否则登录检测、列目录、上传全部失败。
BUILTIN_UAS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36 Edg/128.0.0.0",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:129.0) Gecko/20100101 Firefox/129.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Safari/605.1.15",
]
MODERN_UA = BUILTIN_UAS[0]   # 默认 UA（向后兼容：保留原变量名）
# 下拉菜单中内置 UA 的简化显示名（仅影响显示，不影响实际使用的 UA；顺序与 BUILTIN_UAS 一一对应）
UA_DISPLAY_NAMES = [
    "Windows 系统 Chrome 浏览器",
    "macOS 系统 Chrome 浏览器",
    "Windows 系统 Edge 浏览器",
    "Windows 系统 Firefox 浏览器",
    "macOS 系统 Safari 浏览器",
]
# mimetypes 兜底：(扩展名 -> MIME)，避免某些类型 guess 不出时传成 octet-stream 被拒
EXT_MIME = {
    ".md": "text/markdown", ".txt": "text/plain", ".py": "text/plain", ".log": "text/plain",
    ".html": "text/html", ".htm": "text/html", ".css": "text/css", ".js": "application/javascript",
    ".json": "application/json", ".xml": "application/xml", ".csv": "text/csv",
    ".zip": "application/zip", ".rar": "application/x-rar-compressed",
    ".7z": "application/x-7z-compressed", ".tar": "application/x-tar", ".gz": "application/gzip",
    ".pdf": "application/pdf",
    ".doc": "application/msword",
    ".docx": "application/vnd.openxmlformats-officedocument.wordprocessingml.document",
    ".xls": "application/vnd.ms-excel",
    ".xlsx": "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
    ".ppt": "application/vnd.ms-powerpoint",
    ".pptx": "application/vnd.openxmlformats-officedocument.presentationml.presentation",
    ".apk": "application/vnd.android.package-archive",
    ".exe": "application/octet-stream", ".dmg": "application/octet-stream",
}

# 服务端「永久错误」关键词：命中则不重试，直接记录（多为账号/类型/目录容量限制）
PERMANENT_KEYWORDS = (
    "上限", "已满", "数量超限", "文件数", "类型不支持", "格式不对", "不支持该类型",
    "不支持", "禁止", "违规", "敏感", "审核", "权限", "会员", "升级",
)


# ====================== 文件名 / 目录名 规范化 ======================
def sanitize_name(name, is_dir=False):
    """清理单个文件名或目录名，尽量不影响识别。
    返回 (clean, changed, reason)。changed=False 表示无需修改。
    规则：非常规空白→普通空格；目录名空格→下划线(兼容分享链接)；
    目录名中的"+"→下划线(蓝奏云新建目录名含"+"会失败)；
    删除非法字符(\\ / : * ? " < > | 及控制字符)；去首尾点/空格；超长保扩展名截断。
    """
    changed = False
    reasons = []
    clean = name

    # 非常规空白归一
    for ch in NAME_SPACE_NORMALIZE:
        if ch in clean:
            clean = clean.replace(ch, " ")
            changed = True
    # 目录名空格 -> 下划线
    if is_dir and " " in clean:
        clean = clean.replace(" ", "_")
        changed = True
    # 目录名中的 "+" 会导致蓝奏云新建目录失败，替换为下划线（仅目录名，文件名保持原样）
    if is_dir and "+" in clean:
        clean = clean.replace("+", "_")
        changed = True
        reasons.append("目录名'+'替换为'_'")
    # 删除非法字符与控制字符
    bad = [c for c in clean if c in ILLEGAL_NAME_CHARS or ord(c) < 32]
    if bad:
        seen = []
        for c in bad:
            if c not in seen:
                seen.append(c)
        clean = "".join(c for c in clean if c not in ILLEGAL_NAME_CHARS and ord(c) >= 32)
        changed = True
        reasons.append("非法字符[" + "".join(seen) + "]删除")
    # 去首尾点/空格（Windows/macOS 不安全的首尾字符）
    stripped = clean.strip(". ").strip()
    if stripped != clean:
        clean = stripped
        changed = True
        if "首尾" not in "".join(reasons):
            reasons.append("去首尾点/空格")
    # 超长截断（尽量保留扩展名完整）
    limit = MAX_DIRNAME_LEN if is_dir else MAX_FILENAME_LEN
    if len(clean) > limit:
        base, ext = os.path.splitext(clean)
        if ext and len(ext) < limit:
            keep = limit - len(ext)
            clean = base[:keep] + ext
        else:
            clean = clean[:limit]
        changed = True
        reasons.append(f"超长截断(≤{limit})")
    if clean == "":
        clean = "未命名"
        changed = True
        reasons.append("空名补默认")
    return clean, changed, "；".join(reasons)


def sanitize_rel(rel):
    """对相对路径的每个分段分别清洗（目录名 is_dir=True，文件名 is_dir=False）。
    返回 (clean_rel, changed, reason)。changed=False 表示整条路径无需修改。
    """
    parts = rel.split(os.sep)
    out = []
    changed_any = False
    reasons = []
    for i, part in enumerate(parts):
        is_dir = i < len(parts) - 1
        clean, changed, reason = sanitize_name(part, is_dir=is_dir)
        out.append(clean)
        if changed:
            changed_any = True
            if reason:
                reasons.append(f"{part}→{clean}({reason})")
    return os.sep.join(out), changed_any, "；".join(reasons)


def ext_allowed(rel):
    """该文件后缀是否在蓝奏云允许上传清单内（无后缀也视为不允许）。"""
    ext = os.path.splitext(rel)[1].lower().lstrip(".")
    return ext in ALLOWED_EXT


Item = namedtuple("Item", ["id", "name"])


class LanZouClient:
    """蓝奏云 API 的轻量自实现客户端，仅依赖 requests。
    替代已停更且上传接口失效的 lanzou-api 库。
    所有接口走 https://pc.woozooo.com/doupload.php (uid 参数)，
    与浏览器网盘页面同源，避免库自带的 lanzouw.com 等已反爬域名。
    """
    BASE = "https://pc.woozooo.com"
    SUCCESS = 0
    FAILED = -1          # 服务端拒绝 (zt != 1)
    NETWORK_ERROR = -2   # 请求异常 / 响应非 JSON
    _MAX_PAGES = 50      # 文件夹文件列表分页上限，防止异常时死循环

    def __init__(self):
        self.session = requests.Session()
        self.user_agent = MODERN_UA
        self.session.headers.update({
            "User-Agent": self.user_agent,
            "X-Requested-With": "XMLHttpRequest",
            "Accept": "application/json, text/javascript, */*; q=0.01",
            "Referer": self.BASE + "/mydisk.php",
        })
        self.uid = ""

    def set_user_agent(self, ua):
        """运行时动态切换 User-Agent（影响后续所有请求与上传）。"""
        self.user_agent = ua
        self.session.headers["User-Agent"] = ua

    def login(self, raw_cookie):
        """解析并写入浏览器 Cookie，返回 (ok, cookie_dict 或 error_msg)。"""
        cookie = {}
        for part in raw_cookie.split(";"):
            part = part.strip()
            if not part or "=" not in part:
                continue
            k, v = part.split("=", 1)
            cookie[k.strip()] = v.strip()
        if "phpdisk_info" not in cookie:
            return False, "Cookie 缺少 phpdisk_info（请从浏览器登录后复制完整的 Cookie 请求头）"
        if "ylogin" not in cookie:
            return False, "Cookie 缺少 ylogin（请复制完整的 Cookie 请求头，而非仅 phpdisk_info）"
        self.uid = cookie["ylogin"]
        self.session.cookies.clear()
        for k, v in cookie.items():
            self.session.cookies.set(k, v, domain=".woozooo.com")
        return True, cookie

    def is_logged_in(self):
        """用真实接口(doupload.php task=47)验证会话是否有效。"""
        j = self._post_json(47, folder_id=-1)
        return bool(j) and j.get("zt") == 1

    def _post_json(self, task, **data):
        data["task"] = task
        try:
            r = self.session.post(
                f"{self.BASE}/doupload.php?uid={self.uid}",
                data=data, verify=False, timeout=30,
            )
            return r.json()
        except Exception:
            return None

    def get_dir_list(self, folder_id=-1):
        """返回 [Item(id, name), ...] 子文件夹列表。"""
        j = self._post_json(47, folder_id=folder_id)
        out = []
        if not j or not isinstance(j.get("text"), list):
            return out
        for f in j["text"]:
            try:
                out.append(Item(int(f["fol_id"]), f["name"]))
            except (KeyError, TypeError, ValueError):
                continue
        return out

    def get_file_list(self, folder_id=-1):
        """返回 [Item(id, name), ...] 文件列表(按页拉全)。"""
        out = []
        page = 1
        while page <= self._MAX_PAGES:
            j = self._post_json(5, folder_id=folder_id, pg=page)
            if not j:
                break
            text = j.get("text") or []
            if isinstance(text, list):
                for f in text:
                    try:
                        name = (f.get("name_all") or "").replace("&amp;", "&")
                        out.append(Item(int(f["id"]), name))
                    except (KeyError, TypeError, ValueError):
                        continue
            if not text or j.get("info") == 0:
                break
            page += 1
        return out

    def mkdir(self, parent_id, folder_name, description=""):
        """在 parent_id 下创建子目录，返回新目录 id(int>0)，失败返回 -1。
        description: 蓝奏云文件夹「描述」字段（仅在新建时提交；若同名目录已存在则复用，不更新其描述）。
        """
        name = folder_name.replace(" ", "_")
        # 已存在则直接复用，避免重复建同名目录
        for item in self.get_dir_list(parent_id):
            if item.name == name:
                return item.id
        j = self._post_json(2, parent_id=(parent_id if parent_id is not None else -1),
                            folder_name=name, folder_description=description or "")
        if not j or j.get("zt") != 1:
            return -1
        # 创建成功后重新列父目录、按名取 id(不依赖 mkdir 响应字段，更稳)
        for item in self.get_dir_list(parent_id):
            if item.name == name:
                return item.id
        return -1


def format_size(n):
    n = float(n)
    if n < 1024:
        return f"{n:.0f} B"
    if n < 1024 ** 2:
        return f"{n / 1024:.1f} KB"
    if n < 1024 ** 3:
        return f"{n / 1024 ** 2:.1f} MB"
    return f"{n / 1024 ** 3:.2f} GB"


def classify_error(code, detail):
    """返回 ('transient'|'permanent', reason)。transient 可重试，permanent 不重试。"""
    d = (detail or "").lower()
    if code == LanZouClient.NETWORK_ERROR:
        return "transient", "网络/超时"
    for kw in PERMANENT_KEYWORDS:
        if kw in (detail or ""):
            return "permanent", "服务端永久拒绝"
    if "timeout" in d or "timed out" in d or "超时" in (detail or ""):
        return "transient", "网络超时"
    if "频繁" in (detail or "") or "过快" in (detail or "") or "频率" in (detail or ""):
        return "transient", "请求过于频繁"
    return "transient", "未知瞬时错误"


class TaskLog:
    """每次上传任务生成一个独立 JSON 日志，记录每文件状态与错误，便于查漏补缺。"""
    def __init__(self, local_folder, target_id, target_path, description=""):
        self.ts = datetime.now()
        stamp = self.ts.strftime("%Y%m%d_%H%M%S")
        safe = re.sub(r'[^A-Za-z0-9_-]', '_', os.path.basename(local_folder or "task"))[:30] or "task"
        os.makedirs(LOGS_DIR, exist_ok=True)
        self.path = os.path.join(LOGS_DIR, f"task_{stamp}_{safe}.json")
        self.data = {
            "start_time": self.ts.isoformat(timespec="seconds"),
            "local_folder": local_folder,
            "target_id": target_id,
            "target_path": target_path,
            "dir_description": description,
            "total": 0,
            "uploaded": 0, "skipped": 0, "failed": 0,
            "files": {},            # rel -> {status,size,attempts,error}
            "failed_files": [],     # 仅失败文件清单，便于快速读取
        }

    def set_total(self, n):
        self.data["total"] = n

    def update(self, rel, status, size, attempts, error, remote_rel=None):
        self.data["files"][rel] = {
            "status": status, "size": size,
            "attempts": attempts, "error": error,
            # 实际上传到云端时的相对路径（含子目录与改名后的文件名），重试时据此定位云端目录
            "remote_rel": remote_rel if remote_rel is not None else rel,
        }
        self.data["uploaded"] = sum(1 for e in self.data["files"].values() if e["status"] == "success")
        self.data["skipped"] = sum(1 for e in self.data["files"].values() if e["status"] == "skipped")
        self.data["failed"] = sum(1 for e in self.data["files"].values() if e["status"] == "failed")
        self.data["failed_files"] = [r for r, e in self.data["files"].items() if e["status"] == "failed"]

    @classmethod
    def load(cls, path):
        """从已有日志文件载入，后续写回同一路径（用于重试失败文件）。"""
        obj = cls.__new__(cls)
        obj.path = path
        with open(path, encoding="utf-8") as f:
            obj.data = json.load(f)
        obj.ts = datetime.now()   # 重试的计时基准以本次重传为准
        return obj

    def finish(self):
        self.data["end_time"] = datetime.now().isoformat(timespec="seconds")
        try:
            self.data["duration_sec"] = round((datetime.now() - self.ts).total_seconds(), 1)
        except Exception:
            pass

    def save(self):
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(self.data, f, ensure_ascii=False, indent=2)
        os.replace(tmp, self.path)


class NullTaskLog:
    """日志功能关闭时的空实现：所有方法均为 no-op，path 为 None（表示不写日志文件）。"""
    path = None

    def set_total(self, n): pass
    def update(self, *a, **k): pass
    def finish(self): pass
    def save(self): pass


class App:
    def __init__(self, root):
        self.root = root
        self.root.title("蓝奏云批量上传")
        self.root.geometry("390x520")
        self.root.minsize(360, 470)
        try:
            self._apply_icon(self.root)
        except Exception:
            pass

        self.client = LanZouClient()
        self.cookie_valid = False
        self.cookie_checked = False
        self.running = False
        self.cancelled = False

        # ===== 上传状态(由工作线程写，UI 定时器读) =====
        self.total_files = 0
        self.total_bytes = 0
        self.file_start_offset = 0
        self.processed_bytes = 0
        self.uploaded_count = 0
        self.uploaded_bytes = 0
        self.skipped_count = 0
        self.skipped_bytes = 0
        self.failed_count = 0
        self.current_file = ""
        self.start_time = 0.0
        self.samples = deque()
        self._last_sample_t = 0.0
        self.log_queue = queue.Queue()
        self._pending_popup = None

        # ===== 路径/目标 =====
        self.local_folder = ""              # 兼容字段：单一目录时等于 local_items[0]，否则为空
        self.local_items = []               # 实际上传来源：文件/文件夹路径列表（可多选）
        self.target_id = -1                # 用户在「浏览云目录」中选的目标目录
        self.target_path = "根目录"
        self.target_depth = 0
        self.upload_root_id = -1           # 实际上传根：target_id 下再建的「本地目录名」文件夹
        self.upload_root_path = ""
        self.dir_description = ""          # 为蓝奏云上「本地目录名」文件夹填写的描述
        self.last_file_list = []

        # ===== 配置 =====
        self.config = {
            "cookie": "",
            "ignore_hidden": True,
            "last_local_folder": "",
            "last_target_folder_id": -1,
            "last_target_path": "根目录",
            "last_target_depth": 0,
            "dir_description": "",
            "last_task": None,
            "ua_mode": "random",
            "ua_custom": "",
        }
        self.ignore_hidden_var = tk.BooleanVar(value=True)
        self.ignore_hidden_var.trace_add("write", lambda *a: self.save_config())

        # 上传前检查的三类自动处置开关（默认均不选中，需用户手动开启）
        self.auto_fix_name_var = tk.BooleanVar(value=False)       # 自动处理文件名中的禁用文字
        self.auto_fix_type_var = tk.BooleanVar(value=False)       # 自动更改限制上传文件类型扩展名
        self.auto_exclude_oversize_var = tk.BooleanVar(value=False)  # 自动排除超过 100M 的文件
        for _v in (self.auto_fix_name_var, self.auto_fix_type_var, self.auto_exclude_oversize_var):
            _v.trace_add("write", lambda *a: self.save_config())

        # 上传日志功能开关（默认不选中：主界面「日志」按钮隐藏、上传不写日志）
        self.enable_log_var = tk.BooleanVar(value=False)
        self.enable_log_var.trace_add("write", lambda *a: self.save_config())

        # 访问时使用 User-Agent 的设置
        self.ua_mode_var = tk.StringVar(value="random")     # random / builtin:N / custom
        self.ua_custom_var = tk.StringVar(value="")

        self.load_config()
        # 依据设置应用 User-Agent（必须在 load_config 之后、任何登录/上传之前）
        self.apply_user_agent()

        self.build_ui()
        self.refresh_target_display()
        self.refresh_controls()
        self.refresh_resume_hint()
        self._fit_window_height()
        self.root.after(250, self.update_ui)
        # 每次启动都自动检测 Cookie 有效性
        self.root.after(500, self.auto_check_cookie)

    # ====================== 图标 ======================
    def _load_icon(self):
        """加载窗口图标。兼容源码运行与 PyInstaller 打包后的多种路径布局。"""
        candidates = []
        if getattr(sys, "frozen", False):
            # PyInstaller 运行时会设置 sys._MEIPASS（资源根目录）
            meipass = getattr(sys, "_MEIPASS", None)
            if meipass:
                candidates.append(os.path.join(meipass, "assets", "appicon.png"))
            # onedir .app 兜底：HERE = Contents/MacOS，assets 实际在 Contents/Resources
            candidates.append(os.path.join(os.path.dirname(HERE), "Resources", "assets", "appicon.png"))
        # 源码运行时，图标就在程序同目录的 assets/ 下
        candidates.append(os.path.join(HERE, "assets", "appicon.png"))
        for p in candidates:
            if os.path.exists(p):
                return tk.PhotoImage(file=p)
        return None

    def _apply_icon(self, win):
        try:
            img = self._load_icon()
            if img is not None:
                win.iconphoto(True, img)
        except Exception:
            pass

    # ====================== 配置 ======================
    def load_config(self):
        need_default = False
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                self.config.update(json.load(f))
        except FileNotFoundError:
            # 没有配置文件：按默认生成 config.json（cookie 与自定义 UA 均为空）
            need_default = True
        except json.JSONDecodeError:
            pass
        # 本地来源目录：每次启动都要求手动选择，不自动恢复上次目录；
        # 仅云盘目标目录会持久化复用（见下方 last_target_*）。
        self.local_folder = ""
        self.local_items = []
        self.ignore_hidden_var.set(bool(self.config.get("ignore_hidden", True)))
        self.auto_fix_name_var.set(bool(self.config.get("auto_fix_name", False)))
        self.auto_fix_type_var.set(bool(self.config.get("auto_fix_type", False)))
        self.auto_exclude_oversize_var.set(bool(self.config.get("auto_exclude_oversize", False)))
        self.enable_log_var.set(bool(self.config.get("enable_log", False)))
        self.ua_mode_var.set(str(self.config.get("ua_mode", "random")))
        self.ua_custom_var.set(str(self.config.get("ua_custom", "")))
        self.target_id = int(self.config.get("last_target_folder_id", -1))
        self.target_path = self.config.get("last_target_path", "根目录")
        self.target_depth = int(self.config.get("last_target_depth", 0))
        self.dir_description = self.config.get("dir_description", "")
        if need_default:
            self.save_config()

    def save_config(self):
        os.makedirs(DATA_DIR, exist_ok=True)
        self.config["cookie"] = self.config.get("cookie", "")
        self.config["ignore_hidden"] = bool(self.ignore_hidden_var.get())
        self.config["auto_fix_name"] = bool(self.auto_fix_name_var.get())
        self.config["auto_fix_type"] = bool(self.auto_fix_type_var.get())
        self.config["auto_exclude_oversize"] = bool(self.auto_exclude_oversize_var.get())
        self.config["enable_log"] = bool(self.enable_log_var.get())
        self.config["ua_mode"] = str(self.ua_mode_var.get())
        self.config["ua_custom"] = str(self.ua_custom_var.get())
        self.config["last_local_folder"] = self.local_folder
        self.config["last_local_items"] = list(self.local_items)
        self.config["last_target_folder_id"] = self.target_id
        self.config["last_target_path"] = self.target_path
        self.config["last_target_depth"] = self.target_depth
        self.config["dir_description"] = self.dir_description
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(self.config, f, ensure_ascii=False, indent=2)

    # ====================== User-Agent 应用 ======================
    def apply_user_agent(self):
        """依据 ua_mode 解析实际使用的 User-Agent 并写入客户端：
        - random：每次启动随机挑一个内置 UA
        - builtin:N：使用第 N 个内置 UA（N=0..4）
        - custom：使用用户手填的 UA（为空则回退到默认 UA）
        """
        mode = str(self.ua_mode_var.get())
        if mode == "random":
            ua = random.choice(BUILTIN_UAS)
        elif mode.startswith("builtin:"):
            try:
                ua = BUILTIN_UAS[int(mode.split(":", 1)[1])]
            except (ValueError, IndexError):
                ua = BUILTIN_UAS[0]
        elif mode == "custom":
            ua = str(self.ua_custom_var.get()).strip() or BUILTIN_UAS[0]
        else:
            ua = BUILTIN_UAS[0]
        self.client.set_user_agent(ua)

    # ====================== Cookie ======================
    def do_login(self, raw):
        ok, cookie_or_msg = self.client.login(raw)
        if not ok:
            return False, cookie_or_msg
        try:
            if self.client.is_logged_in():
                return True, "有效"
            return False, "Cookie 无效或服务端未认证（可能已过期，请重新登录后复制）"
        except Exception as e:
            return False, f"登录请求异常: {e}"

    def auto_check_cookie(self):
        raw = (self.config.get("cookie") or "").strip()
        if not raw:
            self.cookie_checked = True
            self.update_cookie_btn()
            return
        ok, msg = self.do_login(raw)
        self.cookie_valid = ok
        self.cookie_checked = True
        if not ok:
            self.log_queue.put("⚠ 已保存的 Cookie 无效：" + msg + "\n")
            messagebox.showwarning(
                "Cookie 无效",
                "启动时检测到已保存的 Cookie 无效：\n" + msg +
                "\n\n请点击右上角「云盘 Cookie」按钮，重新填写并检测。",
            )
        else:
            self.log_queue.put("✓ Cookie 有效，已自动登录。\n")
        self.update_cookie_btn()
        self.refresh_controls()

    # ====================== 设置弹窗（仅保留非 Cookie 选项） ======================
    def open_settings(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("设置")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.geometry("380x280")
        try:
            self._apply_icon(dlg)
        except Exception:
            pass

        ttk.Checkbutton(dlg, text="忽略系统隐藏文件 (.DS_Store / Thumbs.db 等)",
                        variable=self.ignore_hidden_var).pack(anchor="w", padx=14, pady=(16, 6))

        # 上传前检查自动处置（默认不选中，选中后对应问题不再弹窗，直接按以下方式处理）
        ttk.Checkbutton(dlg, text="自动处理文件名中的禁用文字（非法字符/超长自动修复）",
                        variable=self.auto_fix_name_var).pack(anchor="w", padx=14, pady=4)
        ttk.Checkbutton(dlg, text="自动更改限制上传文件类型扩展名（追加可用扩展名）",
                        variable=self.auto_fix_type_var).pack(anchor="w", padx=14, pady=4)
        ttk.Checkbutton(dlg, text="自动排除超过 100M 的文件",
                        variable=self.auto_exclude_oversize_var).pack(anchor="w", padx=14, pady=4)
        ttk.Checkbutton(dlg, text="开启上传日志功能",
                        variable=self.enable_log_var).pack(anchor="w", padx=14, pady=4)

        # ===== 访问时使用 User-Agent =====
        ttk.Separator(dlg, orient="horizontal").pack(fill="x", padx=14, pady=(8, 6))
        ttk.Label(dlg, text="访问时使用 User-Agent",
                  font=("PingFang SC", "10", "bold")).pack(anchor="w", padx=14, pady=(0, 4))

        ua_items = ["每次启动自动随机内置UA"] + UA_DISPLAY_NAMES + ["手动输入自定义UA"]
        mode = self.ua_mode_var.get()
        if mode == "random":
            ua_idx = 0
        elif mode.startswith("builtin:"):
            try:
                ua_idx = 1 + int(mode.split(":", 1)[1])
            except (ValueError, IndexError):
                ua_idx = 0
        elif mode == "custom":
            ua_idx = len(ua_items) - 1
        else:
            ua_idx = 0

        ua_combo = ttk.Combobox(dlg, values=ua_items, state="readonly")
        ua_combo.pack(anchor="w", padx=14, pady=(0, 4), fill="x")
        ua_combo.current(ua_idx)

        # 自定义 UA 多行输入框：默认隐藏且不占位；选择「手动输入自定义UA」时显示，窗口随之增高
        ua_frame = ttk.Frame(dlg)
        ua_hint = ttk.Label(ua_frame, text="自定义 User-Agent：",
                            font=("PingFang SC", "9"))
        ua_hint.pack(anchor="w", padx=14, pady=(2, 2))
        ua_text = tk.Text(ua_frame, height=5, wrap="word", relief="solid", borderwidth=1)
        ua_text.pack(fill="x", padx=14, pady=(0, 6))
        ua_text.insert("1.0", self.ua_custom_var.get())

        def _on_ua_pick(event=None):
            # 仅当选中「手动输入自定义UA」(末项) 时显示输入框；其余情况隐藏且不占位
            if ua_combo.current() == len(ua_items) - 1:
                ua_frame.pack(anchor="w", fill="x")
                dlg.geometry("380x390")   # 窗口随输入框显示而增高（仅比隐藏态多 UA 框所需高度）
            else:
                ua_frame.pack_forget()
                dlg.geometry("380x280")

        ua_combo.bind("<<ComboboxSelected>>", _on_ua_pick)
        _on_ua_pick()  # 初始化：按当前选择决定是否显示输入框

        def save_close():
            self.config["ignore_hidden"] = bool(self.ignore_hidden_var.get())
            self.config["auto_fix_name"] = bool(self.auto_fix_name_var.get())
            self.config["auto_fix_type"] = bool(self.auto_fix_type_var.get())
            self.config["auto_exclude_oversize"] = bool(self.auto_exclude_oversize_var.get())
            self.config["enable_log"] = bool(self.enable_log_var.get())
            ci = ua_combo.current()
            if ci == 0:
                self.ua_mode_var.set("random")
            elif ci == len(ua_items) - 1:
                self.ua_mode_var.set("custom")
            else:
                self.ua_mode_var.set("builtin:" + str(ci - 1))
            # 仅接受单个 UA：折叠全部换行/多余空白为单行（去首尾空白）
            self.ua_custom_var.set(" ".join(ua_text.get("1.0", tk.END).split()))
            self.save_config()
            self.apply_user_agent()   # 立即按新设置应用 UA
            self.refresh_controls()
            self.log_queue.put("设置已保存。\n")
            dlg.destroy()

        # 底部按钮：保存 / 取消 居中，间距与 Cookie 窗口一致（padx=10）
        spacer = ttk.Frame(dlg)
        spacer.pack(side="bottom", fill="y", expand=True)
        btn_row = ttk.Frame(dlg)
        btn_row.pack(side="bottom", fill="x", padx=14, pady=(4, 14))
        btn_center = ttk.Frame(btn_row)
        btn_center.pack(anchor="center")
        ttk.Button(btn_center, text="保存", command=save_close).pack(side="left", padx=10)
        ttk.Button(btn_center, text="取消", command=dlg.destroy).pack(side="left", padx=10)

        # 固定默认大小且不可调节
        dlg.resizable(False, False)

    # ====================== 云盘 Cookie 弹窗 ======================
    def open_cookie_window(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("云盘 Cookie")
        dlg.transient(self.root)
        dlg.grab_set()
        # 窗格更高，输入框更高
        dlg.geometry("430x430")
        try:
            self._apply_icon(dlg)
        except Exception:
            pass

        # 标题行：左为「登录 Cookie」，右为「检测 Cookie」按钮（点击后变为结果色）
        lbl_row = ttk.Frame(dlg)
        lbl_row.pack(fill="x", padx=14, pady=(14, 2))
        ttk.Label(lbl_row, text="登录 Cookie",
                  font=("PingFang SC", "10", "bold")).pack(side="left")

        def reset_test_btn():
            test_btn.config(text="检测 Cookie", fg="#000000")

        def test():
            raw = txt.get("1.0", tk.END).strip()
            if not raw:
                messagebox.showinfo("提示", "请先粘贴 Cookie。")
                return
            ok, msg = self.do_login(raw)
            self.cookie_valid = ok
            self.cookie_checked = True
            if ok:
                test_btn.config(text="Cookie 有效", fg="#1a7f37")
            else:
                test_btn.config(text="Cookie 无效", fg="#c0392b")
            self.update_cookie_btn()
            self.refresh_controls()

        # 检测按钮：初始黑字「检测 Cookie」；点击后变绿「Cookie 有效」/红「Cookie 无效」
        test_btn = tk.Button(lbl_row, text="检测 Cookie", fg="#000000",
                             font=("PingFang SC", "10"), command=test)
        test_btn.pack(side="right")

        # 输入框更高
        txt = tk.Text(dlg, height=10, wrap="word")
        txt.pack(fill="x", padx=14, pady=2)
        txt.insert("1.0", self.config.get("cookie", ""))
        txt.focus_set()

        # —— 如何从 Chrome 获取 Cookie 的帮助说明（关键信息用红色）——
        help_txt = tk.Text(dlg, height=10, wrap="word", relief="flat",
                           borderwidth=0, bg="#f3f3f3",
                           font=("PingFang SC", "9"), state="normal")
        help_txt.pack(fill="x", padx=14, pady=(4, 6))
        help_txt.tag_configure("k", foreground="#c0392b")

        def seg(text, key=False):
            if key:
                help_txt.insert("end", text, "k")
            else:
                help_txt.insert("end", text)

        seg("如何获取 Cookie（以 ")
        seg("Chrome", True)
        seg(" 为例）：\n")
        seg("步骤 1：打开 ")
        seg("Chrome", True)
        seg(" 浏览器，登录蓝奏云网页版（如 www.lanzou.com）。\n")
        seg("步骤 2：按 ")
        seg("F12", True)
        seg(" 打开")
        seg("开发者工具", True)
        seg("（或右键页面选「检查」）。\n")
        seg("步骤 3：点顶部「")
        seg("网络 (Network)", True)
        seg("」标签，并勾选")
        seg("保留日志", True)
        seg("。\n")
        seg("步骤 4：在页面上点一下或按 F5 刷新，让下方出现请求记录。\n")
        seg("步骤 5：在请求列表点任意请求，在右侧「")
        seg("标头 (Headers)", True)
        seg("」中找到「")
        seg("请求标头", True)
        seg("」里的 ")
        seg("Cookie", True)
        seg(" 这一行。\n")
        seg("步骤 6：把 ")
        seg("Cookie", True)
        seg(" 后面的整段内容")
        seg("复制", True)
        seg("，粘贴到上面的输入框即可。\n")
        help_txt.config(state="disabled")

        def save_close():
            raw = txt.get("1.0", tk.END).strip()
            self.config["cookie"] = raw
            # 同步写入客户端并校验，使「浏览云目录」可立即使用
            if raw:
                ok, msg = self.do_login(raw)
                self.cookie_valid = ok
                self.cookie_checked = True
            self.save_config()
            self.update_cookie_btn()
            self.refresh_controls()
            self.log_queue.put("Cookie 已保存。\n")
            dlg.destroy()

        # 输入框内容变化后，检测按钮恢复初始黑字状态
        def on_modified(event=None):
            txt.edit_modified(False)
            reset_test_btn()
        txt.bind("<<Modified>>", on_modified)
        txt.edit_modified(False)   # 清除初始 insert 触发的修改标记

        # 保存/取消按钮：紧跟在「获取 Cookie 说明」文字框下方
        btn_row = ttk.Frame(dlg)
        btn_row.pack(fill="x", padx=14, pady=(8, 14))
        btn_center = ttk.Frame(btn_row)
        btn_center.pack(anchor="center")
        ttk.Button(btn_center, text="保存", command=save_close).pack(side="left", padx=10)
        ttk.Button(btn_center, text="取消", command=dlg.destroy).pack(side="left", padx=10)

        # 固定默认大小且不可调节
        dlg.resizable(False, False)

    # ====================== Cookie 状态按钮 ======================
    def update_cookie_btn(self):
        """主界面「云盘 Cookie」按钮：文字显示登录有效性（绿/红）。"""
        if not hasattr(self, "cookie_btn"):
            return
        if not self.cookie_checked:
            self.cookie_btn.config(text="Cookie 检测中…", fg="#555555")
        elif self.cookie_valid:
            self.cookie_btn.config(text="登录有效", fg="#1a7f37")
        elif not (self.config.get("cookie") or "").strip():
            self.cookie_btn.config(text="未配置 Cookie", fg="#555555")
        else:
            self.cookie_btn.config(text="登录无效", fg="#c0392b")

    # ====================== 本地文件夹 / 目标目录 ======================
    def prompt_dir_description(self, folder_name):
        """为蓝奏云上即将建立的「本地目录名」文件夹输入描述。返回字符串(可空)或 None(取消)。"""
        dlg = tk.Toplevel(self.root)
        dlg.title("目录描述（可选）")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.geometry("420x160")
        try:
            self._apply_icon(dlg)
        except Exception:
            pass

        ttk.Label(dlg, text=f"上传后将在云盘目标目录下建立文件夹「{folder_name}」",
                  wraplength=380, justify="left").pack(anchor="w", padx=14, pady=(14, 4))
        ttk.Label(dlg, text="可为其填写「目录描述」（仅新建时提交；留空则不填写）：",
                  wraplength=380, justify="left").pack(anchor="w", padx=14, pady=(0, 4))

        entry = ttk.Entry(dlg)
        entry.insert(0, self.dir_description or "")
        entry.pack(fill="x", padx=14, pady=(0, 10))
        entry.focus_set()

        result = {"val": None}

        def ok():
            result["val"] = entry.get().strip()
            dlg.destroy()

        def cancel():
            result["val"] = None
            dlg.destroy()

        btn_row = ttk.Frame(dlg)
        btn_row.pack(fill="x", padx=14, pady=(0, 12))
        ttk.Button(btn_row, text="确定", command=ok).pack(side="right", padx=(8, 0))
        ttk.Button(btn_row, text="取消", command=cancel).pack(side="right")
        entry.bind("<Return>", lambda e: ok())
        dlg.wait_window()
        return result["val"]

    # ====================== 选择本地来源（文件/文件夹，可多选） ======================
    def _format_local_display(self):
        items = getattr(self, "local_items", [])
        if not items:
            return "（未选择）"
        if len(items) == 1:
            return os.path.basename(items[0].rstrip(os.sep))
        n_files = sum(1 for p in items if os.path.isfile(p))
        n_dirs = sum(1 for p in items if os.path.isdir(p))
        if n_files and n_dirs:
            return f"已选择 {n_files} 个文件，{n_dirs} 个文件夹"
        if n_dirs:
            return f"已选择 {n_dirs} 个文件夹"
        return f"已选择 {n_files} 个文件"

    def _update_desc_visibility(self):
        """仅当「单一目录」被选中时才显示目录描述行；其余情况隐藏该行。"""
        items = getattr(self, "local_items", [])
        single_dir = (len(items) == 1 and os.path.isdir(items[0]))
        if single_dir:
            self.dir_desc_row.pack(fill="x", padx=8, pady=(0, 6))
        else:
            self.dir_desc_row.pack_forget()

    def _open_local_picker(self):
        """弹出「选择上传文件/文件夹」对话框，可反复添加多个文件与文件夹。
        返回所选路径列表（至少 1 项）或 None（取消）。"""
        dlg = tk.Toplevel(self.root)
        dlg.title("选择上传文件/文件夹")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.geometry("460x380")
        try:
            self._apply_icon(dlg)
        except Exception:
            pass

        items = list(getattr(self, "local_items", []))

        listbox = tk.Listbox(dlg)
        listbox.pack(fill="both", expand=True, padx=10, pady=(10, 4))
        sb = ttk.Scrollbar(listbox, command=listbox.yview)
        listbox.config(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")

        def render():
            listbox.delete(0, tk.END)
            for p in items:
                kind = "文件夹" if os.path.isdir(p) else "文件"
                listbox.insert(tk.END, f"[{kind}] {p}")

        def add_files():
            fs = filedialog.askopenfilenames(title="选择文件（可多选）")
            for f in fs:
                ap = os.path.abspath(f)
                if ap not in items:
                    items.append(ap)
            render()

        def add_folder():
            d = filedialog.askdirectory(title="选择文件夹")
            if d:
                ad = os.path.abspath(d)
                if ad not in items:
                    items.append(ad)
            render()

        def remove_sel():
            for i in reversed(list(listbox.curselection())):
                items.pop(i)
            render()

        def clear_all():
            items.clear()
            render()

        btn_add = ttk.Frame(dlg)
        btn_add.pack(fill="x", padx=10, pady=4)
        ttk.Button(btn_add, text="添加文件...", command=add_files).pack(side="left", padx=4)
        ttk.Button(btn_add, text="添加文件夹...", command=add_folder).pack(side="left", padx=4)
        ttk.Button(btn_add, text="移除", command=remove_sel).pack(side="left", padx=4)
        ttk.Button(btn_add, text="清空", command=clear_all).pack(side="left", padx=4)

        result = {"items": None}

        def ok():
            result["items"] = list(items)
            dlg.destroy()

        def cancel():
            result["items"] = None
            dlg.destroy()

        btn_row = ttk.Frame(dlg)
        btn_row.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(btn_row, text="确定", command=ok).pack(side="right", padx=(8, 0))
        ttk.Button(btn_row, text="取消", command=cancel).pack(side="right")
        render()
        dlg.wait_window()
        return result["items"]

    # ---------- 原生单次多选（仅 macOS） ----------

    def _pick_local_items(self):
        """按平台选择本地来源：
        - macOS: 原生 NSOpenPanel，单次对话框即可同时多选「文件与文件夹」。
        - Windows / Linux 及其他: 沿用原 Tk 列表窗口（文件+文件夹混合多选）。
        原生 macOS 实现异常时回退到原 Tk 窗口。返回路径列表或 None（取消）。"""
        import sys
        plat = sys.platform
        if plat == "darwin":
            try:
                return self._native_pick_macos()
            except Exception:
                return self._open_local_picker()
        return self._open_local_picker()

    def _native_pick_macos(self):
        """macOS 原生 NSOpenPanel：单次对话框同时多选文件与文件夹。返回路径列表或 None（取消）。"""
        import ctypes
        objc = ctypes.CDLL('/usr/lib/libobjc.dylib')
        objc.objc_getClass.restype = ctypes.c_void_p
        objc.objc_getClass.argtypes = [ctypes.c_char_p]
        objc.sel_registerName.restype = ctypes.c_void_p
        objc.sel_registerName.argtypes = [ctypes.c_char_p]
        objc.objc_msgSend.restype = ctypes.c_void_p

        def cls(name):
            return objc.objc_getClass(name)

        def sel(name):
            return objc.sel_registerName(name)

        def msg(recv, selector, *args):
            objc.objc_msgSend.argtypes = [ctypes.c_void_p, ctypes.c_void_p] + [ctypes.c_void_p] * len(args)
            return objc.objc_msgSend(recv, sel(selector), *args)

        def msg_scalar(recv, selector, *args):
            # 用于返回值为标量（NSInteger/NSUInteger/BOOL）的方法，避免把 0 读成 None
            objc.objc_msgSend.argtypes = [ctypes.c_void_p, ctypes.c_void_p] + [ctypes.c_void_p] * len(args)
            objc.objc_msgSend.restype = ctypes.c_ulong
            try:
                return objc.objc_msgSend(recv, sel(selector), *args)
            finally:
                objc.objc_msgSend.restype = ctypes.c_void_p

        def nsstring(s):
            buf = s.encode('utf-8')
            return msg(cls(b'NSString'), b'stringWithUTF8String:', ctypes.c_char_p(buf))

        NSOpenPanel = cls(b'NSOpenPanel')
        panel = msg(NSOpenPanel, b'openPanel')
        msg(panel, b'setCanChooseFiles:', 1)
        msg(panel, b'setCanChooseDirectories:', 1)
        msg(panel, b'setAllowsMultipleSelection:', 1)
        msg(panel, b'setResolvesAliases:', 1)
        msg(panel, b'setCanCreateDirectories:', 1)
        msg(panel, b'setMessage:', nsstring('选择要上传的文件和文件夹（可多选）'))
        msg(panel, b'setPrompt:', nsstring('选择'))
        app = msg(cls(b'NSApplication'), b'sharedApplication')
        msg(app, b'activateIgnoringOtherApps:', 1)
        if msg_scalar(panel, b'runModal') != 1:  # NSModalResponseOK == 1
            return None
        urls = msg(panel, b'URLs')
        n = msg_scalar(urls, b'count')
        paths = []
        for i in range(n):
            url = msg(urls, b'objectAtIndex:', i)
            path_str = msg(url, b'path')
            if not path_str:
                continue
            objc.objc_msgSend.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
            cstr = objc.objc_msgSend(path_str, sel(b'UTF8String'))
            if not cstr:
                continue
            ptr = ctypes.cast(cstr, ctypes.c_char_p)
            if ptr.value:
                paths.append(ptr.value.decode('utf-8'))
        return paths

    def select_local_sources(self):
        """点击「选择上传文件/文件夹」：可选择一个或多个文件/文件夹，全部上传到云盘目标目录。
        仅当单一目录被选中时，才提示输入目录描述；其余情况不提示并隐藏描述行。"""
        chosen = self._pick_local_items()
        if chosen is None:
            return  # 取消：保留原有选择

        # 规整：去重 + 仅保留存在的路径
        seen = set()
        items = []
        for p in chosen:
            ap = os.path.abspath(p)
            if ap not in seen and os.path.exists(ap):
                seen.add(ap)
                items.append(ap)

        if not items:
            # 清空选择
            self.local_items = []
            self.local_folder = ""
            self.local_path_var.set("（未选择）")
            self.dir_description = ""
            self.dir_desc_var.set("（无）")
            self._update_desc_visibility()
            self.save_config()
            self.refresh_controls()
            self.refresh_resume_hint()
            return

        # 先立即记录并保存所选：即便后续不填描述，本次选择也已持久化。
        self.local_items = items
        self.local_folder = items[0]
        self.local_path_var.set(self._format_local_display())
        self.save_config()

        if len(items) == 1 and os.path.isdir(items[0]):
            # 仅单一目录：提示输入目录描述（可选）；取消描述不会丢弃已选目录。
            folder_name, _, _ = sanitize_name(os.path.basename(items[0].rstrip(os.sep)), is_dir=True)
            desc = self.prompt_dir_description(folder_name)
            if desc is not None:
                self.dir_description = desc
                self.dir_desc_var.set(desc or "（无）")
                self.save_config()
        else:
            # 其他情况（多文件/多文件夹/混合）：不提示描述
            self.dir_description = ""
            self.dir_desc_var.set("（无）")

        self._update_desc_visibility()
        self.refresh_controls()
        self.refresh_resume_hint()

    def refresh_target_display(self):
        self.target_path_var.set(self.target_path + f"  (id={self.target_id})")

    def browse_target(self):
        if not self.cookie_valid:
            messagebox.showwarning("请先登录", "请先在「设置」中填写有效 Cookie 再浏览目录。")
            return

        dlg = tk.Toplevel(self.root)
        dlg.title("选择蓝奏云目标目录")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.geometry("460x420")
        try:
            self._apply_icon(dlg)
        except Exception:
            pass

        stack = [(-1, "根目录")]
        folders_cache = []

        path_label = ttk.Label(dlg, text="")
        path_label.pack(fill="x", padx=10, pady=(10, 0))
        listbox = tk.Listbox(dlg, height=18)
        listbox.pack(fill="both", expand=True, padx=10, pady=8)
        sb = ttk.Scrollbar(listbox, command=listbox.yview)
        listbox.config(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")

        def render():
            cur_id = stack[-1][0]
            try:
                folders = self.client.get_dir_list(cur_id)
            except Exception as e:
                folders = []
                messagebox.showerror("读取目录失败", str(e))
            folders_cache.clear()
            folders_cache.extend(folders)
            listbox.delete(0, tk.END)
            for f in folders:
                listbox.insert(tk.END, f.name)
            path_label.config(text="当前路径: " + " / ".join(n for _, n in stack))

        def enter():
            sel = listbox.curselection()
            if not sel:
                return
            f = folders_cache[sel[0]]
            stack.append((f.id, f.name))
            render()

        def up():
            if len(stack) > 1:
                stack.pop()
                render()

        def confirm():
            self.target_id = stack[-1][0]
            self.target_path = " / ".join(n for _, n in stack)
            self.target_depth = len(stack) - 1
            self.refresh_target_display()
            self.save_config()
            dlg.destroy()

        btn_frame = ttk.Frame(dlg)
        btn_frame.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(btn_frame, text="进入", command=enter).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="上一级", command=up).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="选择此目录", command=confirm).pack(side="left", padx=4)
        ttk.Button(btn_frame, text="取消", command=dlg.destroy).pack(side="right", padx=4)
        listbox.bind("<Double-1>", lambda e: enter())

        render()
        dlg.wait_window()
        self.refresh_controls()
        self.refresh_resume_hint()

    # ====================== 文件扫描 / 校验 ======================
    def collect_files(self):
        items = self.local_items
        ignore = bool(self.ignore_hidden_var.get())
        files = []
        for root in items:
            if os.path.isdir(root):
                for dirpath, dirnames, filenames in os.walk(root):
                    if ignore:
                        dirnames[:] = [d for d in dirnames if not d.startswith(".") and d not in HIDDEN_IGNORE]
                    for fn in filenames:
                        if ignore and (fn.startswith(".") or fn in HIDDEN_IGNORE):
                            continue
                        abspath = os.path.join(dirpath, fn)
                        try:
                            size = os.path.getsize(abspath)
                        except OSError:
                            size = 0
                        rel = os.path.relpath(abspath, root)
                        files.append({"abspath": abspath, "rel": rel, "size": size, "root": root})
            elif os.path.isfile(root):
                abspath = root
                try:
                    size = os.path.getsize(abspath)
                except OSError:
                    size = 0
                rel = os.path.basename(abspath)
                files.append({"abspath": abspath, "rel": rel, "size": size, "root": root})
        return files

    def validate_before_upload(self, files, base_depth=None):
        """结构性校验：仅检查目录层级（蓝奏云硬限制，无法自动修复）。
        文件大小 / 文件名非法字符 / 文件类型 改为「上传前交互检查」弹窗处理，不再在此阻断。
        base_depth: 实际上传根目录的深度（默认取 self.target_depth）；本地目录本身会作为一层，
                    因此 start_upload 调用时传入 self.target_depth + 1。
        返回 (ok, problems: list[str])"""
        problems = []
        if base_depth is None:
            base_depth = self.target_depth
        allowed_local_depth = MAX_DEPTH - base_depth

        offending = set()
        max_local_depth = 0
        for f in files:
            parts = rel_parent_parts(f["rel"])
            depth = len(parts)
            max_local_depth = max(max_local_depth, depth)
            if depth > allowed_local_depth:
                offending.add(tuple(parts[: allowed_local_depth + 1]))
        if max_local_depth > allowed_local_depth:
            lines = ["【目录层级超限】实际上传根目录已占 %d 层（含本地目录本身），本地最多只能新建 %d 层（合计上限 %d 层）。超限位置示例："
                     % (base_depth, allowed_local_depth, MAX_DEPTH)]
            for p in sorted(offending)[:20]:
                lines.append("  - " + os.path.join(*p) + " ...")
            if len(offending) > 20:
                lines.append(f"  ... 共 {len(offending)} 处超限")
            problems.extend(lines)

        return (len(problems) == 0, problems)

    def analyze_files(self, files):
        """将文件按三类「上传前问题」分组，供交互弹窗展示。
        返回 (oversize, bad_name, bad_type)：
          oversize: [rel, ...]                      单文件 > 100MB
          bad_name: [(orig_rel, clean_rel, reason)] 文件名/目录名含非法字符或超长(需清洗)
          bad_type: [rel, ...]                      后缀不在允许上传清单
        """
        oversize, bad_name, bad_type = [], [], []
        for f in files:
            rel = f["rel"]
            size = f["size"]
            if size > MAX_FILE_BYTES:
                oversize.append(rel)
            clean_rel, changed, reason = sanitize_rel(rel)
            if changed:
                bad_name.append((rel, clean_rel, reason))
            if not ext_allowed(rel):
                bad_type.append(rel)
        return oversize, bad_name, bad_type

    # ====================== 上传前交互检查弹窗 ======================
    def show_issues_dialog(self, oversize, bad_name, bad_type):
        """在同一界面展示三类问题并列出具体文件，每类配单选框。
        返回处置字典 disposition = {bucket: action}，或用户取消时返回 None。
        任何一类有问题却未选择 -> 「开始上传」按钮禁用。
        窗口高度按内容自适应（内容过多时内部滚动，整体不超过屏幕高度）。
        """
        # 每类的标题、问题数、选项、文件清单
        buckets = []
        if oversize:
            buckets.append((
                "oversize", "⚠ 超出单文件 100MB 限制", len(oversize),
                [("ignore", "忽略：这些大文件不上传（蓝奏云单文件上限 100MB）")],
                [(r, r) for r in oversize],
            ))
        if bad_name:
            buckets.append((
                "bad_name", "✎ 文件名/目录名含不允许的字符或过长", len(bad_name),
                [("fix", "自动修复：删除或替换不允许的字符（尽量保留原意）"),
                 ("ignore", "忽略：这些文件不上传")],
                [(orig, f"{orig}  →  {clean}   [{reason}]") for orig, clean, reason in bad_name],
            ))
        if bad_type:
            buckets.append((
                "bad_type", "⛔ 文件类型/后缀不在允许上传清单", len(bad_type),
                [("fix", f"自动修复：原后缀后追加可用扩展名（保留原后缀，如 123.pps → 123.pps.{BAD_EXT_REPLACE}）"),
                 ("ignore", "忽略：这些文件不上传")],
                [(r, r) for r in bad_type],
            ))

        affected = len(set(oversize) | {t[0] for t in bad_name} | set(bad_type))

        dlg = tk.Toplevel(self.root)
        dlg.title("上传前检查")
        dlg.transient(self.root)
        dlg.grab_set()
        W = 520
        dlg.minsize(W, 200)
        try:
            self._apply_icon(dlg)
        except Exception:
            pass

        # 顶部说明
        head = ttk.Frame(dlg)
        head.pack(fill="x", padx=14, pady=(12, 4))
        ttk.Label(head, text="上传前检查", font=("PingFang SC", "13", "bold")).pack(anchor="w")
        ttk.Label(head,
                  text=f"共发现 {len(buckets)} 类问题，涉及 {affected} 个文件。\n"
                       f"请为每一类选择处理方式；全部选择后「开始上传」才可点击。",
                  font=("PingFang SC", "9"), foreground="#555555").pack(anchor="w", pady=(3, 0))

        # 滚动区
        canvas = tk.Canvas(dlg, borderwidth=0, highlightthickness=0)
        scroll = ttk.Scrollbar(dlg, orient="vertical", command=canvas.yview)
        inner = ttk.Frame(canvas)
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        inner_id = canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side="left", fill="x", expand=False, padx=(10, 0), pady=4)
        scroll.pack(side="right", fill="y", padx=(0, 6), pady=4)
        # 让内部内容宽度跟随画布宽度，列表框才能撑满
        canvas.bind("<Configure>",
                    lambda e: canvas.itemconfig(inner_id, width=canvas.winfo_width()))

        self._issue_vars = {}
        start_btn = ttk.Button(dlg, text="开始上传")  # 初始状态由 upd() 决定

        def upd():
            # 所有有问题的类都必须已选择，否则禁用
            ok = all(self._issue_vars[b[0]].get() for b in buckets)
            start_btn.config(state="normal" if ok else "disabled")

        for key, title, count, options, items in buckets:
            lf = ttk.LabelFrame(inner, text=f"{title}　（{count} 个）")
            lf.pack(fill="x", padx=10, pady=6)
            # 文件清单（限高、可滚动）
            lb = tk.Listbox(lf, height=min(len(items), 6), font=("Menlo", "9"))
            lb.pack(fill="x", padx=8, pady=(4, 2))
            lb_sb = ttk.Scrollbar(lb, command=lb.yview)
            lb.config(yscrollcommand=lb_sb.set)
            lb_sb.pack(side="right", fill="y")
            for _, disp in items:
                lb.insert(tk.END, disp)
            # 选项
            var = tk.StringVar(value="")
            self._issue_vars[key] = var
            var.trace_add("write", lambda *a: upd())
            opt_row = ttk.Frame(lf)
            opt_row.pack(fill="x", padx=8, pady=(2, 8))
            for val, label in options:
                ttk.Radiobutton(opt_row, text=label, variable=var, value=val).pack(anchor="w", pady=(1, 0))

        # 底部按钮
        btn_frame = ttk.Frame(dlg)
        btn_frame.pack(fill="x", padx=14, pady=(4, 12))
        start_btn.pack(side="left")
        cancel_btn = ttk.Button(btn_frame, text="取消")
        cancel_btn.pack(side="right")
        self._issues_result = None

        def close():
            canvas.unbind_all("<MouseWheel>")
            dlg.destroy()

        def do_start():
            self._issues_result = {key: self._issue_vars[key].get() for key, *_ in buckets}
            close()

        cancel_btn.config(command=close)
        start_btn.config(command=do_start)
        upd()  # 初始化按钮状态

        # 鼠标滚轮滚动
        def _on_wheel(e):
            canvas.yview_scroll(int(-1 * (e.delta / 120)), "units")
        canvas.bind_all("<MouseWheel>", _on_wheel)

        # 窗口高度按内容自适应（内容过多则内部滚动，整体不超过屏幕高度）
        dlg.update_idletasks()
        content_h = inner.winfo_reqheight()
        MAX_CANVAS_H = 460
        canvas_h = min(content_h, MAX_CANVAS_H)
        canvas.configure(height=canvas_h)
        if content_h > canvas_h:
            scroll.pack(side="right", fill="y", padx=(0, 6), pady=4)
        else:
            scroll.pack_forget()
        dlg.update_idletasks()
        total_h = dlg.winfo_reqheight()
        screen_h = dlg.winfo_screenheight()
        if total_h > screen_h - 60:
            avail = (screen_h - 60) - (total_h - canvas_h)
            canvas.configure(height=max(120, avail))
            scroll.pack(side="right", fill="y", padx=(0, 6), pady=4)
            dlg.update_idletasks()
            total_h = dlg.winfo_reqheight()
        dlg.geometry(f"{W}x{total_h}")
        dlg.minsize(W, total_h)

        dlg.wait_window()
        return self._issues_result

    def resolve_files(self, files, oversize_set, bad_name_list, bad_type_set, disp):
        """按用户在弹窗中的选择，生成最终待上传文件列表（含 target_rel）。
        - oversize 选 ignore -> 这些文件丢弃
        - bad_name 选 fix -> 应用清洗后的路径；选 ignore -> 丢弃
        - bad_type 选 fix -> 扩展名改为 BAD_EXT_REPLACE；选 ignore -> 丢弃
        bad_name_list 为 analyze_files 返回的 [(orig_rel, clean_rel, reason), ...]
        """
        bad_name_set = {t[0] for t in bad_name_list}
        out = []
        for f in files:
            orig_rel = f["rel"]
            drop = False
            clean_rel, changed, _ = sanitize_rel(orig_rel)
            eff_rel = clean_rel

            if orig_rel in bad_name_set:
                if disp.get("bad_name") == "ignore":
                    drop = True
                # fix: 已体现在 clean_rel 中
            if orig_rel in bad_type_set:
                if disp.get("bad_type") == "ignore":
                    drop = True
                elif disp.get("bad_type") == "fix":
                    # 追加允许的扩展名（保留原扩展名，便于识别），
                    # 如 123.pps -> 123.pps.zip；无扩展名则 noext -> noext.zip。
                    # 注意：仅用于上传时使用的文件名，绝不修改本地文件。
                    d = os.path.dirname(clean_rel)
                    name = os.path.basename(clean_rel)
                    orig_ext = os.path.splitext(name)[1]          # 原扩展名，如 .pps（可能为空）
                    stem = os.path.splitext(name)[0]              # 去掉原扩展名后的主干
                    protected = orig_ext + "." + BAD_EXT_REPLACE  # 必须保留的后缀，如 .pps.zip /.zip
                    max_stem = MAX_FILENAME_LEN - len(protected)
                    if len(stem) > max_stem:                      # 超长时只截断主干，保留两段扩展名
                        stem = stem[:max_stem]
                    final_name = stem + protected
                    eff_rel = (d + os.sep if d else "") + final_name
            if orig_rel in oversize_set and disp.get("oversize") == "ignore":
                drop = True

            if drop:
                continue
            nf = dict(f)
            nf["target_rel"] = eff_rel
            out.append(nf)
        return out

    # ====================== 断点续传：读取上次任务 ======================
    def _norm_folder(self, v):
        """将 last_task 中保存的 folder 统一规整为列表（兼容旧版单字符串格式）。"""
        if isinstance(v, list):
            return list(v)
        if isinstance(v, str):
            return [v] if v else []
        return []

    def load_prev_status(self):
        """读取上次同文件夹+同目标的任务日志，返回 {rel: status}。"""
        lt = self.config.get("last_task")
        if not lt:
            return {}
        if self._norm_folder(lt.get("folder")) != self.local_items:
            return {}
        if int(lt.get("target_id", -1)) != self.upload_root_id:
            return {}
        p = lt.get("path")
        if not p or not os.path.exists(p):
            return {}
        try:
            with open(p, encoding="utf-8") as f:
                d = json.load(f)
            return {rel: e.get("status") for rel, e in d.get("files", {}).items()}
        except Exception:
            return {}

    # ====================== 上传 ======================
    def start_upload(self):
        if self.running:
            return
        if not self.cookie_valid:
            messagebox.showwarning("未登录", "Cookie 无效，请先在「设置」中填写有效 Cookie。")
            return
        items = self.local_items
        if not items:
            messagebox.showwarning("未选择", "请先选择要上传的文件/文件夹。")
            return
        for p in items:
            if not os.path.exists(p):
                messagebox.showwarning("路径无效", f"找不到所选路径：\n{p}")
                return
        self.local_folder = items[0]   # 兼容字段：取首个作为代表路径

        files = self.collect_files()
        if not files:
            messagebox.showinfo("无文件", "所选内容中没有可上传的文件。")
            return

        # 为每项在云盘目标目录下建立自己的顶层文件夹：
        #  - 文件夹项：以文件夹名为目录（含描述，仅单一目录时）。
        #  - 文件项：直接放入目标目录。
        # 全部内容都上传到用户选定的目标目录下，并保持各自目录结构。
        self.upload_root_id = self.target_id
        self.upload_root_path = self.target_path
        for f in files:
            f["target_root_id"] = self.target_id   # 默认（文件项直接入目标目录）

        single_dir = (len(items) == 1 and os.path.isdir(items[0]))
        if single_dir:
            # 单一目录：维持原行为，建立一个「本地目录名」顶层文件夹（含描述）
            top_name, _, _ = sanitize_name(os.path.basename(items[0].rstrip(os.sep)), is_dir=True)
            try:
                top_id = self.client.mkdir(self.target_id, top_name, description=self.dir_description)
            except Exception as e:
                messagebox.showerror("无法创建上传目录", f"在「{self.target_path}」下创建文件夹「{top_name}」失败：{e}")
                return
            if not isinstance(top_id, int) or top_id < 0:
                messagebox.showerror(
                    "无法创建上传目录",
                    f"在「{self.target_path}」下创建文件夹「{top_name}」失败，请检查 Cookie 与网络后重试。",
                )
                return
            for f in files:
                f["target_root_id"] = top_id
            self.upload_root_id = top_id
            self.upload_root_path = self.target_path + " / " + top_name
            self.target_path_var.set(self.upload_root_path + f"  (id={self.upload_root_id})")
        else:
            # 多文件/多文件夹/混合：每个文件夹项各建顶层文件夹，文件项直接入目标目录
            for item in items:
                if os.path.isdir(item):
                    nm, _, _ = sanitize_name(os.path.basename(item.rstrip(os.sep)), is_dir=True)
                    try:
                        fid = self.client.mkdir(self.target_id, nm, description="")
                    except Exception:
                        fid = -1
                    if not isinstance(fid, int) or fid < 0:
                        fid = self.target_id   # 兜底：创建失败时直接放入目标目录
                    for f in files:
                        if f.get("root") == item:
                            f["target_root_id"] = fid
            self.target_path_var.set(self.target_path + f"  (id={self.target_id})")

        # 层级校验：实际上传根比所选目标深一层（本地目录本身占一层）
        ok, problems = self.validate_before_upload(files, base_depth=self.target_depth + 1)
        if not ok:
            messagebox.showerror(
                "无法开始上传",
                "上传前检查发现问题，已停止上传：\n\n" + "\n".join(problems),
            )
            return

        # 上传前交互检查：超出 100M / 文件名非法字符或超长 / 不允许的文件类型
        oversize, bad_name, bad_type = self.analyze_files(files)
        if oversize or bad_name or bad_type:
            disp = {}
            # 已开启「自动」开关的类别：不再弹窗，直接按对应方式处置
            if oversize and self.auto_exclude_oversize_var.get():
                disp["oversize"] = "ignore"        # 自动排除超大文件
            if bad_name and self.auto_fix_name_var.get():
                disp["bad_name"] = "fix"           # 自动修复文件名
            if bad_type and self.auto_fix_type_var.get():
                disp["bad_type"] = "fix"           # 自动追加可用扩展名

            if "oversize" in disp:
                self.log_queue.put(f"⚙ 已按设置自动排除 {len(oversize)} 个超过 100M 的文件。\n")
            if "bad_name" in disp:
                self.log_queue.put(f"⚙ 已按设置自动修复 {len(bad_name)} 个文件名/目录名。\n")
            if "bad_type" in disp:
                self.log_queue.put(f"⚙ 已按设置自动处理 {len(bad_type)} 个受限类型文件扩展名。\n")

            # 仍需用户手动选择的类别（未开启自动开关的部分）
            need_oversize = bool(oversize) and "oversize" not in disp
            need_bad_name = bool(bad_name) and "bad_name" not in disp
            need_bad_type = bool(bad_type) and "bad_type" not in disp
            if need_oversize or need_bad_name or need_bad_type:
                disp_user = self.show_issues_dialog(
                    oversize if need_oversize else [],
                    bad_name if need_bad_name else [],
                    bad_type if need_bad_type else [],
                )
                if disp_user is None:  # 用户取消
                    return
                disp.update(disp_user)

            files = self.resolve_files(files, set(oversize), bad_name, set(bad_type), disp)
            if not files:
                messagebox.showinfo(
                    "无文件可上传",
                    "您对全部问题都选择了「忽略」，没有可上传的文件。",
                )
                return

        self.save_config()
        self.last_file_list = files
        self.total_files = len(files)
        self.total_bytes = sum(f["size"] for f in files)

        # 重置状态
        self.file_start_offset = 0
        self.processed_bytes = 0
        self.uploaded_count = 0
        self.uploaded_bytes = 0
        self.skipped_count = 0
        self.skipped_bytes = 0
        self.failed_count = 0
        self.current_file = ""
        self.start_time = time.time()
        self.paused_duration = 0.0          # 累计停顿时长(不计入平均速度)
        self.samples.clear()
        self._last_sample_t = 0.0
        self._pending_popup = None
        self.cancelled = False
        self.running = True

        # 断点续传：仅当日志功能开启时加载上次任务已完成列表
        if self.enable_log_var.get():
            self.prev_status = self.load_prev_status()
        else:
            self.prev_status = {}
        resumed = sum(1 for s in self.prev_status.values() if s in ("success", "skipped"))

        # 任务日志（记录实际上传根 id 与描述，便于断点续传比对）；关闭日志功能时用空实现
        if self.enable_log_var.get():
            self.task_log = TaskLog(self.local_folder, self.upload_root_id, self.upload_root_path,
                                    description=self.dir_description)
            self.task_log.set_total(self.total_files)
            self.task_log.save()
        else:
            self.task_log = NullTaskLog()

        self.log_queue.put(
            f"开始上传：共 {self.total_files} 个文件，{format_size(self.total_bytes)}\n"
        )
        if resumed:
            self.log_queue.put(f"断点续传：检测到上次任务，将跳过 {resumed} 个已完成文件。\n")
        self.refresh_controls()

        t = threading.Thread(target=self.run_upload, daemon=True)
        t.start()

    def upload_callback(self, file_name, total_size, now_size):
        now_size = min(now_size, total_size)
        self.processed_bytes = self.file_start_offset + now_size
        eff = self._eff_elapsed()
        if eff - self._last_sample_t >= 0.25:
            self.samples.append((eff, self.processed_bytes))
            self._last_sample_t = eff

    def _eff_elapsed(self):
        """已用「有效」时长 = 墙钟 - 停顿累计，停顿不计入平均速度。"""
        return max(0.0, time.time() - self.start_time - getattr(self, "paused_duration", 0.0))

    def upload_file_real(self, filepath, folder_id, callback=None, remote_name=None):
        """通过蓝奏云当前上传接口 html5up.php 上传单个文件。
        返回 (code, detail)：code 成功=0，服务端拒绝=-1，网络异常=-2；detail 为错误信息/服务端提示。
        remote_name: 指定上传到服务端使用的文件名（用于自动修复后的文件名/扩展名）；
                     为 None 时使用本地文件名。
        """
        name = remote_name or os.path.basename(filepath)
        try:
            size = os.path.getsize(filepath)
        except OSError:
            return LanZouClient.FAILED, "无法读取文件"
        mime, _ = mimetypes.guess_type(filepath)
        if not mime:
            ext = os.path.splitext(name)[1].lower()
            mime = EXT_MIME.get(ext, "application/octet-stream")
        try:
            mtime = os.path.getmtime(filepath)
        except OSError:
            mtime = time.time()
        last_modified = time.strftime(
            "%a %b %d %Y %H:%M:%S GMT+0800 (中国标准时间)", time.localtime(mtime)
        )

        post_data = {
            "task": "1",
            "vie": "2",
            "ve": "2",
            "id": "WU_FILE_0",
            "name": name,
            "type": mime,
            "lastModifiedDate": last_modified,
            "size": str(size),
            "folder_id_bb_n": str(folder_id),
            "upload_file": (name, open(filepath, "rb"), mime),
        }
        enc = MultipartEncoder(post_data)
        headers = {
            "User-Agent": self.client.user_agent,
            "X-Requested-With": "XMLHttpRequest",
            "Accept": "application/json, text/javascript, */*; q=0.01",
            "Content-Type": enc.content_type,
            "Referer": f"https://pc.woozooo.com/mydisk.php?item=files&action=index&u={self.client.uid}",
            "Origin": "https://pc.woozooo.com",
        }
        timeout = max(120, int(size / (512 * 1024)) + 60)

        def _monitor(m):
            if callback:
                try:
                    callback(name, size, m.bytes_read)
                except Exception:
                    pass

        try:
            monitor = MultipartEncoderMonitor(enc, _monitor)
            r = self.client.session.post(
                "https://pc.woozooo.com/html5up.php",
                data=monitor, headers=headers, verify=False, timeout=timeout,
            )
        except Exception as e:
            self.log_queue.put(f"  ! 上传请求异常: {e}\n")
            return LanZouClient.NETWORK_ERROR, str(e)

        try:
            j = r.json()
        except Exception:
            self.log_queue.put(f"  ! 上传响应异常(非 JSON, HTTP {r.status_code})\n")
            return LanZouClient.FAILED, f"响应非 JSON (HTTP {r.status_code})"
        if j.get("zt") == 1:
            return LanZouClient.SUCCESS, ""
        info = j.get("info") or j.get("text") or "未知错误"
        self.log_queue.put(f"  ! 服务端拒绝上传: {info}\n")
        return LanZouClient.FAILED, str(info)

    def run_upload(self):
        files = self.last_file_list
        prev = getattr(self, "prev_status", {}) or {}
        task_log = self.task_log

        # 按「解析后的远程相对路径」分组：同一目录下的文件连续上传，便于分批次(每批 ≤100)
        def rel_dir_of(f):
            d = os.path.dirname(f.get("target_rel", f["rel"]))
            return d if d and d != "." else "."

        groups = OrderedDict()
        for f in files:
            groups.setdefault((f["target_root_id"], rel_dir_of(f)), []).append(f)

        for (root_id, rel_dir), group in groups.items():
            if self.cancelled:
                self.log_queue.put("【已取消】用户中止了上传。\n")
                break

            # 定位/创建该远程目录（整组共用，避免逐文件重复建目录）
            folder_id = root_id
            dir_err = None
            try:
                if rel_dir != ".":
                    for part in rel_dir.split(os.sep):
                        folder_id = self.client.mkdir(folder_id, part)
                        if not isinstance(folder_id, int) or folder_id < 0:
                            raise RuntimeError(f"创建目录失败 (code={folder_id}): {part}")
            except Exception as e:
                dir_err = e

            if dir_err is not None:
                # 整个目录不可用时，组内所有未完成文件标记为失败
                for f in group:
                    orig_rel = f["rel"]
                    size = f["size"]
                    if prev.get(orig_rel) in ("success", "skipped"):
                        self.file_start_offset += size
                        self.processed_bytes = self.file_start_offset
                        self.skipped_count += 1
                        self.skipped_bytes += size
                        task_log.update(orig_rel, "skipped", size, 0, "续传跳过(上次已完成)",
                                        remote_rel=f.get("target_rel", orig_rel))
                        continue
                    self.file_start_offset += size
                    self.failed_count += 1
                    self.log_queue.put(f"  ✗ 目录错误，跳过: {orig_rel}  ({dir_err})\n")
                    task_log.update(orig_rel, "failed", size, 0, f"目录错误: {dir_err}",
                                    remote_rel=f.get("target_rel", orig_rel))
                task_log.save()
                continue

            # 重名检测：整组一次性拉取已存在文件名（避免逐文件重复请求）
            try:
                existing = self.client.get_file_list(folder_id)
                existing_names = {x.name for x in existing}
            except Exception as e:
                existing_names = set()
                self.log_queue.put(f"  ! 重名检查失败(按续传/上传处理): {e}\n")

            # 同一目录内分批上传，每批 ≤ BATCH_SIZE 个，批间随机停顿
            for bi in range(0, len(group), BATCH_SIZE):
                if self.cancelled:
                    break
                batch = group[bi:bi + BATCH_SIZE]
                batch_no = bi // BATCH_SIZE + 1
                total_batches = (len(group) + BATCH_SIZE - 1) // BATCH_SIZE
                self.log_queue.put(
                    f"── 目录 [{rel_dir}] 第 {batch_no}/{total_batches} 批（{len(batch)} 个）──\n"
                )

                for f in batch:
                    if self.cancelled:
                        break
                    orig_rel = f["rel"]
                    eff_rel = f.get("target_rel", orig_rel)
                    size = f["size"]
                    abspath = f["abspath"]
                    remote_name = os.path.basename(eff_rel)

                    # 断点续传：跳过上次已完成的文件（按原始 rel 判定，保证跨次一致）
                    ps = prev.get(orig_rel)
                    if ps in ("success", "skipped"):
                        self.file_start_offset += size
                        self.processed_bytes = self.file_start_offset
                        self.skipped_count += 1
                        self.skipped_bytes += size
                        task_log.update(orig_rel, "skipped", size, 0, "续传跳过(上次已完成)",
                                        remote_rel=eff_rel)
                        self.log_queue.put(f"  ⊙ 已完成(跳过): {orig_rel}\n")
                        continue

                    rename_note = f"  (原名: {orig_rel})" if eff_rel != orig_rel else ""
                    self.current_file = eff_rel
                    self.log_queue.put(f"▶ 上传: {eff_rel}{rename_note}  ({format_size(size)})\n")

                    # 重名检查：跳过已存在
                    if remote_name in existing_names:
                        self.file_start_offset += size
                        self.skipped_count += 1
                        self.skipped_bytes += size
                        self.processed_bytes = self.file_start_offset
                        task_log.update(orig_rel, "skipped", size, 0, "云端已存在",
                                        remote_rel=eff_rel)
                        self.log_queue.put(f"  ⊙ 已存在，跳过: {eff_rel}\n")
                        continue

                    # 上传（带自动重试）
                    self.processed_bytes = self.file_start_offset
                    attempts = 0
                    last_detail = ""
                    success = False
                    while attempts <= RETRY_MAX:
                        if self.cancelled:
                            break
                        attempts += 1
                        code, detail = self.upload_file_real(
                            abspath, folder_id, callback=self.upload_callback, remote_name=remote_name
                        )
                        last_detail = detail
                        if code == LanZouClient.SUCCESS:
                            success = True
                            break
                        kind, reason = classify_error(code, detail)
                        if kind == "permanent":
                            self.log_queue.put(f"  ✗ 永久错误，放弃重试: {eff_rel}  ({detail})\n")
                            break
                        # 瞬时错误：指数退避后重试
                        if attempts <= RETRY_MAX:
                            delay = min(RETRY_MAX_DELAY, RETRY_BASE_DELAY * (2 ** (attempts - 1)))
                            delay += random.uniform(0, 1.5)
                            self.log_queue.put(
                                f"  ↻ 第 {attempts} 次重试 {eff_rel}（{reason}，{delay:.0f}s 后）\n"
                            )
                            self._sleep(delay)

                    if success:
                        self.uploaded_count += 1
                        self.uploaded_bytes += size
                        task_log.update(orig_rel, "success", size, attempts, "",
                                        remote_rel=eff_rel)
                        existing_names.add(remote_name)  # 本批后续文件重名判定即时更新
                        self.log_queue.put(f"  ✓ 完成: {eff_rel}（尝试 {attempts} 次）\n")
                    else:
                        self.failed_count += 1
                        task_log.update(orig_rel, "failed", size, attempts, last_detail,
                                        remote_rel=eff_rel)
                        self.log_queue.put(f"  ✗ 上传失败 (尝试 {attempts} 次): {eff_rel}  — {last_detail}\n")
                    self.file_start_offset += size
                    self.processed_bytes = self.file_start_offset
                    task_log.save()
                    # 文件间隔，降低被限流概率
                    if not success and not self.cancelled:
                        self._sleep(INTER_FILE_DELAY)

                # 批次之间随机停顿(2~10s)，降低限流概率；停顿不计入平均速度
                if bi + BATCH_SIZE < len(group) and not self.cancelled:
                    pause = random.uniform(BATCH_PAUSE_MIN, BATCH_PAUSE_MAX)
                    self.log_queue.put(f"  ⏸ 第 {batch_no} 批完成，随机停顿 {pause:.0f}s 后继续...\n")
                    self._sleep(pause)

        # 收尾
        self.running = False
        self.current_file = ""
        task_log.finish()
        task_log.save()
        # 记录本次任务，供下次断点续传（仅当日志功能开启时）
        if task_log.path is not None:
            self.config["last_task"] = {
                "folder": list(self.local_items),
                "target_id": self.upload_root_id,
                "path": task_log.path,
            }
            try:
                with open(CONFIG_PATH, "w", encoding="utf-8") as cf:
                    json.dump(self.config, cf, ensure_ascii=False, indent=2)
            except Exception:
                pass

        summary = (
            f"\n上传结束：成功 {self.uploaded_count} 个 / {format_size(self.uploaded_bytes)}，"
            f"跳过 {self.skipped_count} 个，失败 {self.failed_count} 个。\n"
        )
        if task_log.path is not None:
            summary += f"任务日志: {task_log.path}\n"
        if self.failed_count:
            if task_log.path is not None:
                summary += (
                    f"⚠ 有 {self.failed_count} 个文件未成功。\n"
                    f"任务日志已保存到 logs/ 目录（点主界面「日志」按钮可打开）。\n"
                    f"保持所选目录与目标不变，再次点击「开始上传」即可自动断点续传/重试这些文件。\n"
                )
            else:
                summary += (
                    f"⚠ 有 {self.failed_count} 个文件未成功。\n"
                    f"（当前未开启上传日志，无法记录详情与自动续传；如需记录请在「设置」中开启「开启上传日志功能」。）\n"
                )
        self.log_queue.put(summary)
        self._pending_popup = (summary, self.cancelled)
        self.root.after(0, self.refresh_resume_hint)

    def _sleep(self, secs):
        """可被取消的睡眠；累计实际停顿时长(不计入平均速度)。"""
        end = time.time() + secs
        slept = 0.0
        while time.time() < end:
            if self.cancelled:
                return
            step = min(0.2, end - time.time())
            time.sleep(step)
            slept += step
        self.paused_duration = getattr(self, "paused_duration", 0.0) + slept

    def cancel_upload(self):
        if self.running:
            self.cancelled = True
            self.log_queue.put("正在取消（将在当前文件结束后停止）...\n")

    # ====================== 日志查看 / 断点续传提示 ======================
    def open_in_finder(self, path):
        """用系统文件管理器打开文件/目录（文件会定位到所在目录）。"""
        if not path or not os.path.exists(path):
            messagebox.showwarning("无日志", f"未找到：{path}")
            return
        try:
            if sys.platform == "darwin":
                if os.path.isfile(path):
                    subprocess.run(["open", "-R", path])
                else:
                    subprocess.run(["open", path])
            elif sys.platform == "win32":
                if os.path.isfile(path):
                    subprocess.run(["explorer", "/select,", path])
                else:
                    subprocess.run(["explorer", path])
            else:
                subprocess.run(["xdg-open", path])
        except Exception as e:
            messagebox.showerror("打开失败", f"无法打开：{e}")

    def open_logs_dir(self):
        """打开任务日志所在目录（logs/）。"""
        os.makedirs(LOGS_DIR, exist_ok=True)
        self.open_in_finder(LOGS_DIR)

    def open_last_log(self):
        """在日志查看窗口中定位上次任务日志（若有），否则打开查看窗口。"""
        lt = self.config.get("last_task")
        p = lt.get("path") if isinstance(lt, dict) else None
        self.open_log_viewer(preset_path=p if (p and os.path.exists(p)) else None)

    def list_recent_logs(self):
        """返回 [(显示名, 路径), ...]，按修改时间倒序。"""
        if not os.path.isdir(LOGS_DIR):
            return []
        items = []
        for fn in os.listdir(LOGS_DIR):
            if not fn.startswith("task_") or not fn.endswith(".json"):
                continue
            p = os.path.join(LOGS_DIR, fn)
            try:
                st = os.path.getmtime(p)
                with open(p, encoding="utf-8") as f:
                    d = json.load(f)
            except Exception:
                continue
            files = d.get("files", {})
            total = d.get("total", len(files))
            failed = sum(1 for e in files.values() if e.get("status") == "failed")
            start = (d.get("start_time") or "").replace("T", " ")
            lf = d.get("local_folder", "?")
            if isinstance(lf, list):
                lf = lf[0] if lf else "?"
            fol = os.path.basename(lf or "?")
            label = f"{start}  ·  {fol}  ·  共{total}/失败{failed}"
            items.append((label, p, st))
        items.sort(key=lambda x: x[2], reverse=True)
        return [(label, p) for label, p, _ in items]

    def open_log_viewer(self, preset_path=None):
        """日志查看窗口：下拉选择最近日志，下方展示整理后的内容。"""
        logs = self.list_recent_logs()
        if not logs:
            messagebox.showinfo("无日志", "logs/ 目录中还没有任何任务日志。")
            return

        win = tk.Toplevel(self.root)
        win.title("任务日志查看")
        win.transient(self.root)
        try:
            self._apply_icon(win)
        except Exception:
            pass
        win.geometry("680x560")

        # 顶部：选择日志
        top = ttk.Frame(win)
        top.pack(fill="x", padx=12, pady=(12, 4))
        ttk.Label(top, text="选择日志:").pack(side="left", padx=(0, 6))
        names = [n for n, _ in logs]
        paths = [p for _, p in logs]
        cb = ttk.Combobox(top, values=names, state="readonly")
        cb.pack(side="left", fill="x", expand=True)
        idx = 0
        if preset_path and preset_path in paths:
            idx = paths.index(preset_path)
        cb.current(idx)

        # 中部：整理后的日志内容
        mid = ttk.LabelFrame(win, text="日志内容")
        mid.pack(fill="both", expand=True, padx=12, pady=4)
        tw = scrolledtext.ScrolledText(mid, wrap="word", state="normal")
        tw.pack(fill="both", expand=True, padx=6, pady=6)

        # 底部：操作按钮
        bot = ttk.Frame(win)
        bot.pack(fill="x", padx=12, pady=(4, 12))
        self._viewer_current_path = paths[idx]
        retry_btn = ttk.Button(bot, text="🔄 重试该日志未成功文件",
                               command=lambda: self._viewer_retry(win))
        retry_btn.pack(side="right", padx=(6, 0))
        ttk.Button(bot, text="📂 打开日志目录", command=self.open_logs_dir).pack(side="right")
        ttk.Button(bot, text="关闭", command=win.destroy).pack(side="left")

        def on_select(ev=None):
            i = cb.current()
            if i < 0:
                return
            self._viewer_current_path = paths[i]
            self._render_log_text(tw, paths[i], retry_btn)

        cb.bind("<<ComboboxSelected>>", on_select)
        self._render_log_text(tw, paths[idx], retry_btn)

    def _render_log_text(self, tw, path, retry_btn):
        """把日志整理为：基本信息 → 失败列表 → 成功列表，并写入文本控件。"""
        try:
            with open(path, encoding="utf-8") as f:
                d = json.load(f)
        except Exception as e:
            tw.delete("1.0", tk.END)
            tw.insert(tk.END, f"日志读取失败: {e}")
            retry_btn.config(state="disabled")
            return
        files = d.get("files", {})
        total = d.get("total", len(files))
        success = sum(1 for e in files.values() if e.get("status") == "success")
        skipped = sum(1 for e in files.values() if e.get("status") == "skipped")
        failed = sum(1 for e in files.values() if e.get("status") == "failed")
        L = []
        L.append("===== 基本信息 =====")
        L.append(f"任务开始 : {d.get('start_time', '-')}")
        L.append(f"本地目录 : {d.get('local_folder', '-')}")
        L.append(f"上传目标 : {d.get('target_path', '-')}  (id={d.get('target_id', '-')})")
        if d.get("dir_description"):
            L.append(f"目录描述 : {d.get('dir_description')}")
        if d.get("end_time"):
            L.append(f"任务结束 : {d.get('end_time')}（用时 {d.get('duration_sec', '?')} 秒）")
        L.append(f"文件总数 : {total}")
        L.append(f"成功 {success} 个，跳过(已存在/续传) {skipped} 个，失败 {failed} 个")
        L.append("")
        L.append(f"===== 失败文件列表（{failed}）=====")
        if failed == 0:
            L.append("（无）")
        else:
            for rel, e in files.items():
                if e.get("status") == "failed":
                    L.append(f"  ✗ {rel}")
                    if e.get("error"):
                        L.append(f"      失败原因: {e['error']}")
        L.append("")
        L.append(f"===== 成功文件列表（{success}）=====")
        if success == 0:
            L.append("（无）")
        else:
            for rel, e in files.items():
                if e.get("status") == "success":
                    L.append(f"  ✓ {rel}")
        tw.delete("1.0", tk.END)
        tw.insert(tk.END, "\n".join(L))
        retry_btn.config(state="normal" if failed > 0 else "disabled")

    def _viewer_retry(self, win):
        p = getattr(self, "_viewer_current_path", None)
        if not p:
            return
        win.destroy()
        self.retry_failed_from_log(p)

    def retry_failed_from_log(self, log_path):
        """重新上传某份日志中状态为「失败」的文件（写回同一日志）。"""
        if self.running:
            messagebox.showinfo("正在上传", "请等待当前上传任务完成后再重试。")
            return
        raw = self.config.get("cookie", "")
        if not raw:
            messagebox.showwarning("未登录", "请先在「设置」中填写有效 Cookie。")
            return
        if not self.cookie_valid:
            ok, msg = self.do_login(raw)
            if not ok:
                messagebox.showerror("Cookie 无效", msg + "\n请到「设置」中重新填写并检测。")
                return
        try:
            log = TaskLog.load(log_path)
        except Exception as e:
            messagebox.showerror("日志读取失败", str(e))
            return
        d = log.data
        base_id = int(d.get("target_id", -1))
        if base_id < 0:
            messagebox.showerror("日志无效", "该日志缺少有效的上传目标 id，无法重试。")
            return
        local_folder = d.get("local_folder", "")
        if isinstance(local_folder, list):
            local_folder = local_folder[0] if local_folder else ""
        failed = [r for r, e in d.get("files", {}).items() if e.get("status") == "failed"]
        if not failed:
            messagebox.showinfo("无需重试", "该日志中没有失败的文件。")
            return

        # 组装待重传文件列表（远程相对路径沿用日志中记录的 remote_rel）
        files = []
        missing = []
        for rel in failed:
            abspath = os.path.join(local_folder, rel)
            if os.path.isfile(abspath):
                size = os.path.getsize(abspath)
                remote_rel = d["files"][rel].get("remote_rel") or rel
                files.append({"rel": rel, "abspath": abspath, "size": size, "target_rel": remote_rel})
            else:
                missing.append(rel)
        if not files:
            messagebox.showinfo(
                "无可上传文件",
                "失败文件对应的本地源文件均已不存在，无法重试。\n（如已移动/删除，请重新选择目录上传）",
            )
            return

        # 复用原任务的上传目标，直接写回同一日志文件
        self.local_folder = local_folder
        self.local_items = [local_folder] if local_folder else []
        self.local_path_var.set(self._format_local_display())
        self.upload_root_id = base_id
        self.upload_root_path = d.get("target_path", "")
        self.target_path_var.set(self.upload_root_path + f"  (id={self.upload_root_id})")
        self.last_file_list = files
        self.total_files = len(files)
        self.total_bytes = sum(f["size"] for f in files)
        self.file_start_offset = 0
        self.processed_bytes = 0
        self.uploaded_count = 0
        self.uploaded_bytes = 0
        self.skipped_count = 0
        self.skipped_bytes = 0
        self.failed_count = 0
        self.current_file = ""
        self.start_time = time.time()
        self.paused_duration = 0.0
        self.samples.clear()
        self._last_sample_t = 0.0
        self._pending_popup = None
        self.cancelled = False
        self.running = True
        self.prev_status = {}
        self.task_log = log

        if missing:
            self.log_queue.put(
                f"注：{len(missing)} 个失败文件本地源已不存在，已跳过重传。\n"
            )
        self.log_queue.put(
            f"开始重试：日志 {os.path.basename(log_path)}，"
            f"共 {self.total_files} 个失败文件待重传。\n"
        )
        self.refresh_controls()
        t = threading.Thread(target=self.run_upload, daemon=True)
        t.start()

    def refresh_resume_hint(self):
        """若上次任务有未成功文件，在界面顶部显示断点续传提示横幅；否则隐藏。"""
        # 日志功能关闭时，不写日志、也无断点续传记录，故隐藏横幅
        if not self.enable_log_var.get():
            if self.resume_hint.winfo_ismapped():
                self.resume_hint.pack_forget()
            return
        lt = self.config.get("last_task")
        failed = 0
        folder = ""
        if isinstance(lt, dict):
            p = lt.get("path")
            if p and os.path.exists(p):
                try:
                    with open(p, encoding="utf-8") as f:
                        d = json.load(f)
                    failed = sum(1 for e in d.get("files", {}).values()
                                 if e.get("status") == "failed")
                    folder = lt.get("folder", "")
                except Exception:
                    pass
        if failed > 0:
            self.resume_hint.config(
                text=f"⚠ 上次任务有 {failed} 个文件未成功（目录：{folder or '未知'}）。\n"
                     f"保持所选目录与目标不变，直接点击「开始上传」即可自动断点续传/重试。"
                     f"点击此处可打开该任务日志。"
            )
            if not self.resume_hint.winfo_ismapped():
                self.resume_hint.pack(fill="x", padx=12, pady=(0, 4))
            self.resume_hint.config(cursor="hand2")
        else:
            if self.resume_hint.winfo_ismapped():
                self.resume_hint.pack_forget()

    # ====================== UI 刷新 ======================
    def update_ui(self):
        try:
            while True:
                line = self.log_queue.get_nowait()
                self.log_text.insert(tk.END, line)
                self.log_text.see(tk.END)
        except queue.Empty:
            pass

        if self._pending_popup is not None and not self.running:
            summary, cancelled = self._pending_popup
            self._pending_popup = None
            if cancelled:
                messagebox.showinfo("已取消", summary)
            else:
                messagebox.showinfo("上传完成", summary)

        if self.running or self.total_files:
            done_count = self.uploaded_count + self.skipped_count + self.failed_count
            remaining_count = max(0, self.total_files - done_count)
            remaining_bytes = max(0, self.total_bytes - self.processed_bytes)
            pct = (self.processed_bytes / self.total_bytes * 100) if self.total_bytes else 0

            self.current_var.set("正在上传: " + (self.current_file or "—"))
            self.uploaded_var.set(f"已上传 {self.uploaded_count} / 跳过 {self.skipped_count} / 失败 {self.failed_count}")
            self.remaining_var.set(f"未上传: {remaining_count} 个 / {format_size(remaining_bytes)}")
            self.progress_var.set(f"进度: {pct:.1f}%")
            self.pb["maximum"] = self.total_bytes
            self.pb["value"] = self.processed_bytes

            now = time.time()
            elapsed = self._eff_elapsed()       # 已扣除停顿的有效时长
            if elapsed <= 0:
                speed = 0.0
            elif elapsed < 30:
                speed = self.processed_bytes / elapsed
            else:
                cut = elapsed - 30
                while self.samples and self.samples[0][0] < cut:
                    self.samples.popleft()
                if len(self.samples) >= 2:
                    t0, b0 = self.samples[0]
                    speed = (self.processed_bytes - b0) / (elapsed - t0)
                else:
                    speed = self.processed_bytes / elapsed
            self.speed_var.set(f"速度: {format_size(speed)}/s")

            if not self.running and self.total_files:
                self.current_var.set("空闲")
                self.speed_var.set("速度: —")
                self.refresh_controls()

        self.root.after(250, self.update_ui)

    # ====================== 控件可用性 ======================
    def refresh_controls(self):
        can_start = self.cookie_valid and bool(self.local_items)
        state = "disabled" if self.running else "normal"
        self.start_btn.config(state=state if can_start else "disabled")
        self.cancel_btn.config(state="normal" if self.running else "disabled")
        self.browse_btn.config(state="normal" if (self.cookie_valid and not self.running) else "disabled")
        self.local_btn.config(state=state)
        self.settings_btn.config(state=state)
        self.update_cookie_btn()
        self.update_log_btn_visibility()

    def update_log_btn_visibility(self):
        """「日志」按钮仅在「开启上传日志功能」启用时显示。"""
        if not hasattr(self, "log_btn"):
            return
        if self.enable_log_var.get():
            self.log_btn.grid()          # 恢复之前记录的 grid 布局
        else:
            self.log_btn.grid_remove()   # 隐藏但保留 grid 配置

    # ====================== 构建界面 ======================
    def _fit_window_height(self):
        """按内容自动计算窗口高度：保证底部按钮完整可见，多余空间由日志区吸收，避免大片空白。"""
        self.root.update_idletasks()
        # 日志区为 expand 时会占满剩余空间，导致测不到真实所需高度；
        # 先临时取消 expand 测量自然高度，再恢复。
        self.f_log.pack_configure(expand=False)
        self.root.update_idletasks()
        need_h = self.root.winfo_reqheight()
        self.f_log.pack_configure(expand=True)
        # 留少量余量，避免断点续传横幅出现时挤压日志区
        fit_h = need_h + 60
        self.root.geometry(f"390x{fit_h}")
        self.root.minsize(360, need_h)

    def build_ui(self):
        # 头部
        header = ttk.Frame(self.root)
        header.pack(fill="x", padx=12, pady=(12, 4))
        ttk.Label(header, text="蓝奏云批量上传", font=("PingFang SC", "15", "bold"),
                  foreground="#1f6feb").pack(anchor="center")
        ttk.Label(header, text="保持目录结构 · 自动重试 · 断点续传",
                  font=("PingFang SC", "9"), foreground="#8a8a8a").pack(anchor="center")

        # 断点续传提示横幅（默认隐藏，detect 到上次失败任务后显示）
        self.resume_hint = tk.Label(
            self.root, text="", bg="#fff7e6", fg="#a35b00",
            font=("PingFang SC", "9"), wraplength=360, justify="left",
            padx=8, pady=4, anchor="w",
        )
        self.resume_hint.pack_forget()
        self.resume_hint.bind("<Button-1>", lambda e: self.open_last_log())

        # 本地来源
        f_src = ttk.LabelFrame(self.root, text="本地来源")
        f_src.pack(fill="x", padx=12, pady=4)
        row1 = ttk.Frame(f_src)
        row1.pack(fill="x", padx=8, pady=(6, 2))
        self.local_btn = ttk.Button(row1, text="选择上传文件/文件夹", command=self.select_local_sources)
        self.local_btn.pack(side="left")
        self.local_path_var = tk.StringVar(value=self._format_local_display())
        ttk.Label(f_src, textvariable=self.local_path_var, foreground="#555",
                  wraplength=330, justify="left").pack(anchor="w", padx=8, pady=(0, 2))
        self.dir_desc_var = tk.StringVar(value=self.dir_description or "（无）")
        self.dir_desc_row = ttk.Frame(f_src)
        self.dir_desc_row.pack(fill="x", padx=8, pady=(0, 6))
        ttk.Label(self.dir_desc_row, text="目录描述:", foreground="#555").pack(side="left")
        ttk.Label(self.dir_desc_row, textvariable=self.dir_desc_var, foreground="#555",
                  wraplength=300, justify="left").pack(side="left", padx=(4, 0))
        self._update_desc_visibility()

        # 云盘目标 + 设置
        f_tgt = ttk.LabelFrame(self.root, text="云盘目标")
        f_tgt.pack(fill="x", padx=12, pady=4)
        row2 = ttk.Frame(f_tgt)
        row2.pack(fill="x", padx=8, pady=(6, 2))
        self.browse_btn = ttk.Button(row2, text="浏览目标云目录", command=self.browse_target)
        self.browse_btn.pack(side="left")
        # 「云盘 Cookie」按钮：文字显示登录有效性（绿/红），点击打开 Cookie 填写窗口
        self.cookie_btn = tk.Button(row2, text="Cookie 检测中…", fg="#555555",
                                    font=("PingFang SC", "10"), command=self.open_cookie_window)
        self.cookie_btn.pack(side="right")
        self.target_path_var = tk.StringVar(value=self.target_path + f"  (id={self.target_id})")
        ttk.Label(f_tgt, textvariable=self.target_path_var, foreground="#555",
                  wraplength=330, justify="left").pack(anchor="w", padx=8, pady=(0, 6))

        # 进度
        f_st = ttk.LabelFrame(self.root, text="进度")
        f_st.pack(fill="x", padx=12, pady=4)
        grid = ttk.Frame(f_st)
        grid.pack(fill="x", padx=8, pady=6)
        grid.columnconfigure(1, weight=1)
        self.current_var = tk.StringVar(value="空闲")
        self.uploaded_var = tk.StringVar(value="已上传 0 / 跳过 0 / 失败 0")
        self.remaining_var = tk.StringVar(value="未上传: 0 个 / 0 B")
        self.speed_var = tk.StringVar(value="速度: —")
        self.progress_var = tk.StringVar(value="0.0%")
        ttk.Label(grid, textvariable=self.current_var).grid(row=0, column=0, columnspan=2, sticky="w", pady=1)
        ttk.Label(grid, textvariable=self.uploaded_var).grid(row=1, column=0, sticky="w", pady=1)
        ttk.Label(grid, textvariable=self.remaining_var).grid(row=1, column=1, sticky="w", pady=1)
        ttk.Label(grid, textvariable=self.speed_var).grid(row=2, column=0, sticky="w", pady=1)
        ttk.Label(grid, textvariable=self.progress_var).grid(row=2, column=1, sticky="e", pady=1)
        self.pb = ttk.Progressbar(f_st, orient="horizontal", mode="determinate", maximum=1)
        self.pb.pack(fill="x", padx=8, pady=(0, 8))

        # 日志
        self.f_log = ttk.LabelFrame(self.root, text="日志")
        self.f_log.pack(fill="both", expand=True, padx=12, pady=4)
        self.log_text = scrolledtext.ScrolledText(self.f_log, height=6, state="normal", wrap="word")
        self.log_text.pack(fill="both", expand=True, padx=6, pady=6)

        # 底部按钮：设置（最左）→ 任务日志，中间弹性占位，开始上传 / 取消（最右）
        f_bot = ttk.Frame(self.root)
        f_bot.pack(fill="x", padx=12, pady=(2, 10))
        f_bot.columnconfigure(0, weight=0)   # 设置（最左）
        f_bot.columnconfigure(1, weight=0)   # 任务日志
        f_bot.columnconfigure(2, weight=1)   # 中间弹性占位（把左右两组分开）
        f_bot.columnconfigure(3, weight=0)   # 开始上传
        f_bot.columnconfigure(4, weight=0)   # 取消
        self.settings_btn = ttk.Button(f_bot, text="设置", command=self.open_settings)
        self.settings_btn.grid(row=0, column=0, padx=(0, 4), sticky="w")
        self.log_btn = ttk.Button(f_bot, text="日志", command=self.open_log_viewer)
        self.log_btn.grid(row=0, column=1, padx=(0, 4), sticky="w")
        self.update_log_btn_visibility()
        self.start_btn = ttk.Button(f_bot, text="开始上传", command=self.start_upload)
        self.start_btn.grid(row=0, column=3, padx=4)
        self.cancel_btn = ttk.Button(f_bot, text="取消", command=self.cancel_upload)
        self.cancel_btn.grid(row=0, column=4, padx=(4, 0))


def rel_parent_parts(rel):
    """返回相对路径中"目录部分"的分段列表（不含文件名）。"""
    d = os.path.dirname(rel)
    if not d or d == ".":
        return []
    return d.split(os.sep)


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
