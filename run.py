#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""山东大学通知监控

每次运行：抓取各站点通知列表 -> 与 state.db 比对 -> 把新通知发到邮箱。
只依赖 Python 标准库，无需 pip 安装任何东西。

用法:
    py -3 run.py              正常抓取并发送
    py -3 run.py --dry-run    只抓取、打印，不发邮件、不写库
    py -3 run.py --test-email 发一封测试邮件
"""

import difflib
import gzip
import hashlib
import html as htmllib
import http.cookiejar
import json
import os
import random
import re
import smtplib
import socket
import sqlite3
import ssl
import sys
import time
import getpass
from datetime import date, datetime, timedelta, timezone
from email.message import EmailMessage
from email.utils import formataddr, formatdate
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urljoin, urlsplit, urlunsplit
from urllib.request import (Request, build_opener, ProxyHandler,
                            HTTPCookieProcessor)

# 打包成 exe 后 __file__ 指向临时解包目录，配置/数据库要跟着 exe 走
BASE = (os.path.dirname(sys.executable) if getattr(sys, "frozen", False)
        else os.path.dirname(os.path.abspath(__file__)))
CONFIG_PATH = os.path.join(BASE, "config.json")
DB_PATH = os.path.join(BASE, "state.db")
LOG_PATH = os.path.join(BASE, "log.txt")

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")

DEFAULT_CONFIG = {
    "sources": [
        {
            "name": "山东大学 通知公告",
            "url": "https://www.sdu.edu.cn/tzgg.htm",
            "detail": False,
        },
        {
            "name": "山东大学本科生院 通知公告",
            "url": "https://www.bkjx.sdu.edu.cn/index/tzgg.htm",
            "detail": True,
        },
        {
            "name": "山东大学（青岛）通知公告",
            "url": "https://www.qdxq.sdu.edu.cn/xwzx1/tzyg/tzgg.htm",
            "detail": True,
        },
        {
            "name": "SDUQDCS学生会",
            "type": "wechat",
            "account": "SDUQDCS学生会",
            "wechat_id": "SDUQDJSJXSH",
            "pages": 5,
            "detail": False,
        },
    ],
    "email": {
        "smtp_host": "",
        "smtp_port": 465,
        "ssl": True,
        "starttls": True,
        "username": "",
        "password": "",
        "from_name": "山大通知助手",
        "to": "",
    },
    # 第一次运行（还没有历史记录）时，只推送最近 N 天的通知，避免一次性刷屏
    "first_run_days": 7,
    # 微信公众号走的是搜索索引，历史文章会被反复翻出来；
    # 超过这个天数的文章只入库、不推送（每轮都生效，不只是首轮）
    "wechat_max_age_days": 7,
    # 每轮每个站点最多推送多少条
    "max_items_per_source": 20,
    # 没有新通知时是否也发邮件
    "send_when_empty": False,
    # 是否使用系统代理。校园网直连，默认 False
    "use_system_proxy": False,
}


# ---------------------------------------------------------------- 基础工具

def log(msg):
    line = "[%s] %s" % (datetime.now().strftime("%Y-%m-%d %H:%M:%S"), msg)
    print(line)
    try:
        if os.path.exists(LOG_PATH) and os.path.getsize(LOG_PATH) > 512 * 1024:
            with open(LOG_PATH, "r", encoding="utf-8", errors="replace") as f:
                tail = f.readlines()[-1000:]
            with open(LOG_PATH, "w", encoding="utf-8") as f:
                f.writelines(tail)
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except OSError:
        pass


def load_config():
    if not os.path.exists(CONFIG_PATH):
        save_config(DEFAULT_CONFIG)
        log("已生成配置文件 config.json")
        return json.loads(json.dumps(DEFAULT_CONFIG))
    with open(CONFIG_PATH, "r", encoding="utf-8-sig") as f:
        cfg = json.load(f)
    merged = json.loads(json.dumps(DEFAULT_CONFIG))
    merged.update(cfg)
    merged["email"] = dict(DEFAULT_CONFIG["email"], **cfg.get("email", {}))
    return merged


def save_config(cfg):
    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)


_OPENER = build_opener(ProxyHandler({}))


def http_get(url, timeout=25, retries=2):
    last = None
    for attempt in range(retries + 1):
        try:
            req = Request(url, headers={
                "User-Agent": UA,
                "Accept": "text/html,application/xhtml+xml,*/*;q=0.8",
                "Accept-Language": "zh-CN,zh;q=0.9",
                "Accept-Encoding": "gzip",
                "Connection": "close",
            })
            with _OPENER.open(req, timeout=timeout) as r:
                raw = r.read()
                charset = r.headers.get_content_charset() or "utf-8"
            if raw[:2] == b"\x1f\x8b":
                raw = gzip.decompress(raw)
            for enc in (charset, "utf-8", "gb18030"):
                try:
                    return raw.decode(enc)
                except (UnicodeDecodeError, LookupError):
                    continue
            return raw.decode("utf-8", "replace")
        except (HTTPError, URLError, socket.timeout, OSError) as e:
            last = e
            if attempt < retries:
                time.sleep(1.5 * (attempt + 1))
    raise last


def strip_tags(s):
    s = re.sub(r"<(script|style)\b.*?</\1>", " ", s or "", flags=re.S | re.I)
    s = re.sub(r"<[^>]+>", " ", s)
    s = htmllib.unescape(s)
    return re.sub(r"\s+", " ", s).strip()


# ---------------------------------------------------------------- 解析

LI_RE = re.compile(r"<li\b[^>]*>(.*?)</li>", re.S | re.I)
HREF_RE = re.compile(r'href\s*=\s*["\']([^"\']+)["\']', re.I)

P_YMD = re.compile(r"(20\d{2})\s*[年./\-]\s*(\d{1,2})\s*[月./\-]\s*(\d{1,2})")
P_MDY = re.compile(r"(?<!\d)(\d{1,2})\.(\d{1,2})\s*(?:</?[^>]*>\s*)?(20\d{2})")
P_DM = re.compile(r"(?<!\d)(\d{1,2})\s*(?:\d{2}\s*)?(\d{1,2})\s*月")

TITLE_PATTERNS = [
    r"<h4[^>]*>(.*?)</h4>",
    r"<h5[^>]*>(.*?)</h5>",
    r"<h3[^>]*>(.*?)</h3>",
    r'<p[^>]*class="[^"]*title[^"]*"[^>]*>(.*?)</p>',
    r'<div[^>]*class="[^"]*title[^"]*"[^>]*>(.*?)</div>',
]


def _fix_year(m, d, today):
    """列表页常常只有“月日”，年份缺失。按“不超过今天”推断。"""
    year = today.year
    if (m, d) > (today.month, today.day):
        year -= 1
    return date(year, m, d)


def extract_date(chunk, today):
    """返回 (日期, 年份是否确定)。列表页只有“月日”时年份靠推断。"""
    head = strip_tags(chunk)[:80]
    m = P_YMD.search(head)
    if m:
        try:
            return date(int(m.group(1)), int(m.group(2)), int(m.group(3))), True
        except ValueError:
            pass
    m = P_MDY.search(head)
    if m:
        try:
            return date(int(m.group(3)), int(m.group(1)), int(m.group(2))), True
        except ValueError:
            pass
    m = P_DM.search(head)
    if m:
        try:
            return _fix_year(int(m.group(2)), int(m.group(1)), today), False
        except ValueError:
            pass
    return None, False


def extract_title(chunk):
    for pat in TITLE_PATTERNS:
        m = re.search(pat, chunk, re.S | re.I)
        if m:
            t = strip_tags(m.group(1))
            if len(t) >= 4:
                return t
    m = re.search(r"<a\b[^>]*>(.*?)</a>", chunk, re.S | re.I)
    if m:
        t = strip_tags(m.group(1))
        t = re.sub(r"^\s*(20\d{2}\s*[年./\-]\s*)?\d{1,2}\s*[月./\-]\s*\d{1,2}\s*日?\s*", "", t)
        t = re.sub(r"^\s*\d{1,2}\s*\d{1,2}\s*月\s*", "", t)
        t = re.sub(r"^\s*20\d{2}\s*", "", t)
        t = re.sub(r"\s*20\d{2}[-./]\d{1,2}[-./]\d{1,2}\s*$", "", t)
        if len(t) >= 4:
            return t
    return None


def extract_link(chunk, base):
    for m in HREF_RE.finditer(chunk):
        href = htmllib.unescape(m.group(1)).strip()
        if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
            continue
        return canonical(urljoin(base, href))
    return None


def title_text(title):
    t = re.sub(r"\s*20\d{2}[-./]\d{1,2}[-./]\d{1,2}\s*$", "", title or "")
    return re.sub(r"[\s\W_]+", "", t)


def title_key(title, d):
    """同一篇文章被不同栏目转载时，标题和日期一致。"""
    t = title_text(title)
    if not t:
        return None
    ds = d.isoformat() if hasattr(d, "isoformat") else (d or "")
    return t[:80] + "|" + ds


def canonical(url):
    parts = urlsplit(url)
    return urlunsplit((parts.scheme, parts.netloc.lower(), parts.path or "/",
                       parts.query, ""))


def item_key(item):
    """微信公众号的链接带一次性 token，不能用 URL 去重。"""
    return item.get("key") or item["url"]


def parse_items(html, base_url, today):
    items, seen = [], set()
    for chunk in LI_RE.findall(html):
        d, exact = extract_date(chunk, today)
        if not d:
            continue
        title = extract_title(chunk)
        link = extract_link(chunk, base_url)
        if not title or not link:
            continue
        if link in seen:
            continue
        seen.add(link)
        items.append({"title": title, "url": link, "date": d, "exact": exact})
    items.sort(key=lambda x: x["date"], reverse=True)
    return items


DETAIL_DATE = re.compile(
    r"(?:日期|发布时间|发布日期|时间)\s*[:：]?\s*"
    r"(20\d{2})\s*[年./\-]\s*(\d{1,2})\s*[月./\-]\s*(\d{1,2})")


def enrich_from_detail(url):
    """列表标题被截断时，回详情页取完整标题和精确日期。失败返回 (None, None)。"""
    try:
        html = http_get(url, timeout=20, retries=1)
    except Exception:
        return None, None
    title, d = None, None
    m = re.search(r"<h1[^>]*>(.*?)</h1>", html, re.S | re.I)
    if m:
        title = strip_tags(m.group(1))
    if not title or len(title) < 4:
        m = re.search(r"<title[^>]*>(.*?)</title>", html, re.S | re.I)
        if m:
            title = re.sub(r"\s*[-_|]\s*山东大学.*$", "", strip_tags(m.group(1))).strip()
    m = DETAIL_DATE.search(html)
    if m:
        try:
            d = date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        except ValueError:
            d = None
    return (title if title and len(title) >= 4 else None), d


# ---------------------------------------------------------------- 微信公众号

WECHAT_SEARCH = ("https://weixin.sogou.com/weixin?query=%s&s_from=input"
                 "&_sug_=n&type=2&page=%d&ie=utf8")
WECHAT_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
             "(KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36")
WECHAT_LIST_RE = re.compile(r'<ul[^>]*class="[^"]*news-list[^"]*"[^>]*>(.*?)</ul>', re.S | re.I)
WECHAT_LI_RE = re.compile(r"<li\b[^>]*>(.*?)</li>", re.S | re.I)
WECHAT_H3_RE = re.compile(r"<h3[^>]*>(.*?)</h3>", re.S | re.I)
WECHAT_LINK_RE = re.compile(r'href\s*=\s*["\']([^"\']+)["\']', re.I)
WECHAT_SOURCE_RE = re.compile(r'class="[^"]*all-time-y2[^"]*"[^>]*>(.*?)</span>', re.S | re.I)
WECHAT_SUMMARY_RE = re.compile(r'<p[^>]*class="[^"]*txt-info[^"]*"[^>]*>(.*?)</p>', re.S | re.I)
WECHAT_TS_RE = re.compile(r"timeConvert\('(\d{10})'\)")


class WeChatSession:
    """搜狗微信搜索需要带 Cookie 会话，否则 /link 会跳反爬页。"""

    def __init__(self):
        self.jar = http.cookiejar.CookieJar()
        self.opener = build_opener(ProxyHandler({}),
                                   HTTPCookieProcessor(self.jar))

    def get(self, url, referer=None, timeout=25, retries=2):
        # 只带 UA/Referer，是搜狗微信搜索最稳定的组合；
        # 额外的 Accept 头反而更容易触发反爬。
        headers = {"User-Agent": WECHAT_UA}
        if referer:
            headers["Referer"] = referer
        last = None
        for attempt in range(retries + 1):
            try:
                req = Request(url, headers=headers)
                with self.opener.open(req, timeout=timeout) as r:
                    raw = r.read()
                    charset = r.headers.get_content_charset() or "utf-8"
                if raw[:2] == b"\x1f\x8b":
                    raw = gzip.decompress(raw)
                text = None
                for enc in (charset, "utf-8", "gb18030"):
                    try:
                        text = raw.decode(enc)
                        break
                    except (UnicodeDecodeError, LookupError):
                        continue
                if text is None:
                    text = raw.decode("utf-8", "replace")

                # 搜狗有时回 200 + 验证码页，等一会儿再试一次
                if "/weixin?" in url and ("antispider" in text
                                          or "请输入验证码" in text):
                    last = RuntimeError("搜狗触发反爬验证")
                    if attempt < retries:
                        time.sleep(30)
                        continue
                    raise last
                return text
            except (HTTPError, URLError, socket.timeout, OSError) as e:
                last = e
                if attempt < retries:
                    time.sleep(2.0 * (attempt + 1))
        raise last


def _norm_name(s):
    return re.sub(r"\s+", "", s or "")


def parse_wechat_items(html, account, source_name):
    """解析搜狗微信搜索结果页，只保留目标公众号的文章。"""
    block = WECHAT_LIST_RE.search(html)
    if not block:
        if "antispider" in html or "验证码" in html:
            raise RuntimeError("搜狗触发反爬验证，请稍后重试")
        raise RuntimeError("搜狗页面结构异常（未找到文章列表）")

    items, seen = [], set()
    for chunk in WECHAT_LI_RE.findall(block.group(1)):
        h3 = WECHAT_H3_RE.search(chunk)
        if not h3:
            continue
        title = strip_tags(h3.group(1))
        if len(title) < 2:
            continue
        m = WECHAT_LINK_RE.search(h3.group(1))
        if not m:
            continue
        href = htmllib.unescape(m.group(1)).strip()
        if href.startswith("/"):
            href = "https://weixin.sogou.com" + href
        if not href:
            continue

        ts_m = WECHAT_TS_RE.search(chunk)
        if not ts_m:
            s2 = re.search(r'class="[^"]*s2[^"]*"[^>]*>(.*?)</span>',
                           chunk, re.S | re.I)
            ts_m = re.search(r"(\d{10})", s2.group(1)) if s2 else None
        if not ts_m:
            continue
        ts = int(ts_m.group(1))

        src_m = WECHAT_SOURCE_RE.search(chunk)
        src_name = strip_tags(src_m.group(1)) if src_m else ""
        if _norm_name(src_name) != _norm_name(account):
            continue

        # 搜狗时间戳是 UTC 秒；统一按北京时间转日期
        d = (datetime.fromtimestamp(ts, timezone.utc)
             + timedelta(hours=8)).date()
        summary = ""
        sm = WECHAT_SUMMARY_RE.search(chunk)
        if sm:
            summary = strip_tags(sm.group(1))

        key = "wechat:%s:%d:%s" % (
            account, ts,
            hashlib.sha1(title_text(title).encode("utf-8")).hexdigest()[:12])
        if key in seen:
            continue
        seen.add(key)
        items.append({
            "key": key,
            "title": title,
            "url": href,
            "sogou_url": href,
            "date": d,
            "exact": True,
            "summary": summary,
            "source": source_name,
            "wechat": True,
        })

    items.sort(key=lambda x: x["date"], reverse=True)
    return items


def resolve_wechat_url(session, link, referer):
    """把搜狗 /link 解析成 mp.weixin.qq.com 直链；失败返回 None。"""
    try:
        html = session.get(link, referer=referer, timeout=20, retries=1)
    except Exception:
        return None
    parts = re.findall(r"url\s*\+=\s*'([^']*)'", html)
    parts += re.findall(r'url\s*\+=\s*"([^"]*)"', html)
    direct = "".join(parts)
    return direct if "mp.weixin.qq.com" in direct else None


def enrich_wechat_links(items, session, referer, limit=5):
    """只给前几条新文章解析直链，减少搜狗请求次数。"""
    for it in items[:limit]:
        direct = resolve_wechat_url(session, it.get("sogou_url") or it["url"],
                                    referer)
        if direct:
            it["url"] = direct
        time.sleep(random.uniform(1.0, 2.0))


def fetch_wechat_source(src):
    """返回 (items, session, search_url)。"""
    name = src["name"]
    account = (src.get("account") or name).strip()
    queries = []
    for q in (src.get("wechat_id"), account):
        if q and q not in queries:
            queries.append(q)
    pages = max(1, min(int(src.get("pages", 3)), 5))
    session = WeChatSession()
    search_url = ""

    parsed, last_error = [], None
    for q in queries:
        query_items = []
        first_url = ""
        blocked = False
        for page in range(1, pages + 1):
            url = WECHAT_SEARCH % (quote(q), page)
            if page == 1:
                first_url = url
            try:
                html = session.get(url, referer="https://weixin.sogou.com/",
                                   retries=1)
            except Exception as e:
                blocked = "反爬" in str(e)
                if page == 1:
                    last_error = e
                    log("  搜索“%s”失败：%s" % (q, e))
                    break
                log("  第 %d 页失败：%s" % (page, e))
                break
            try:
                got = parse_wechat_items(html, account, name)
            except Exception as e:
                blocked = "反爬" in str(e)
                if page == 1:
                    last_error = e
                    log("  搜索“%s”失败：%s" % (q, e))
                    break
                log("  第 %d 页解析失败：%s" % (page, e))
                break
            query_items.extend(got)
            if not got:
                break
            if page < pages:
                time.sleep(random.uniform(1.2, 2.6))
        if query_items:
            parsed = query_items
            search_url = first_url
            break
        if blocked:
            break

    if not parsed:
        raise last_error or RuntimeError("没有解析到公众号文章")

    uniq, seen = [], set()
    for it in parsed:
        if it["key"] in seen:
            continue
        seen.add(it["key"])
        uniq.append(it)
    uniq.sort(key=lambda x: x["date"], reverse=True)
    return uniq, session, search_url


# ---------------------------------------------------------------- 数据库

SCHEMA = """
CREATE TABLE IF NOT EXISTS items(
    key        TEXT PRIMARY KEY,
    source     TEXT NOT NULL,
    title      TEXT NOT NULL,
    title_key  TEXT,
    url        TEXT NOT NULL,
    published  TEXT,
    first_seen TEXT
);
CREATE TABLE IF NOT EXISTS source_state(
    name        TEXT PRIMARY KEY,
    initialized INTEGER DEFAULT 0,
    last_ok     TEXT,
    fail_streak INTEGER DEFAULT 0
);
"""


def open_db():
    conn = sqlite3.connect(DB_PATH)
    conn.executescript(SCHEMA)
    cols = [r[1] for r in conn.execute("PRAGMA table_info(items)")]
    if "title_key" not in cols:                 # 旧库升级
        conn.execute("ALTER TABLE items ADD COLUMN title_key TEXT")
    conn.execute("CREATE INDEX IF NOT EXISTS idx_items_title ON items(title_key)")
    for k, t, pub in conn.execute(
            "SELECT key, title, published FROM items WHERE title_key IS NULL").fetchall():
        conn.execute("UPDATE items SET title_key=? WHERE key=?", (title_key(t, pub), k))
    conn.commit()
    return conn


def source_initialized(conn, name):
    row = conn.execute("SELECT initialized FROM source_state WHERE name=?", (name,)).fetchone()
    return bool(row and row[0])


def mark_source(conn, name, initialized):
    conn.execute(
        "INSERT INTO source_state(name, initialized, last_ok, fail_streak) VALUES(?,?,?,0) "
        "ON CONFLICT(name) DO UPDATE SET initialized=?, last_ok=?, fail_streak=0",
        (name, 1 if initialized else 0, datetime.now().isoformat(timespec="seconds"),
         1 if initialized else 0, datetime.now().isoformat(timespec="seconds")))
    conn.commit()


def is_seen(conn, key):
    return conn.execute("SELECT 1 FROM items WHERE key=?", (key,)).fetchone() is not None


def title_seen(conn, tk):
    return conn.execute("SELECT 1 FROM items WHERE title_key=?", (tk,)).fetchone() is not None


def save_item(conn, item):
    conn.execute(
        "INSERT OR IGNORE INTO items(key, source, title, title_key, url, published, first_seen) "
        "VALUES(?,?,?,?,?,?,?)",
        (item_key(item), item["source"], item["title"],
         title_key(item["title"], item.get("date")), item["url"],
         item["date"].isoformat() if item.get("date") else None,
         datetime.now().isoformat(timespec="seconds")))


# ---------------------------------------------------------------- 邮件

def smtp_configured(cfg):
    e = cfg["email"]
    return bool(e.get("smtp_host") and e.get("username") and e.get("password") and e.get("to"))


def send_mail(cfg, subject, text, html):
    e = cfg["email"]
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = formataddr((e.get("from_name") or "通知助手", e["username"]))
    msg["To"] = e["to"]
    msg["Date"] = formatdate(localtime=True)
    msg.set_content(text)
    msg.add_alternative(html, subtype="html")

    host, port = e["smtp_host"], int(e.get("smtp_port") or 465)
    ctx = ssl.create_default_context()
    if e.get("ssl", True):
        server = smtplib.SMTP_SSL(host, port, timeout=30, context=ctx)
    else:
        server = smtplib.SMTP(host, port, timeout=30)
        if e.get("starttls", True):
            server.starttls(context=ctx)
    try:
        server.login(e["username"], e["password"])
        server.send_message(msg)
    finally:
        try:
            server.quit()
        except Exception:
            pass


def build_mail(cfg, new_items):
    today = date.today().isoformat()
    groups = {}
    for it in new_items:
        groups.setdefault(it["source"], []).append(it)
    order = [s["name"] for s in cfg["sources"] if s["name"] in groups]
    groups = {k: groups[k] for k in order}
    for k in groups:
        groups[k].sort(key=lambda x: (x["date"], x["title"]), reverse=True)

    text = ["%d 条新通知（%s）" % (len(new_items), today), ""]
    html_parts = [
        '<div style="font-family:-apple-system,Segoe UI,Microsoft YaHei,sans-serif;'
        'max-width:680px;color:#222">',
        '<h2 style="margin:0 0 4px">山大通知 · %s</h2>' % today,
        '<p style="color:#666;margin:0 0 18px">共 %d 条新通知</p>' % len(new_items),
    ]
    for source, items in groups.items():
        text.append("【%s】" % source)
        html_parts.append('<h3 style="margin:18px 0 8px;font-size:15px;color:#555;'
                          'border-left:3px solid #1a73e8;padding-left:8px">%s</h3>'
                          % htmllib.escape(source))
        html_parts.append('<ul style="margin:0;padding-left:20px">')
        for it in items:
            ds = it["date"].isoformat() if it.get("date") else "日期未知"
            summary = (it.get("summary") or "").strip()
            text.append("  - [%s] %s\n    %s" % (ds, it["title"], it["url"]))
            if summary:
                text.append("    %s" % summary[:120])
            if it.get("wechat"):
                text.append("    （链接打不开时，请在微信“搜一搜”里搜索标题）")
            html_parts.append(
                '<li style="margin:8px 0"><a href="%s" style="color:#1a73e8;'
                'text-decoration:none">%s</a><br>'
                '<span style="color:#888;font-size:12px">%s</span>'
                % (htmllib.escape(it["url"]), htmllib.escape(it["title"]), ds))
            if summary:
                html_parts.append(
                    '<div style="color:#555;font-size:13px;margin-top:2px">%s</div>'
                    % htmllib.escape(summary[:160]))
            if it.get("wechat"):
                html_parts.append(
                    '<div style="color:#aaa;font-size:11px;margin-top:2px">'
                    '链接打不开时，请在微信“搜一搜”里搜索标题</div>')
            html_parts.append("</li>")
        html_parts.append("</ul>")
        text.append("")
    html_parts.append('<p style="color:#aaa;font-size:12px;margin-top:24px">'
                      '由本机 sdu-notify 生成</p></div>')
    return "\n".join(text), "".join(html_parts)


def _ask(prompt, default=""):
    try:
        return input(prompt).strip() or default
    except (EOFError, KeyboardInterrupt):
        return default


def _ask_secret(prompt):
    try:
        return getpass.getpass(prompt).strip()
    except (EOFError, KeyboardInterrupt):
        return ""


def email_wizard(cfg):
    print("\n=== 首次配置邮箱 ===")
    print("QQ 邮箱：设置 -> 账户 -> 开启 SMTP -> 获取授权码（不是登录密码）")
    print("163/126 同理。企业邮箱填 mail.<公司域名>。\n")
    addr = _ask("你的邮箱地址 (如 xxx@qq.com): ")
    if not addr:
        print("已跳过，稍后可手动编辑 config.json")
        return cfg
    domain = addr.split("@")[-1].lower()
    presets = {
        "qq.com": ("smtp.qq.com", 465),
        "163.com": ("smtp.163.com", 465),
        "126.com": ("smtp.126.com", 465),
        "sina.com": ("smtp.sina.com", 465),
        "gmail.com": ("smtp.gmail.com", 587),
        "outlook.com": ("smtp.office365.com", 587),
        "sdu.edu.cn": ("mail.sdu.edu.cn", 465),
    }
    host, port = presets.get(domain, ("smtp." + domain, 465))
    hp = _ask("SMTP 服务器 [%s:%d]: " % (host, port))
    if hp:
        if ":" in hp:
            host, hp_port = hp.rsplit(":", 1)
            port = int(hp_port)
        else:
            host = hp
    # 按端口推断加密方式：465=SSL，587=STARTTLS，其它=明文
    cfg["email"].update({
        "smtp_host": host, "smtp_port": int(port),
        "ssl": int(port) == 465,
        "starttls": int(port) == 587,
        "username": addr,
        "password": _ask_secret("邮箱授权码/密码: "),
        "to": _ask("收件邮箱 [%s]: " % addr, addr),
    })
    save_config(cfg)
    print("已保存到 config.json\n")
    return cfg


# ---------------------------------------------------------------- 主流程

def _similar_event(item, accepted, window_days=3, threshold=0.7):
    """同一事件被不同栏目分别报道：标题高度相似且日期相近。"""
    t = title_text(item["title"])
    if not t:
        return None
    for prev in accepted:
        if prev["source"] == item["source"]:      # 同一栏目内的相似标题不算重复
            continue
        if abs((item["date"] - prev["date"]).days) > window_days:
            continue
        if difflib.SequenceMatcher(None, t, title_text(prev["title"])).ratio() >= threshold:
            return prev
    return None


def main():
    args = set(sys.argv[1:])
    try:
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass

    cfg = load_config()
    today = date.today()

    if "--test-email" in args:
        if not smtp_configured(cfg) and sys.stdin.isatty():
            cfg = email_wizard(cfg)
        if not smtp_configured(cfg):
            print("邮箱还没配置：直接运行 run.py，会进入配置向导。")
            return 2
        send_mail(cfg, "[山大通知] 测试邮件",
                  "这是一封测试邮件。收到说明配置正确。",
                  "<p>这是一封<b>测试邮件</b>。收到说明配置正确。</p>")
        print("测试邮件已发送到 %s" % cfg["email"]["to"])
        return 0

    if not smtp_configured(cfg) and "--dry-run" not in args:
        if sys.stdin.isatty():
            cfg = email_wizard(cfg)
        if not smtp_configured(cfg):
            print("未配置邮箱，仅做抓取预览。配置后即可发送。")

    # 没配置邮箱 / dry-run 时不落库，避免留下半截状态
    write = smtp_configured(cfg) and "--dry-run" not in args
    conn = open_db()
    new_items, failures, seen_titles = [], [], set()
    news_names = {s["name"] for s in cfg["sources"] if s.get("news")}
    accepted_news = []

    for src in cfg["sources"]:
        name = src["name"]
        is_wechat = src.get("type") == "wechat"
        url = src.get("url", "")
        log("抓取：%s%s" % (name, "（微信公众号）" if is_wechat else ""))

        wx_session = wx_referer = None
        if is_wechat:
            try:
                items, wx_session, wx_referer = fetch_wechat_source(src)
            except Exception as e:
                log("  失败：%s（稍后重试，本轮跳过）" % e)
                failures.append(name)
                continue
            log("  解析到 %d 条" % len(items))
        else:
            try:
                html = http_get(url)
            except Exception as e:
                log("  失败：%s（检查是否连着校园网）" % e)
                failures.append(name)
                continue
            items = parse_items(html, url, today)
            log("  解析到 %d 条" % len(items))

        if not items:
            log("  警告：0 条，页面结构可能变了")
            failures.append(name + "（解析为空）")
            continue

        news_mode = name in news_names
        baseline = not source_initialized(conn, name)
        cutoff = today - timedelta(days=int(cfg.get("first_run_days", 7)))
        # 微信公众号的结果集不稳定，历史文章会时不时冒出来；
        # 所以它的时间窗口每轮都生效，而不是只在首轮生效。
        wx_cutoff = today - timedelta(
            days=int(cfg.get("wechat_max_age_days", 7)))

        picked, stale = [], 0
        for it in items:
            it["source"] = name
            if is_seen(conn, item_key(it)):
                continue
            if is_wechat:
                too_old = it["date"] < wx_cutoff
            else:
                too_old = baseline and it["date"] < cutoff
            if too_old:
                if write:
                    save_item(conn, it)     # 历史条目只入库、不推送
                stale += 1
                continue
            picked.append(it)
        if stale:
            log("  跳过 %d 条超出 %d 天的旧文章（只入库）"
                % (stale, int(cfg.get("wechat_max_age_days", 7))
                   if is_wechat else int(cfg.get("first_run_days", 7))))

        cap = int(cfg.get("max_items_per_source", 20))
        if len(picked) > cap:
            if write:                       # 超出上限的只记为已见，避免下次当成新通知
                for it in picked[cap:]:
                    save_item(conn, it)
                conn.commit()
            picked = picked[:cap]

        if not is_wechat and src.get("detail", True):
            for it in picked:
                if it["title"].endswith(("...", "…")) or len(it["title"]) >= 36:
                    t, d = enrich_from_detail(it["url"])
                    if t:
                        it["title"] = t
                    if d and not it.get("exact"):
                        it["date"] = d          # 列表页年份是推断的，用详情页校正

        uniq = []
        for it in picked:
            tk = title_key(it["title"], it["date"])
            if tk and (tk in seen_titles or title_seen(conn, tk)):
                log("  跳过重复：%s" % it["title"][:32])
                continue
            if news_mode and cfg.get("dedupe_similar", True):
                dup = _similar_event(it, accepted_news)
                if dup:
                    log("  合并同事件：%s ≈ %s" % (it["title"][:20], dup["title"][:20]))
                    if write:
                        save_item(conn, it)    # 记为已见，避免下次又被当成新通知
                        conn.commit()
                    continue
            seen_titles.add(tk)
            uniq.append(it)
            if news_mode:
                accepted_news.append(it)
        picked = uniq

        if is_wechat and picked:
            enrich_wechat_links(picked, wx_session, wx_referer)

        if write:
            mark_source(conn, name, initialized=True)
            conn.commit()
        log("  新通知 %d 条" % len(picked))
        new_items.extend(picked)

    if failures:
        log("异常站点：%s" % "；".join(failures))

    if not new_items:
        log("没有新通知。")
        if cfg.get("send_when_empty") and smtp_configured(cfg):
            txt, htm = build_mail(cfg, [])
            send_mail(cfg, "[山大通知] 今日无新通知", txt, htm)
        conn.close()
        return 0

    txt, htm = build_mail(cfg, new_items)
    subject = "[山大通知] %d 条新通知 · %s" % (len(new_items), today.isoformat())

    print("\n" + txt)

    if "--dry-run" in args:
        log("dry-run：不发送、不写库")
        conn.close()
        return 0

    if not smtp_configured(cfg):
        log("未配置邮箱，跳过发送。")
        conn.close()
        return 1

    try:
        send_mail(cfg, subject, txt, htm)
    except Exception as e:
        log("邮件发送失败：%s（本轮通知不记账，下次运行会重试）" % e)
        conn.close()
        return 1

    for it in new_items:      # 只有发送成功才记账，避免漏推
        save_item(conn, it)
    conn.commit()
    log("已发送到 %s" % cfg["email"]["to"])
    conn.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
