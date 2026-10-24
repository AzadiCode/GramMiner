# -*- coding: utf-8 -*-
"""
Miko Miner Room — ربات اختصاصی مینی‌بازی «اتاق ماینر میکو»
Stack (هم‌ساختار با AI BotMaker): Flask + MongoDB(pymongo) + مینی‌اپ تک‌فایلی index.html

- ربات: /start (دکمه‌ی ورود به بازی)، /top، /wallet، /help
- API مینی‌اپ: /api/state (ذخیره/بارگذاری)، /api/prices (قیمت زنده)، /api/top (رده‌بندی)
- احراز هویت با initData تلگرام (HMAC)
- ضد تقلب سبک: اعتبارسنجی ساختار state + سقف رشد ثروت در زمان

Environment:
  BOT_TOKEN   توکن ربات (الزامی)
  BASE_URL    آدرس عمومی سرور، مثلا https://yourapp.onrender.com (الزامی)
  MONGO_URI   خالی = حافظه‌ی موقت (با ری‌استارت پاک می‌شه)
  SECRET_KEY  اختیاری؛ پیش‌فرض از BOT_TOKEN ساخته می‌شه
  STAR_USD    ارزش هر استار به دلار (پیش‌فرض 0.013)
  MAX_WORTH_RATE  سقف رشد ثروت بازیکن به دلار در ثانیه (پیش‌فرض 0.0003)
  BUCKET_CAP      سقف «اعتبار رشد» ذخیره‌شده به دلار (پیش‌فرض 6)
"""
import os, re, json, time, hmac, hashlib, threading, logging
from collections import deque
from urllib.parse import parse_qsl
from datetime import datetime, timezone

import requests
from flask import Flask, request, jsonify, send_from_directory

# ───────────────────────── تنظیمات ─────────────────────────
BOT_TOKEN = os.environ["BOT_TOKEN"]
BASE_URL = os.environ["BASE_URL"].rstrip("/")
MONGO_URI = os.environ.get("MONGO_URI", "").strip()
SECRET_KEY = os.environ.get("SECRET_KEY", BOT_TOKEN)
STAR_USD = float(os.environ.get("STAR_USD", "0.013"))
MAX_WORTH_RATE = float(os.environ.get("MAX_WORTH_RATE", "0.0003"))
BUCKET_CAP = float(os.environ.get("BUCKET_CAP", "6"))
BUCKET_START = 1.0
PRICE_TTL = 30          # ثانیه
OFFLINE_MAX = 4 * 3600  # باید با OFFLINE_MAX کلاینت یکی باشه
STATE_VERSION = 3
SAVE_MIN_GAP = 2.0      # حداقل فاصله‌ی دو ذخیره (ثانیه)

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("miko")

app = Flask(__name__)
if MONGO_URI:
    from pymongo import MongoClient
    db = MongoClient(MONGO_URI, serverSelectionTimeoutMS=8000).get_database("mikominer")
else:
    import mongomock
    db = mongomock.MongoClient().get_database("mikominer")
    log.warning("MONGO_URI تنظیم نشده؛ از حافظه‌ی موقت استفاده می‌شه")
db.players.create_index("worth")

BOT_SECRET = hashlib.sha256(("bot" + SECRET_KEY).encode()).hexdigest()[:32]

# ───────────────────────── قوانین بازی (برای اعتبارسنجی) ─────────────────────────
COINS = ("STAR", "TON", "USD")
MINER_IDS = {"s1", "s2", "s3", "t1", "t2", "t3", "d1", "d2", "d3"}
ROOM_KEYS = ("ac", "strip", "tube", "hex")
SHELVES, EMAX = 6, 100
MAX_AMOUNT = 1e9


# ───────────────────────── ابزارها ─────────────────────────
def now():
    return datetime.now(timezone.utc)


def tg(method, **data):
    try:
        r = requests.post(f"https://api.telegram.org/bot{BOT_TOKEN}/{method}", json=data, timeout=15)
        return r.json()
    except Exception as e:
        log.warning("tg %s failed: %s", method, e)
        return {"ok": False, "description": str(e)}


def verify_init_data(init_data):
    try:
        pairs = dict(parse_qsl(init_data, keep_blank_values=True))
        got = pairs.pop("hash", None)
        if not got:
            return None
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        key = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        calc = hmac.new(key, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, got):
            return None
        if time.time() - int(pairs.get("auth_date", 0)) > 86400:
            return None
        return json.loads(pairs["user"])
    except Exception:
        return None


def auth():
    u = verify_init_data(request.headers.get("X-Init-Data", ""))
    return u if u else None


def display_name(u):
    name = (u.get("first_name") or "") + (" " + u["last_name"] if u.get("last_name") else "")
    return (name.strip() or u.get("username") or "ناشناس")[:24]


def fnum(n, d=8):
    return f"{n:.{d}f}"


# ───────────────────────── قیمت زنده ─────────────────────────
_price_lock = threading.Lock()
_price = {"t": 0.0, "ton": None}
_ton_hist = deque(maxlen=60)

TON_SOURCES = [
    ("https://api.binance.com/api/v3/ticker/price?symbol=TONUSDT", lambda j: float(j["price"])),
    ("https://www.okx.com/api/v5/market/ticker?instId=TON-USDT", lambda j: float(j["data"][0]["last"])),
    ("https://api.bybit.com/v5/market/tickers?category=spot&symbol=TONUSDT",
     lambda j: float(j["result"]["list"][0]["lastPrice"])),
    ("https://api.coingecko.com/api/v3/simple/price?ids=the-open-network&vs_currencies=usd",
     lambda j: float(j["the-open-network"]["usd"])),
]


def fetch_ton():
    for url, parse in TON_SOURCES:
        try:
            r = requests.get(url, timeout=5)
            p = parse(r.json())
            if p > 0:
                return p
        except Exception:
            continue
    return None


def get_prices():
    with _price_lock:
        if time.time() - _price["t"] > PRICE_TTL:
            p = fetch_ton()
            _price["t"] = time.time()          # حتی در خطا، تا TTL دوباره تلاش نکنه
            if p:
                _price["ton"] = p
                _ton_hist.append(p)
        ton = _price["ton"]
        hist = list(_ton_hist)
    coins = {
        "STAR": {"usd": STAR_USD, "hist": [STAR_USD] * 40},
        "USD": {"usd": 1.0, "hist": [1.0] * 40},
    }
    if ton:
        coins["TON"] = {"usd": ton, "hist": hist if len(hist) > 1 else [ton] * 40}
    return coins


# ───────────────────────── اعتبارسنجی state ─────────────────────────
def _num(v, hi=MAX_AMOUNT):
    if isinstance(v, bool) or not isinstance(v, (int, float)):
        raise ValueError("number")
    v = float(v)
    if v != v or v < 0 or v > hi:
        raise ValueError("range")
    return v


def clean_state(s):
    """فقط کلیدهای شناخته‌شده با مقادیر معتبر؛ در غیر این صورت ValueError"""
    if not isinstance(s, dict) or s.get("v") != STATE_VERSION:
        raise ValueError("version")
    out = {"v": STATE_VERSION, "usd": _num(s.get("usd"))}
    w = s.get("wallet")
    if not isinstance(w, dict):
        raise ValueError("wallet")
    out["wallet"] = {c: _num(w.get(c, 0)) for c in COINS}
    if s.get("sel") not in COINS:
        raise ValueError("sel")
    out["sel"] = s["sel"]
    out["pc"] = int(_num(s.get("pc"), 5))
    out["shelves"] = int(_num(s.get("shelves"), SHELVES))
    if out["shelves"] < 1:
        raise ValueError("shelves")
    slots = s.get("slots")
    if not isinstance(slots, list) or len(slots) != SHELVES * 2:
        raise ValueError("slots")
    out["slots"] = []
    for i, m in enumerate(slots):
        if m is None:
            out["slots"].append(None)
        elif m in MINER_IDS and i < out["shelves"] * 2:
            out["slots"].append(m)
        else:
            raise ValueError("slot")
    room = s.get("room") or {}
    out["room"] = {k: True for k in ROOM_KEYS if isinstance(room, dict) and room.get(k)}
    out["taps"] = int(_num(s.get("taps"), 1e9))
    out["sold"] = _num(s.get("sold"))
    out["ch"] = int(_num(s.get("ch"), 8))
    out["en"] = _num(s.get("en"), EMAX)
    out["et"] = _num(s.get("et"), 1e14)
    dl = s.get("dl", "")
    out["dl"] = dl if isinstance(dl, str) and re.fullmatch(r"\d{4}-\d{2}-\d{2}", dl) else ""
    out["st"] = int(_num(s.get("st", 0), 7))
    return out


def check_growth(p, new_worth, t):
    """
    سقف رشد ثروت: یک «سطل اعتبار» که با گذر زمان پر می‌شه. رشد بیشتر از سطل = رد.
    (سرعت‌گیر ساده؛ برای برداشت واقعی باید محاسبات سمت سرور انجام بشه.)
    """
    last = float(p.get("worth", 0.0)) if p else 0.0
    bucket = float(p.get("bucket", BUCKET_START)) if p else BUCKET_START
    bt = p.get("bt") if p else None
    dt = max(0.0, (t - bt).total_seconds()) if bt else 0.0
    bucket = min(BUCKET_CAP, bucket + dt * MAX_WORTH_RATE)
    growth = new_worth - last
    if p and growth > bucket:
        return False, bucket
    if growth > 0:
        bucket -= growth
    return True, max(0.0, bucket)


def public_state(p):
    return p.get("state") if p else None


# ───────────────────────── API مینی‌اپ ─────────────────────────
@app.get("/")
def index():
    r = send_from_directory(os.path.dirname(os.path.abspath(__file__)), "index.html")
    r.headers["Cache-Control"] = "no-cache"
    return r


@app.get("/health")
def health():
    return "ok"


@app.get("/api/prices")
def api_prices():
    return jsonify(coins=get_prices())


@app.get("/api/state")
def api_get_state():
    u = auth()
    if not u:
        return jsonify(error="unauthorized"), 401
    t = now()
    p = db.players.find_one({"_id": u["id"]})
    off = 0
    if p:
        ref = p.get("touch") or p.get("saved") or t
        off = int(max(0, min(OFFLINE_MAX, (t - ref).total_seconds())))
        db.players.update_one({"_id": u["id"]}, {"$set": {"touch": t, "name": display_name(u)}})
    else:
        db.players.insert_one({"_id": u["id"], "name": display_name(u), "state": None, "worth": 0.0,
                               "bucket": BUCKET_START, "bt": t, "touch": t, "saved": t, "created": t})
    return jsonify(state=public_state(p), offline_sec=off)


@app.put("/api/state")
def api_put_state():
    u = auth()
    if not u:
        return jsonify(error="unauthorized"), 401
    body = request.get_json(silent=True) or {}
    try:
        st = clean_state(body.get("state"))
        worth = _num(body.get("worth"), 1e9)
    except (ValueError, TypeError):
        return jsonify(error="bad state"), 400
    t = now()
    p = db.players.find_one({"_id": u["id"]})
    if p and p.get("saved") and (t - p["saved"]).total_seconds() < SAVE_MIN_GAP:
        return jsonify(ok=True, skipped=True)
    ok, bucket = check_growth(p, worth, t)
    if not ok:
        log.warning("growth rejected uid=%s worth=%s last=%s", u["id"], worth, p.get("worth"))
        return jsonify(error="growth limit"), 409
    db.players.update_one({"_id": u["id"]}, {"$set": {
        "state": st, "worth": worth, "bucket": bucket, "bt": t, "saved": t, "touch": t,
        "name": display_name(u)}}, upsert=True)
    return jsonify(ok=True)


@app.get("/api/top")
def api_top():
    u = auth()
    if not u:
        return jsonify(error="unauthorized"), 401
    rows = list(db.players.find({"state": {"$ne": None}}).sort("worth", -1).limit(10))
    top = [{"name": r.get("name", "ناشناس"), "worth": r.get("worth", 0), "me": r["_id"] == u["id"]} for r in rows]
    me = db.players.find_one({"_id": u["id"]})
    rank = None
    if me and me.get("state"):
        rank = db.players.count_documents({"state": {"$ne": None}, "worth": {"$gt": me.get("worth", 0)}}) + 1
    return jsonify(top=top, rank=rank)


# ───────────────────────── ربات ─────────────────────────
PLAY_KB = {"inline_keyboard": [[{"text": "⛏️ ورود به اتاق ماینر", "web_app": {"url": BASE_URL}}]]}


def top_text():
    rows = list(db.players.find({"state": {"$ne": None}}).sort("worth", -1).limit(10))
    if not rows:
        return "هنوز کسی تو رده‌بندی نیست. اولین نفر باش! ⛏️"
    medals = ["🥇", "🥈", "🥉"]
    lines = [f"{medals[i] if i < 3 else str(i + 1) + '.'} {r.get('name', 'ناشناس')} — ${fnum(r.get('worth', 0), 6)}"
             for i, r in enumerate(rows)]
    return "🏆 برترین ماینرها\n\n" + "\n".join(lines)


def wallet_text(uid):
    p = db.players.find_one({"_id": uid})
    if not p or not p.get("state"):
        return "هنوز اتاقی نساختی. اول وارد بازی شو! ⛏️"
    s = p["state"]
    w = s["wallet"]
    n = sum(1 for m in s["slots"] if m)
    return ("👛 کیف پول تو\n\n"
            f"⭐ Stars: {fnum(w['STAR'], 6)}\n"
            f"💎 TON: {fnum(w['TON'], 8)}\n"
            f"💵 USD: ${fnum(w['USD'], 8)}\n\n"
            f"💰 موجودی بازی: ${fnum(s['usd'], 8)}\n"
            f"⚙️ ماینر فعال: {n} · قفسه: {s['shelves']}")


WELCOME = ("⛏️ به اتاق ماینر میکو خوش اومدی!\n\n"
           "استارز، تون و دلار رو با ماینرهات استخراج کن. ارقام ریزه، شبکه سخته و صبر پاداش داره.\n"
           "هر روز سر بزن و پاداش روزانه‌ت رو بگیر 🎁")
HELP = ("/start — ورود به بازی\n/wallet — موجودی کیف پول\n/top — رده‌بندی ثروت\n/help — راهنما")


@app.post("/bot")
def bot_hook():
    if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != BOT_SECRET:
        return "forbidden", 403
    upd = request.get_json(silent=True) or {}
    try:
        msg = upd.get("message")
        if not msg or msg.get("chat", {}).get("type") != "private":
            return "ok"
        chat_id = msg["chat"]["id"]
        cmd = (msg.get("text") or "").strip().split()[:1]
        cmd = cmd[0][1:].split("@")[0].lower() if cmd and cmd[0].startswith("/") else ""
        if cmd == "top":
            tg("sendMessage", chat_id=chat_id, text=top_text(), reply_markup=PLAY_KB)
        elif cmd == "wallet":
            tg("sendMessage", chat_id=chat_id, text=wallet_text(msg["from"]["id"]), reply_markup=PLAY_KB)
        elif cmd == "help":
            tg("sendMessage", chat_id=chat_id, text=HELP, reply_markup=PLAY_KB)
        else:
            tg("sendMessage", chat_id=chat_id, text=WELCOME, reply_markup=PLAY_KB)
    except Exception:
        log.exception("bot_hook error")
    return "ok"


def setup_bot():
    r = tg("setWebhook", url=f"{BASE_URL}/bot", secret_token=BOT_SECRET,
           allowed_updates=["message"], drop_pending_updates=True)
    tg("setMyCommands", commands=[
        {"command": "start", "description": "ورود به بازی"},
        {"command": "wallet", "description": "کیف پول"},
        {"command": "top", "description": "رده‌بندی"},
        {"command": "help", "description": "راهنما"}])
    tg("setChatMenuButton", menu_button={"type": "web_app", "text": "بازی", "web_app": {"url": BASE_URL}})
    log.info("webhook: %s", r)


setup_bot()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 10000)))
