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
  TON_ADDRESS    آدرس دریافت واریز TON (برای فعال شدن واریز TON)
  ADMIN_ID       آیدی عددی ادمین (برای فعال شدن برداشت؛ تأیید دستی با دکمه)
  TONCENTER_KEY / SWAP_FEE / MIN_WD_TON / MIN_WD_USDT  تنظیمات اختیاری کیف پول
  MAX_WORTH_RATE  سقف رشد ثروت بازیکن به دلار در ثانیه (پیش‌فرض 0.0003)
  BUCKET_CAP      سقف «اعتبار رشد» ذخیره‌شده به دلار (پیش‌فرض 6)
  BOT_USERNAME    اختیاری؛ اگه خالی باشه از getMe گرفته می‌شه (برای لینک دعوت)
  REF_BONUS / REF_WELCOME / REF_MAX / REF_DAILY_MAX  تنظیمات زیرمجموعه‌گیری
  CASHOUT_FEE / CASHOUT_MIN_USD / CASHOUT_DAILY_USD  پیش‌فرض انتقال ارز ماین‌شده به کیف پول (بعدش از پنل ادمین قابل تغییره)

پنل ادمین: اگه ADMIN_ID تنظیم باشه، فقط همون کاربر دکمه‌ی 🛡 رو توی بازی می‌بینه (سرور هم همه‌ی /api/admin/* رو چک می‌کنه).
  نمای کلی · برداشت‌ها (تأیید/رد) · کاربران (جستجو، تنظیم موجودی، مسدود) · تنظیمات (کارمزد و حداقل‌ها) · پیام همگانی
"""
import os, re, json, time, math, hmac, hashlib, secrets, threading, logging
from collections import deque
from urllib.parse import parse_qsl
from datetime import datetime, timezone, timedelta

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
REF_BONUS = float(os.environ.get("REF_BONUS", "0.06"))      # جایزه‌ی دعوت‌کننده برای هر زیرمجموعه‌ی فعال (دلار بازی)
REF2_BONUS = float(os.environ.get("REF2_BONUS", "0.01"))    # جایزه‌ی سطح دوم دعوت (دعوت‌کننده‌ی دعوت‌کننده)
REF_WELCOME = float(os.environ.get("REF_WELCOME", "0.03"))  # جایزه‌ی دعوت‌شده
REF_MAX = int(os.environ.get("REF_MAX", "50"))              # سقف زیرمجموعه‌ی پاداش‌دار هر نفر
REF_DAILY_MAX = int(os.environ.get("REF_DAILY_MAX", "10"))  # سقف فعال‌سازی در ۲۴ ساعت
REF_MILESTONES = {3: 0.10, 10: 0.40, 25: 1.00}              # پاداش پله‌ای بر اساس تعداد فعال
REF_MIN_CH, REF_MIN_TAPS = 3, 50                            # شرط «فعال» شدن: ماموریت ۳ + ۵۰ ضربه
# ── کیف پول واقعی (TON / Stars / USDT) ──
TON_ADDRESS = os.environ.get("TON_ADDRESS", "").strip()       # آدرس دریافت واریز TON
TONCENTER_KEY = os.environ.get("TONCENTER_KEY", "").strip()   # اختیاری؛ کلید toncenter برای محدودیت کمتر
ADMIN_ID = int(os.environ.get("ADMIN_ID", "0") or 0)          # آیدی عددی ادمین برای تأیید برداشت‌ها
SWAP_FEE = float(os.environ.get("SWAP_FEE", "0.02"))          # کارمزد تبدیل
MIN_WD = {"TON": float(os.environ.get("MIN_WD_TON", "0.5")), "STAR": 200.0, "USDT": float(os.environ.get("MIN_WD_USDT", "10"))}
MIN_STARS_DEP = 10
ASSETS = ("TON", "STAR", "USDT")
DEC = {"TON": 9, "STAR": 0, "USDT": 6}
CASHOUT_MAP = {"STAR": "STAR", "TON": "TON", "USD": "USDT"}   # ارز ماین‌شده ← دارایی کیف پول
CFG_DEFAULTS = {                                               # پیش‌فرض تنظیمات؛ از پنل ادمین قابل تغییره
    "swap_fee": SWAP_FEE,
    "cashout_fee": float(os.environ.get("CASHOUT_FEE", "0")),
    "cashout_min_usd": float(os.environ.get("CASHOUT_MIN_USD", "0.01")),
    "cashout_daily_usd": float(os.environ.get("CASHOUT_DAILY_USD", "25")),
    "cashout_on": True, "wd_on": True,
    "min_wd_TON": MIN_WD["TON"], "min_wd_STAR": MIN_WD["STAR"], "min_wd_USDT": MIN_WD["USDT"],
}
CFG_LIMITS = {"swap_fee": (0, .5), "cashout_fee": (0, .5), "cashout_min_usd": (0, 1000), "cashout_daily_usd": (0, 1e6),
              "min_wd_TON": (0, 1e6), "min_wd_STAR": (0, 1e7), "min_wd_USDT": (0, 1e6)}
PRICE_TTL = 30          # ثانیه
OFFLINE_MAX = 4 * 3600  # باید با OFFLINE_MAX کلاینت یکی باشه
STATE_VERSION = 4       # v4 = فاز ۶ داستان (فیلد cs)؛ v3 قدیمی هم پذیرفته می‌شه
SAVE_MIN_GAP = 2.0      # حداقل فاصله‌ی دو ذخیره (ثانیه)

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("miko")

app = Flask(__name__)
if MONGO_URI:
    from pymongo import MongoClient
    db = MongoClient(MONGO_URI, serverSelectionTimeoutMS=8000, tz_aware=True).get_database("mikominer")
else:
    import mongomock
    db = mongomock.MongoClient().get_database("mikominer")
    log.warning("MONGO_URI تنظیم نشده؛ از حافظه‌ی موقت استفاده می‌شه")
db.players.create_index("worth")
db.wtx.create_index("uid")

BOT_USERNAME = os.environ.get("BOT_USERNAME", "").lstrip("@")
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


def aware(d):
    """Mongo/mongomock ممکنه datetime بدون منطقه‌ی زمانی برگردونه؛ همیشه UTC-aware می‌کنیم"""
    return d.replace(tzinfo=timezone.utc) if d is not None and d.tzinfo is None else d


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
    if not u:
        return None
    if u["id"] != ADMIN_ID and db.players.find_one({"_id": u["id"], "banned": True}, {"_id": 1}):
        return None          # کاربر مسدود
    return u


def is_admin(u):
    return bool(ADMIN_ID) and bool(u) and u.get("id") == ADMIN_ID


def display_name(u):
    name = (u.get("first_name") or "") + (" " + u["last_name"] if u.get("last_name") else "")
    return (name.strip() or u.get("username") or "ناشناس")[:24]


_cfg = {"t": 0.0, "v": dict(CFG_DEFAULTS)}


def cfg():
    """تنظیمات فعلی (کش ۱۰ ثانیه‌ای)؛ مقدار ذخیره‌شده‌ی ادمین روی پیش‌فرض اولویت داره"""
    if time.time() - _cfg["t"] > 10:
        v = dict(CFG_DEFAULTS)
        try:
            d = db.settings.find_one({"_id": "cfg"}) or {}
            for k, dv in CFG_DEFAULTS.items():
                if k in d:
                    v[k] = bool(d[k]) if isinstance(dv, bool) else float(d[k])
        except Exception as e:
            log.warning("cfg: %s", e)
        _cfg["v"], _cfg["t"] = v, time.time()
    return _cfg["v"]


def set_cfg(upd):
    clean = {}
    for k, dv in CFG_DEFAULTS.items():
        if k not in upd:
            continue
        if isinstance(dv, bool):
            clean[k] = bool(upd[k])
        else:
            x = float(upd[k])
            lo, hi = CFG_LIMITS[k]
            if x != x or x < lo or x > hi:
                raise ValueError(k)
            clean[k] = x
    if clean:
        db.settings.update_one({"_id": "cfg"}, {"$set": clean}, upsert=True)
        _cfg["t"] = 0.0
    return clean


WITHDRAW_MIN_USD = 10.0  # حداقل ارزش دلاری برداشت برای همه‌ی دارایی‌ها

def min_wd():
    """حداقل برداشت برای همه‌ی دارایی‌ها معادل ۱۰ دلار است؛ بر اساس نرخ فعلی هر دارایی."""
    out = {}
    for a in ASSETS:
        price = asset_usd(a)
        out[a] = (math.ceil((WITHDRAW_MIN_USD / price) * (10 ** DEC[a])) / (10 ** DEC[a])) if price > 0 else 0
    return out


def alog(action, **kw):
    """گزارش کارهای ادمین"""
    try:
        db.alog.insert_one({"t": now(), "a": action, **kw})
    except Exception:
        pass


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
    """فقط کلیدهای شناخته‌شده با مقادیر معتبر؛ در غیر این صورت ValueError
    v3 قدیمی پذیرفته می‌شه و به v4 ارتقا پیدا می‌کنه (پیشرفت کاربران حفظ می‌شه)."""
    if not isinstance(s, dict) or s.get("v") not in (3, STATE_VERSION):
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
    out["rd"] = 1 if s.get("rd") else 0
    out["en"] = _num(s.get("en"), EMAX)
    out["et"] = _num(s.get("et"), 1e14)
    dl = s.get("dl", "")
    out["dl"] = dl if isinstance(dl, str) and re.fullmatch(r"\d{4}-\d{2}-\d{2}", dl) else ""
    out["st"] = int(_num(s.get("st", 0), 7))
    raw_cs = s.get("cs", 0)      # صحنه‌های دیده‌شده‌ی داستان؛ فقط نمایشی — clamp می‌شه نه رد
    out["cs"] = int(raw_cs) if isinstance(raw_cs, (int, float)) and not isinstance(raw_cs, bool) and 0 <= raw_cs <= 8 else 0
    # ── فاز ۷+ (تکمیل): کازمتیک میکو و ماموریت هفتگی — نمایشی/شمارش ساده، فقط sanitize ──
    raw_cos = s.get("cos", 1)
    out["cos"] = int(raw_cos) if isinstance(raw_cos, (int, float)) and not isinstance(raw_cos, bool) and 0 <= raw_cos <= 15 else 1
    raw_co = s.get("co", 0)
    out["co"] = min(3, int(raw_co)) if isinstance(raw_co, (int, float)) and not isinstance(raw_co, bool) and 0 <= raw_co <= 3 else 0
    out["mb"] = int(_num(s.get("mb", 0), 1e9))        # کل ماینرهای خریده‌شده (شمارنده‌ی ماموریت هفتگی)
    wk = s.get("wk", "")
    out["wk"] = wk if isinstance(wk, str) and re.fullmatch(r"\d{4}-W\d{1,2}", wk) else ""
    wp = s.get("wp")
    if isinstance(wp, dict):
        out["wp"] = {k: round(float(v), 8) for k, v in wp.items()
                     if k in ("t0", "s0", "b0") and isinstance(v, (int, float)) and not isinstance(v, bool) and 0 <= v < 1e9}
    else:
        out["wp"] = {}
    raw_wc = s.get("wc", 0)
    out["wc"] = int(raw_wc) if isinstance(raw_wc, (int, float)) and not isinstance(raw_wc, bool) and 0 <= raw_wc <= 7 else 0
    out["cashed"] = _num(s.get("cashed", 0))      # مجموع دلارِ ارزهای ماین‌شده‌ی منتقل‌شده به کیف پول
    return out


def check_growth(p, new_worth, t):
    """
    سقف رشد ثروت: یک «سطل اعتبار» که با گذر زمان پر می‌شه. رشد بیشتر از سطل = رد.
    (سرعت‌گیر ساده؛ برای برداشت واقعی باید محاسبات سمت سرور انجام بشه.)
    """
    last = float(p.get("worth", 0.0)) if p else 0.0
    bucket = float(p.get("bucket", BUCKET_START)) if p else BUCKET_START
    bt = aware(p.get("bt")) if p else None
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


# ───────────────────────── زیرمجموعه‌گیری ─────────────────────────
def new_player(uid, name, ref=None):
    t = now()
    doc = {"_id": uid, "name": name, "state": None, "worth": 0.0, "bucket": BUCKET_START,
           "bt": t, "touch": t, "saved": t, "created": t}
    if ref:
        doc["ref"] = ref
    try:
        db.players.insert_one(doc)
        return True
    except Exception:       # DuplicateKey: قبلاً ساخته شده
        return False


def register_ref(uid, name, payload):
    """فقط برای بازیکن کاملاً جدید؛ کسی که قبلاً وارد بازی یا ربات شده، هیچ‌وقت زیرمجموعه حساب نمی‌شه."""
    ref = None
    m = re.fullmatch(r"ref_(\d{1,15})", payload or "")
    if m:
        rid = int(m.group(1))
        if rid != uid and db.players.find_one({"_id": rid, "state": {"$ne": None}}):
            ref = rid
    return new_player(uid, name, ref), ref


def activate_ref(uid):
    """وقتی دعوت‌شده واقعاً بازی کرد (ماموریت ۳ + ۵۰ ضربه) جایزه‌ها پرداخت می‌شن. اتمیک: فقط یک‌بار."""
    t = now()
    p = db.players.find_one_and_update({"_id": uid, "ref": {"$exists": True}, "ref_done": {"$ne": True}},
                                       {"$set": {"ref_done": True, "ref_done_at": t}})
    if not p:
        return
    rid = p["ref"]
    recent = db.players.count_documents({"ref": rid, "ref_done_at": {"$gte": t - timedelta(days=1)}})
    active = db.players.count_documents({"ref": rid, "ref_done": True})
    if active > REF_MAX or recent > REF_DAILY_MAX:
        log.info("ref payout skipped rid=%s active=%s recent=%s", rid, active, recent)
        return
    bonus = REF_BONUS + REF_MILESTONES.get(active, 0.0)
    db.players.update_one({"_id": rid}, {"$inc": {"bonus": bonus, "ref_earned": bonus}})
    db.players.update_one({"_id": uid}, {"$inc": {"bonus": REF_WELCOME}})
    # رفرال دومرحله‌ای (فاز ۷+): دعوت‌کننده‌ی دعوت‌کننده هم جایزه‌ی کوچکی می‌گیره
    up = db.players.find_one({"_id": rid}, {"ref": 1})
    if up and up.get("ref"):
        db.players.update_one({"_id": up["ref"]}, {"$inc": {"bonus": REF2_BONUS, "ref_earned": REF2_BONUS}})
        tg("sendMessage", chat_id=up["ref"],
           text=f"زیرمجموعه‌ی زیرمجموعه‌ات فعال شد: +${REF2_BONUS:.2f} (سطح دوم دعوت)",
           reply_markup=PLAY_KB)
    tg("sendMessage", chat_id=rid, text=f"🎉 پاداش دعوت اضافه شد!\n{p.get('name', 'دوستت')} به ماموریت ۳ رسید.\nجایزه: ${bonus:.2f} · زیرمجموعه‌ی فعال: {active}",
       reply_markup=PLAY_KB)
    tg("sendMessage", chat_id=uid, text=f"🎁 هدیه‌ی خوش‌آمد اضافه شد: ${REF_WELCOME:.2f}\nدفعه‌ی بعد که بازی رو باز کنی تو موجودیت می‌بینی.",
       reply_markup=PLAY_KB)


def ref_link(uid):
    return f"https://t.me/{BOT_USERNAME}?start=ref_{uid}" if BOT_USERNAME else ""


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
        ref = aware(p.get("touch") or p.get("saved")) or t
        off = int(max(0, min(OFFLINE_MAX, (t - ref).total_seconds())))
        db.players.update_one({"_id": u["id"]}, {"$set": {"touch": t, "name": display_name(u)}})
        # پاداش دعوت: یک‌بار تحویل داده می‌شه و به ثروت هم اضافه می‌شه تا سقف رشد اشتباه رد نکنه
        b = float(p.get("bonus", 0) or 0)
        if b > 0:
            claimed = db.players.find_one_and_update({"_id": u["id"], "bonus": {"$gt": 0}},
                                                     {"$set": {"bonus": 0}, "$inc": {"worth": b}})
            b = float(claimed.get("bonus", 0)) if claimed else 0.0
    else:
        new_player(u["id"], display_name(u))
        b = 0.0
    return jsonify(state=public_state(p), offline_sec=off, bonus_usd=b, is_admin=is_admin(u))


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
    if p and p.get("saved") and (t - aware(p["saved"])).total_seconds() < SAVE_MIN_GAP:
        return jsonify(ok=True, skipped=True)
    if p and p.get("cash_at") and (t - aware(p["cash_at"])).total_seconds() < 3:
        return jsonify(ok=True, skipped=True)     # درخواست ذخیره‌ی قدیمیِ در راه بعد از انتقال ماین
    ok, bucket = check_growth(p, worth, t)
    if not ok:
        log.warning("growth rejected uid=%s worth=%s last=%s", u["id"], worth, p.get("worth"))
        return jsonify(error="growth limit"), 409
    # لیگ هفتگی: نقطه‌ی شروع هفته (w0) رو نگه می‌داریم؛ با عوض شدن هفته ریست می‌شه
    iso = t.isocalendar()
    wk = f"{iso[0]}-W{iso[1]}"
    w0 = worth if not p or p.get("wk") != wk else float(p.get("w0", worth))
    db.players.update_one({"_id": u["id"]}, {"$set": {
        "state": st, "worth": worth, "bucket": bucket, "bt": t, "saved": t, "touch": t,
        "wk": wk, "w0": w0, "name": display_name(u)}}, upsert=True)
    if p and p.get("ref") and not p.get("ref_done") and st["ch"] >= REF_MIN_CH and st["taps"] >= REF_MIN_TAPS:
        activate_ref(u["id"])
    return jsonify(ok=True)


@app.get("/api/top")
def api_top():
    u = auth()
    if not u:
        return jsonify(error="unauthorized"), 401
    played = {"state": {"$ne": None}}
    rows = list(db.players.find(played).sort("worth", -1).limit(20))
    top = []
    for r in rows:
        st = r.get("state") or {}
        top.append({"name": r.get("name", "ناشناس"), "worth": r.get("worth", 0), "me": r["_id"] == u["id"],
                    "miners": sum(1 for m in st.get("slots", []) if m), "shelves": st.get("shelves", 1)})
    me = db.players.find_one({"_id": u["id"]})
    rank = None
    if me and me.get("state"):
        rank = db.players.count_documents({"state": {"$ne": None}, "worth": {"$gt": me.get("worth", 0)}}) + 1
    # لیگ هفتگی: بیشترین رشد ثروت از ابتدای هفته (فقط خواندنی؛ جایزه‌ها دستی توسط ادمین)
    iso = t.isocalendar()
    wk = f"{iso[0]}-W{iso[1]}"
    gains = []
    for r in db.players.find({"state": {"$ne": None}, "wk": wk}, {"name": 1, "worth": 1, "w0": 1}).limit(200):
        g = float(r.get("worth", 0) or 0) - float(r.get("w0", r.get("worth", 0)) or 0)
        if g > 0:
            gains.append({"name": r.get("name", "ناشناس"), "gain": round(g, 6), "me": r["_id"] == u["id"]})
    gains.sort(key=lambda x: -x["gain"])
    me_gain = next((g["gain"] for g in gains if g["me"]), None)
    return jsonify(top=top, rank=rank, total=db.players.count_documents(played),
                   week={"top": gains[:5], "me": me_gain, "key": wk})


@app.get("/api/ref")
def api_ref():
    u = auth()
    if not u:
        return jsonify(error="unauthorized"), 401
    me = db.players.find_one({"_id": u["id"]}) or {}
    invited = db.players.count_documents({"ref": u["id"]})
    active = db.players.count_documents({"ref": u["id"], "ref_done": True})
    nxt = next(((k, v) for k, v in sorted(REF_MILESTONES.items()) if active < k), None)
    return jsonify(link=ref_link(u["id"]), invited=invited, active=active,
                   earned=float(me.get("ref_earned", 0) or 0), bonus=REF_BONUS, welcome=REF_WELCOME,
                   next={"at": nxt[0], "bonus": nxt[1]} if nxt else None, max=REF_MAX)


# ───────────────────────── کیف پول واقعی ─────────────────────────
def asset_usd(a):
    if a == "STAR":
        return STAR_USD
    if a == "USDT":
        return 1.0
    return ((get_prices().get("TON") or {}).get("usd")) or 0.0


def floor_to(a, v):
    f = 10 ** DEC[a]
    return math.floor(v * f + 1e-9) / f


def bal_of(p):
    b = (p or {}).get("bal") or {}
    return {a: round(float(b.get(a, 0) or 0), DEC[a]) for a in ASSETS}


def debit(uid, a, amt):
    return bool(db.players.find_one_and_update({"_id": uid, f"bal.{a}": {"$gte": amt}}, {"$inc": {f"bal.{a}": -amt}}))


def credit(uid, a, amt):
    db.players.update_one({"_id": uid}, {"$inc": {f"bal.{a}": amt}})


def log_tx(tid, **kw):
    """ثبت تراکنش با شناسه‌ی یکتا؛ اگه قبلاً ثبت شده باشه False برمی‌گردونه (جلوگیری از شارژ دوباره)"""
    try:
        db.wtx.insert_one({"_id": tid, "t": now(), **kw})
        return True
    except Exception:
        return False


_scan = {"t": 0.0}
_scan_lock = threading.Lock()


def scan_ton():
    """واریزهای TON به آدرس پروژه رو با کامنت MIKO<uid> پیدا و یک‌بار اعتبار می‌ده"""
    if not TON_ADDRESS:
        return
    with _scan_lock:
        if time.time() - _scan["t"] < 8:
            return
        _scan["t"] = time.time()
        try:
            h = {"X-API-Key": TONCENTER_KEY} if TONCENTER_KEY else {}
            r = requests.get("https://toncenter.com/api/v2/getTransactions",
                             params={"address": TON_ADDRESS, "limit": 40}, headers=h, timeout=8).json()
            for tx in r.get("result") or []:
                m = tx.get("in_msg") or {}
                mm = re.fullmatch(r"MIKO(\d{1,15})", (m.get("message") or "").strip())
                val = int(m.get("value") or 0)
                if not m.get("source") or val <= 0 or not mm:
                    continue
                uid, amt = int(mm.group(1)), val / 1e9
                if not db.players.find_one({"_id": uid}, {"_id": 1}):
                    continue
                if log_tx("dep:ton:" + tx["transaction_id"]["hash"], uid=uid, type="deposit", asset="TON", amount=amt, status="done"):
                    credit(uid, "TON", amt)
                    tg("sendMessage", chat_id=uid, text=f"✅ واریز {amt:.4f} TON به کیف پولت اضافه شد.", reply_markup=PLAY_KB)
        except Exception as e:
            log.warning("scan_ton: %s", e)


def _scan_loop():
    while True:
        time.sleep(45)
        scan_ton()


def need_user():
    u = auth()
    if not u:
        return None, (jsonify(error="unauthorized"), 401)
    if not db.players.find_one({"_id": u["id"]}, {"_id": 1}):
        new_player(u["id"], display_name(u))
    return u, None


def amount_arg(body, a):
    try:
        v = float(body.get("amount"))
    except (TypeError, ValueError):
        return None
    v = floor_to(a, v)
    return v if v > 0 and v < 1e9 else None


@app.get("/api/wallet")
def api_wallet():
    u, err = need_user()
    if err:
        return err
    scan_ton()
    uid = u["id"]
    p = db.players.find_one({"_id": uid}) or {}
    hist = [{"id": str(x["_id"]), "type": x.get("type"), "asset": x.get("asset"), "amount": x.get("amount"),
             "status": x.get("status"), "to": x.get("to"), "ts": int(aware(x["t"]).timestamp() * 1000),
             "dir": x.get("sign") or (1 if x.get("type") in ("deposit", "cashout") else -1)}
            for x in db.wtx.find({"uid": uid}).sort("t", -1).limit(15)]
    c = cfg()
    rank = None
    if p.get("state"):
        rank = db.players.count_documents({"state": {"$ne": None}, "worth": {"$gt": p.get("worth", 0)}}) + 1
    return jsonify(bal=bal_of(p), hist=hist, rank=rank, total=db.players.count_documents({"state": {"$ne": None}}),
                   worth=p.get("worth", 0), usd={a: asset_usd(a) for a in ASSETS}, fee=c["swap_fee"], min_wd=min_wd(),
                   min_stars=MIN_STARS_DEP, ton_address=TON_ADDRESS, memo=f"MIKO{uid}",
                   wd_on=bool(ADMIN_ID) and c["wd_on"], is_admin=is_admin(u), star_usd=STAR_USD,
                   cashout={"on": c["cashout_on"], "fee": c["cashout_fee"], "min_usd": c["cashout_min_usd"],
                            "daily_usd": c["cashout_daily_usd"],
                            "left_usd": max(0.0, c["cashout_daily_usd"] - cashout_used(uid))})


@app.post("/api/wallet/stars")
def api_wallet_stars():
    u, err = need_user()
    if err:
        return err
    try:
        n = int((request.get_json(silent=True) or {}).get("amount"))
    except (TypeError, ValueError):
        return jsonify(error="amount"), 400
    if n < MIN_STARS_DEP or n > 10000:
        return jsonify(error="amount"), 400
    to_game = bool((request.get_json(silent=True) or {}).get("to_game"))
    r = tg("createInvoiceLink", title="شارژ بالانس بازی" if to_game else "شارژ Stars",
           description=(f"{n} استارز ← ${n * STAR_USD:.2f} بالانس بازی" if to_game else f"واریز {n} استارز به کیف پول بازی"),
           payload=f"{'depg' if to_game else 'dep'}:{u['id']}", currency="XTR", prices=[{"label": "Stars", "amount": n}])
    if not r.get("ok"):
        return jsonify(error="invoice"), 502
    return jsonify(link=r["result"])


@app.post("/api/wallet/swap")
def api_wallet_swap():
    u, err = need_user()
    if err:
        return err
    b = request.get_json(silent=True) or {}
    fa, ta = b.get("from"), b.get("to")
    if fa not in ASSETS or ta not in ASSETS or fa == ta:
        return jsonify(error="pair"), 400
    amt = amount_arg(b, fa)
    pf, pt = asset_usd(fa), asset_usd(ta)
    if not amt or pf <= 0 or pt <= 0:
        return jsonify(error="amount"), 400
    out = floor_to(ta, amt * pf * (1 - cfg()["swap_fee"]) / pt)
    if out <= 0:
        return jsonify(error="too small"), 400
    if not debit(u["id"], fa, amt):
        return jsonify(error="balance"), 409
    credit(u["id"], ta, out)
    log_tx("swap:" + secrets.token_hex(6), uid=u["id"], type="swap", asset=fa, amount=amt, to=f"{out} {ta}", status="done")
    return jsonify(ok=True, out=out)


@app.post("/api/wallet/togame")
def api_wallet_togame():
    u, err = need_user()
    if err:
        return err
    b = request.get_json(silent=True) or {}
    a = b.get("asset")
    amt = amount_arg(b, a) if a in ASSETS else None
    pr = asset_usd(a) if amt else 0
    if not amt or pr <= 0:
        return jsonify(error="amount"), 400
    usd = round(amt * pr, 8)
    if not debit(u["id"], a, amt):
        return jsonify(error="balance"), 409
    db.players.update_one({"_id": u["id"]}, {"$inc": {"bonus": usd}})      # با همون مسیر امن پاداش‌ها به بازی می‌رسه
    log_tx("game:" + secrets.token_hex(6), uid=u["id"], type="togame", asset=a, amount=amt, to=f"${usd}", status="done")
    return jsonify(ok=True, usd=usd)


@app.post("/api/wallet/withdraw")
def api_wallet_withdraw():
    u, err = need_user()
    if err:
        return err
    if not ADMIN_ID or not cfg()["wd_on"]:
        return jsonify(error="disabled"), 503
    b = request.get_json(silent=True) or {}
    a = b.get("asset")
    amt = amount_arg(b, a) if a in ASSETS else None
    addr = (b.get("address") or "").strip()
    required = min_wd().get(a, 0)
    if not amt or required <= 0 or amt < required:
        return jsonify(error="min", min=required, asset=a, min_usd=WITHDRAW_MIN_USD,
                       price_usd=asset_usd(a)), 400
    if a != "STAR" and not re.fullmatch(r"(?:[EU]Q|kQ|0Q)[A-Za-z0-9_-]{46}|-?\d:[0-9a-fA-F]{64}", addr):
        return jsonify(error="address"), 400
    if not debit(u["id"], a, amt):
        return jsonify(error="balance"), 409
    wid = secrets.token_hex(5)
    log_tx("wd:" + wid, uid=u["id"], type="withdraw", asset=a, amount=amt, to=addr or "—", status="pending")
    tg("sendMessage", chat_id=ADMIN_ID, text=f"💸 درخواست برداشت\nکاربر: {display_name(u)} ({u['id']})\nمقدار: {amt} {a}\nمقصد: {addr or 'پرداخت از داخل تلگرام'}",
       reply_markup={"inline_keyboard": [[{"text": "✅ پرداخت شد", "callback_data": f"wd:ok:{wid}"},
                                          {"text": "❌ رد و برگشت وجه", "callback_data": f"wd:no:{wid}"}]]})
    return jsonify(ok=True)


def cashout_used(uid):
    t = now() - timedelta(days=1)
    return sum(float(x.get("usd", 0) or 0) for x in db.wtx.find({"uid": uid, "type": "cashout", "t": {"$gte": t}}))


@app.post("/api/wallet/cashout")
def api_wallet_cashout():
    """انتقال ارز ماین‌شده‌ی داخل بازی (Stars / TON / USD) به کیف پول واقعی (Stars / TON / USDT)"""
    u, err = need_user()
    if err:
        return err
    c = cfg()
    if not c["cashout_on"]:
        return jsonify(error="disabled"), 503
    b = request.get_json(silent=True) or {}
    coin = b.get("coin")
    if coin not in CASHOUT_MAP:
        return jsonify(error="amount"), 400
    a, uid = CASHOUT_MAP[coin], u["id"]
    p = db.players.find_one({"_id": uid}) or {}
    st = p.get("state")
    if not st:
        return jsonify(error="nostate"), 409
    have = float((st.get("wallet") or {}).get(coin, 0) or 0)
    try:
        want = have if b.get("amount") in (None, "all") else float(b.get("amount"))
    except (TypeError, ValueError):
        return jsonify(error="amount"), 400
    f = 10 ** DEC[a]
    amt = math.floor(min(want, have) * f) / f          # بدون epsilon تا هیچ‌وقت از موجودی بیشتر نشه
    pr = asset_usd(a)
    if pr <= 0:
        return jsonify(error="price"), 503
    usd = round(amt * pr, 8)
    if amt <= 0 or usd < c["cashout_min_usd"]:
        return jsonify(error="min", min=c["cashout_min_usd"]), 400
    left = c["cashout_daily_usd"] - cashout_used(uid)
    if usd > left + 1e-9:
        return jsonify(error="daily", left=max(0.0, left)), 409
    got = floor_to(a, amt * (1 - c["cashout_fee"]))
    if got <= 0:
        return jsonify(error="too small"), 400
    ok = db.players.find_one_and_update(
        {"_id": uid, f"state.wallet.{coin}": {"$gte": amt}},
        {"$inc": {f"state.wallet.{coin}": -amt, "state.cashed": usd}, "$set": {"cash_at": now()}})
    if not ok:
        return jsonify(error="balance"), 409
    credit(uid, a, got)
    log_tx("cash:" + secrets.token_hex(6), uid=uid, type="cashout", asset=a, amount=got, to=f"{amt} {coin}", usd=usd, status="done")
    return jsonify(ok=True, taken=amt, got=got, asset=a, usd=usd)


# ───────────────────────── پنل ادمین (فقط ADMIN_ID) ─────────────────────────
def admin_only():
    u = auth()
    if not u:
        return None, (jsonify(error="unauthorized"), 401)
    if not is_admin(u):
        return None, (jsonify(error="forbidden"), 403)
    return u, None


def usd_of(a, v):
    return float(v or 0) * asset_usd(a)


def user_row(p):
    st = p.get("state") or {}
    return {"id": p["_id"], "name": p.get("name", "ناشناس"), "worth": float(p.get("worth", 0) or 0), "bal": bal_of(p),
            "game_usd": float(st.get("usd", 0) or 0), "mined": {k: float((st.get("wallet") or {}).get(k, 0) or 0) for k in COINS},
            "miners": sum(1 for m in st.get("slots", []) if m), "shelves": st.get("shelves", 0), "banned": bool(p.get("banned")),
            "touch": int(aware(p["touch"]).timestamp() * 1000) if p.get("touch") else 0,
            "created": int(aware(p["created"]).timestamp() * 1000) if p.get("created") else 0,
            "active_refs": db.players.count_documents({"ref": p["_id"], "ref_done": True}),
            "ref": p.get("ref"), "cashed": float(st.get("cashed", 0) or 0)}


@app.get("/api/admin/overview")
def api_admin_overview():
    u, err = admin_only()
    if err:
        return err
    t = now()
    d1 = t - timedelta(days=1)
    total = db.players.count_documents({})
    played = db.players.count_documents({"state": {"$ne": None}})
    liab = {a: 0.0 for a in ASSETS}
    worth_sum = 0.0
    for p in db.players.find({}, {"bal": 1, "worth": 1}):
        worth_sum += float(p.get("worth", 0) or 0)
        for a, v in bal_of(p).items():
            liab[a] += v
    days = [(t - timedelta(days=i)).date() for i in range(6, -1, -1)]
    series = {d: {"d": d.strftime("%m/%d"), "n": 0, "dep": 0.0} for d in days}
    for p in db.players.find({"created": {"$gte": t - timedelta(days=7)}}, {"created": 1}):
        d = aware(p["created"]).date()
        if d in series:
            series[d]["n"] += 1
    dep24 = cash24 = wd24 = 0.0
    dep_n = 0
    pend_n, pend_usd = 0, 0.0
    for x in db.wtx.find({"t": {"$gte": t - timedelta(days=7)}}):
        a, ty = x.get("asset"), x.get("type")
        if a not in ASSETS:
            continue
        usd = usd_of(a, x.get("amount"))
        d = aware(x["t"]).date()
        if ty == "deposit":
            if d in series:
                series[d]["dep"] += usd
            if aware(x["t"]) >= d1:
                dep24 += usd
                dep_n += 1
        elif aware(x["t"]) >= d1:
            if ty == "cashout":
                cash24 += float(x.get("usd", 0) or 0)
            elif ty == "withdraw" and x.get("status") == "paid":
                wd24 += usd
    for x in db.wtx.find({"type": "withdraw", "status": "pending"}):
        pend_n += 1
        pend_usd += usd_of(x.get("asset"), x.get("amount"))
    lg = [{"ts": int(aware(x["t"]).timestamp() * 1000), "a": x.get("a"), "uid": x.get("uid"), "asset": x.get("asset"), "amount": x.get("amount")}
          for x in db.alog.find({}).sort("t", -1).limit(8)]
    return jsonify(users={"total": total, "played": played, "new24": db.players.count_documents({"created": {"$gte": d1}}),
                          "active24": db.players.count_documents({"touch": {"$gte": d1}})},
                   liab=liab, liab_usd=sum(usd_of(a, v) for a, v in liab.items()), worth_sum=worth_sum,
                   dep24_usd=dep24, dep24_n=dep_n, pend_n=pend_n, pend_usd=pend_usd, cash24_usd=cash24, wd24_usd=wd24,
                   series=[series[d] for d in days], log=lg, persistent=bool(MONGO_URI), ton_on=bool(TON_ADDRESS))


@app.get("/api/admin/withdrawals")
def api_admin_wds():
    u, err = admin_only()
    if err:
        return err
    status = request.args.get("status", "pending")
    q = {"type": "withdraw"}
    if status in ("pending", "paid", "rejected"):
        q["status"] = status
    rows = list(db.wtx.find(q).sort("t", -1).limit(40))
    names = {p["_id"]: p.get("name", "ناشناس") for p in db.players.find({"_id": {"$in": list({r["uid"] for r in rows})}}, {"name": 1})}
    return jsonify(items=[{"id": str(r["_id"])[3:], "uid": r["uid"], "name": names.get(r["uid"], "ناشناس"), "asset": r.get("asset"),
                           "amount": r.get("amount"), "usd": usd_of(r.get("asset"), r.get("amount")), "to": r.get("to"),
                           "status": r.get("status"), "ts": int(aware(r["t"]).timestamp() * 1000)} for r in rows])


@app.post("/api/admin/withdrawals/decide")
def api_admin_decide():
    u, err = admin_only()
    if err:
        return err
    b = request.get_json(silent=True) or {}
    wid = re.sub(r"[^0-9a-f]", "", str(b.get("id") or ""))[:20]
    res = decide_wd(wid, bool(b.get("ok")))
    if not res:
        return jsonify(error="done"), 409
    return jsonify(ok=True, status=res)


@app.get("/api/admin/users")
def api_admin_users():
    u, err = admin_only()
    if err:
        return err
    q = (request.args.get("q") or "").strip()[:40]
    if q.lstrip("@").isdigit():
        flt = {"_id": int(q.lstrip("@"))}
    elif q:
        flt = {"name": {"$regex": re.escape(q), "$options": "i"}}
    else:
        flt = {}
    rows = list(db.players.find(flt).sort("touch", -1).limit(25))
    return jsonify(items=[user_row(p) for p in rows], total=db.players.count_documents({}))


@app.get("/api/admin/user")
def api_admin_user():
    u, err = admin_only()
    if err:
        return err
    try:
        uid = int(request.args.get("uid"))
    except (TypeError, ValueError):
        return jsonify(error="uid"), 400
    p = db.players.find_one({"_id": uid})
    if not p:
        return jsonify(error="notfound"), 404
    txs = [{"type": x.get("type"), "asset": x.get("asset"), "amount": x.get("amount"), "status": x.get("status"), "to": x.get("to"),
            "ts": int(aware(x["t"]).timestamp() * 1000),
            "dir": x.get("sign") or (1 if x.get("type") in ("deposit", "cashout") else -1)}
           for x in db.wtx.find({"uid": uid}).sort("t", -1).limit(10)]
    return jsonify(user=user_row(p), txs=txs)


@app.post("/api/admin/adjust")
def api_admin_adjust():
    """شارژ/کسر دستی موجودی کاربر (TON / STAR / USDT) یا هدیه به بالانس بازی (GAME)"""
    u, err = admin_only()
    if err:
        return err
    b = request.get_json(silent=True) or {}
    try:
        uid, asset, amt = int(b.get("uid")), b.get("asset"), float(b.get("amount"))
    except (TypeError, ValueError):
        return jsonify(error="amount"), 400
    if amt != amt or amt == 0 or abs(amt) >= 1e9 or (asset not in ASSETS and asset != "GAME"):
        return jsonify(error="amount"), 400
    if not db.players.find_one({"_id": uid}, {"_id": 1}):
        return jsonify(error="notfound"), 404
    note = str(b.get("note") or "")[:60]
    if asset == "GAME":
        if amt < 0:
            return jsonify(error="amount"), 400
        db.players.update_one({"_id": uid}, {"$inc": {"bonus": round(amt, 8)}})        # با باز کردن بازی تحویل داده می‌شه
        log_tx("adm:" + secrets.token_hex(6), uid=uid, type="admin", asset="STAR", amount=0, to=f"هدیه ${amt} به بازی {note}", status="done", sign=1)
    else:
        v = floor_to(asset, abs(amt))
        if v <= 0:
            return jsonify(error="amount"), 400
        if amt > 0:
            credit(uid, asset, v)
        elif not debit(uid, asset, v):
            return jsonify(error="balance"), 409
        log_tx("adm:" + secrets.token_hex(6), uid=uid, type="admin", asset=asset, amount=v, to=note or "تنظیم توسط ادمین",
               status="done", sign=1 if amt > 0 else -1)
    alog("adjust", uid=uid, asset=asset, amount=amt)
    tg("sendMessage", chat_id=uid, text="🔔 موجودی حسابت توسط مدیریت به‌روز شد.", reply_markup=PLAY_KB)
    return jsonify(ok=True)


@app.post("/api/admin/ban")
def api_admin_ban():
    u, err = admin_only()
    if err:
        return err
    b = request.get_json(silent=True) or {}
    try:
        uid = int(b.get("uid"))
    except (TypeError, ValueError):
        return jsonify(error="uid"), 400
    if uid == ADMIN_ID:
        return jsonify(error="self"), 400
    r = db.players.update_one({"_id": uid}, {"$set": {"banned": bool(b.get("banned"))}})
    if not r.matched_count:
        return jsonify(error="notfound"), 404
    alog("ban" if b.get("banned") else "unban", uid=uid)
    return jsonify(ok=True)


@app.get("/api/admin/settings")
def api_admin_settings_get():
    u, err = admin_only()
    if err:
        return err
    return jsonify(cfg=cfg(), info={"ton_address": TON_ADDRESS, "star_usd": STAR_USD, "persistent": bool(MONGO_URI),
                                    "bot": BOT_USERNAME, "ton_price": (get_prices().get("TON") or {}).get("usd")})


@app.post("/api/admin/settings")
def api_admin_settings_set():
    u, err = admin_only()
    if err:
        return err
    try:
        done = set_cfg((request.get_json(silent=True) or {}).get("cfg") or {})
    except (ValueError, TypeError):
        return jsonify(error="value"), 400
    alog("settings", **{k: v for k, v in done.items()})
    return jsonify(ok=True, cfg=cfg())


def _broadcast(text, ids):
    sent = 0
    for uid in ids:
        if tg("sendMessage", chat_id=uid, text=text, reply_markup=PLAY_KB).get("ok"):
            sent += 1
        time.sleep(0.05)            # زیر سقف ۳۰ پیام در ثانیه‌ی تلگرام
    tg("sendMessage", chat_id=ADMIN_ID, text=f"📣 ارسال همگانی تموم شد: {sent} از {len(ids)} نفر")


@app.post("/api/admin/broadcast")
def api_admin_broadcast():
    u, err = admin_only()
    if err:
        return err
    b = request.get_json(silent=True) or {}
    text = str(b.get("text") or "").strip()[:3000]
    if not text:
        return jsonify(error="empty"), 400
    if b.get("test"):
        ok = tg("sendMessage", chat_id=ADMIN_ID, text=text, reply_markup=PLAY_KB).get("ok")
        return jsonify(ok=bool(ok), n=1)
    ids = [p["_id"] for p in db.players.find({"banned": {"$ne": True}}, {"_id": 1})]
    alog("broadcast", n=len(ids))
    threading.Thread(target=_broadcast, args=(text, ids), daemon=True).start()
    return jsonify(ok=True, n=len(ids))


def decide_wd(wid, approve):
    """تصمیم روی درخواست برداشت؛ اتمیک و فقط یک‌بار. خروجی: وضعیت جدید یا None اگه قبلاً بررسی شده"""
    new = "paid" if approve else "rejected"
    x = db.wtx.find_one_and_update({"_id": "wd:" + wid, "status": "pending"}, {"$set": {"status": new, "decided": now()}})
    if not x:
        return None
    if not approve:
        credit(x["uid"], x["asset"], x["amount"])
    tg("sendMessage", chat_id=x["uid"], text=(f"✅ برداشت {x['amount']} {x['asset']} پرداخت شد." if approve
                                              else f"❌ برداشت رد شد و {x['amount']} {x['asset']} به کیف پولت برگشت."))
    alog("withdraw_" + new, wid=wid, uid=x["uid"], asset=x["asset"], amount=x["amount"])
    return new


def wd_decide(cb):
    """دکمه‌های شیشه‌ای تلگرام برای ادمین"""
    if (cb.get("from") or {}).get("id") != ADMIN_ID:
        return
    _, act, wid = (cb.get("data") or "wd:x:x").split(":")[:3]
    res = decide_wd(wid, act == "ok")
    tg("answerCallbackQuery", callback_query_id=cb["id"], text="ثبت شد" if res else "قبلاً بررسی شده")
    if not res:
        return
    m = cb.get("message") or {}
    tg("editMessageReplyMarkup", chat_id=(m.get("chat") or {}).get("id"), message_id=m.get("message_id"), reply_markup={"inline_keyboard": []})


def stars_paid(msg):
    sp = msg["successful_payment"]
    if sp.get("currency") != "XTR":
        return
    uid, n = msg["from"]["id"], int(sp["total_amount"])
    tid = "dep:star:" + sp["telegram_payment_charge_id"]
    if (sp.get("invoice_payload") or "").startswith("depg:"):       # شارژ مستقیم بالانس بازی
        usd = round(n * STAR_USD, 8)
        if log_tx(tid, uid=uid, type="togame", asset="STAR", amount=n, to=f"${usd}", status="done"):
            db.players.update_one({"_id": uid}, {"$inc": {"bonus": usd}})
            tg("sendMessage", chat_id=uid, text=f"✅ {n} ⭐ پرداخت شد و ${usd:.2f} به بالانس بازیت اضافه شد.\nبازی رو باز کن 🎮", reply_markup=PLAY_KB)
        return
    if log_tx(tid, uid=uid, type="deposit", asset="STAR", amount=n, status="done"):
        credit(uid, "STAR", n)
        tg("sendMessage", chat_id=uid, text=f"✅ {n} ⭐ به کیف پولت اضافه شد.", reply_markup=PLAY_KB)


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
HELP = ("/start — ورود به بازی\n/invite — لینک دعوت دوستان\n/wallet — موجودی کیف پول\n/top — رده‌بندی ثروت\n/help — راهنما")


@app.post("/bot")
def bot_hook():
    if request.headers.get("X-Telegram-Bot-Api-Secret-Token") != BOT_SECRET:
        return "forbidden", 403
    upd = request.get_json(silent=True) or {}
    try:
        if upd.get("callback_query"):
            wd_decide(upd["callback_query"])
            return "ok"
        if upd.get("pre_checkout_query"):
            q = upd["pre_checkout_query"]
            tg("answerPreCheckoutQuery", pre_checkout_query_id=q["id"], ok=q.get("currency") == "XTR")
            return "ok"
        msg = upd.get("message")
        if msg and msg.get("successful_payment"):
            stars_paid(msg)
            return "ok"
        if not msg or msg.get("chat", {}).get("type") != "private":
            return "ok"
        chat_id = msg["chat"]["id"]
        parts = (msg.get("text") or "").strip().split()
        cmd = parts[0][1:].split("@")[0].lower() if parts and parts[0].startswith("/") else ""
        if cmd == "start":
            u = msg["from"]
            _, ref = register_ref(u["id"], display_name(u), parts[1] if len(parts) > 1 else "")
            if ref:
                tg("sendMessage", chat_id=chat_id,
                   text=f"🎁 با دعوت دوستت اومدی! بعد از رسیدن به ماموریت ۳ بازی، ${REF_WELCOME:.2f} هدیه می‌گیری.")
                tg("sendMessage", chat_id=ref,
                   text=f"👋 {display_name(u)} با لینک دعوت تو وارد شد!\nوقتی به ماموریت ۳ برسه، ${REF_BONUS:.2f} پاداش می‌گیری.",
                   reply_markup=PLAY_KB)
        if cmd == "top":
            tg("sendMessage", chat_id=chat_id, text=top_text(), reply_markup=PLAY_KB)
        elif cmd == "invite":
            link = ref_link(msg["from"]["id"])
            tg("sendMessage", chat_id=chat_id,
               text=("🔗 لینک دعوت تو:\n" + link) if link else "لینک دعوت هنوز آماده نیست.")
        elif cmd == "addbal" and ADMIN_ID and msg["from"]["id"] == ADMIN_ID:      # فقط ادمین، برای تست: /addbal TON 10
            try:
                a, v = parts[1].upper(), float(parts[2])
                a = "STAR" if a in ("STAR", "STARS") else a
                assert a in ASSETS and 0 < v < 1e6
                credit(ADMIN_ID, a, floor_to(a, v))
                tg("sendMessage", chat_id=chat_id, text=f"✅ {floor_to(a, v)} {a} به کیف پولت اضافه شد.", reply_markup=PLAY_KB)
            except Exception:
                tg("sendMessage", chat_id=chat_id, text="فرمت: /addbal TON 10  (TON | STAR | USDT)")
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
    global BOT_USERNAME
    if not BOT_USERNAME:
        BOT_USERNAME = (tg("getMe").get("result") or {}).get("username", "")
    r = tg("setWebhook", url=f"{BASE_URL}/bot", secret_token=BOT_SECRET,
           allowed_updates=["message", "callback_query", "pre_checkout_query"], drop_pending_updates=True)
    tg("setMyCommands", commands=[
        {"command": "start", "description": "ورود به بازی"},
        {"command": "invite", "description": "دعوت دوستان"},
        {"command": "wallet", "description": "کیف پول"},
        {"command": "top", "description": "رده‌بندی"},
        {"command": "help", "description": "راهنما"}])
    tg("setChatMenuButton", menu_button={"type": "web_app", "text": "بازی", "web_app": {"url": BASE_URL}})
    log.info("webhook: %s", r)


setup_bot()
threading.Thread(target=_scan_loop, daemon=True).start()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 10000)))
