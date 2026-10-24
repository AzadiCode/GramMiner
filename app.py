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
MIN_WD = {"TON": float(os.environ.get("MIN_WD_TON", "0.5")), "STAR": 100.0, "USDT": float(os.environ.get("MIN_WD_USDT", "1"))}
MIN_STARS_DEP = 10
ASSETS = ("TON", "STAR", "USDT")
DEC = {"TON": 9, "STAR": 0, "USDT": 6}
PRICE_TTL = 30          # ثانیه
OFFLINE_MAX = 4 * 3600  # باید با OFFLINE_MAX کلاینت یکی باشه
STATE_VERSION = 3
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
    out["rd"] = 1 if s.get("rd") else 0
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
    return jsonify(state=public_state(p), offline_sec=off, bonus_usd=b)


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
    ok, bucket = check_growth(p, worth, t)
    if not ok:
        log.warning("growth rejected uid=%s worth=%s last=%s", u["id"], worth, p.get("worth"))
        return jsonify(error="growth limit"), 409
    db.players.update_one({"_id": u["id"]}, {"$set": {
        "state": st, "worth": worth, "bucket": bucket, "bt": t, "saved": t, "touch": t,
        "name": display_name(u)}}, upsert=True)
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
    return jsonify(top=top, rank=rank, total=db.players.count_documents(played))


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
             "status": x.get("status"), "to": x.get("to"), "ts": int(aware(x["t"]).timestamp() * 1000)}
            for x in db.wtx.find({"uid": uid}).sort("t", -1).limit(12)]
    rank = None
    if p.get("state"):
        rank = db.players.count_documents({"state": {"$ne": None}, "worth": {"$gt": p.get("worth", 0)}}) + 1
    return jsonify(bal=bal_of(p), hist=hist, rank=rank, total=db.players.count_documents({"state": {"$ne": None}}),
                   worth=p.get("worth", 0), usd={a: asset_usd(a) for a in ASSETS}, fee=SWAP_FEE, min_wd=MIN_WD,
                   min_stars=MIN_STARS_DEP, ton_address=TON_ADDRESS, memo=f"MIKO{uid}", wd_on=bool(ADMIN_ID))


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
    r = tg("createInvoiceLink", title="شارژ Stars", description=f"واریز {n} استارز به کیف پول بازی",
           payload=f"dep:{u['id']}", currency="XTR", prices=[{"label": "Stars", "amount": n}])
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
    out = floor_to(ta, amt * pf * (1 - SWAP_FEE) / pt)
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
    if not ADMIN_ID:
        return jsonify(error="disabled"), 503
    b = request.get_json(silent=True) or {}
    a = b.get("asset")
    amt = amount_arg(b, a) if a in ASSETS else None
    addr = (b.get("address") or "").strip()
    if not amt or amt < MIN_WD[a]:
        return jsonify(error="min", min=MIN_WD.get(a)), 400
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


def wd_decide(cb):
    """تصمیم ادمین روی درخواست برداشت"""
    if (cb.get("from") or {}).get("id") != ADMIN_ID:
        return
    _, act, wid = (cb.get("data") or "wd:x:x").split(":")[:3]
    new = "paid" if act == "ok" else "rejected"
    x = db.wtx.find_one_and_update({"_id": "wd:" + wid, "status": "pending"}, {"$set": {"status": new}})
    tg("answerCallbackQuery", callback_query_id=cb["id"], text="ثبت شد" if x else "قبلاً بررسی شده")
    if not x:
        return
    if new == "rejected":
        credit(x["uid"], x["asset"], x["amount"])
    tg("sendMessage", chat_id=x["uid"], text=(f"✅ برداشت {x['amount']} {x['asset']} پرداخت شد." if new == "paid"
                                              else f"❌ برداشت رد شد و {x['amount']} {x['asset']} به کیف پولت برگشت."))
    m = cb.get("message") or {}
    tg("editMessageReplyMarkup", chat_id=(m.get("chat") or {}).get("id"), message_id=m.get("message_id"), reply_markup={"inline_keyboard": []})


def stars_paid(msg):
    sp = msg["successful_payment"]
    if sp.get("currency") != "XTR":
        return
    uid, n = msg["from"]["id"], int(sp["total_amount"])
    if log_tx("dep:star:" + sp["telegram_payment_charge_id"], uid=uid, type="deposit", asset="STAR", amount=n, status="done"):
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
