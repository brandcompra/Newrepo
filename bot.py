import asyncio
import difflib
import hashlib
import hmac
import html
import json
import logging
import math
import os
import re
import sqlite3
import time
import unicodedata
from datetime import datetime
from urllib.parse import parse_qsl
from zoneinfo import ZoneInfo

import aiohttp
from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ChatType, ParseMode
from aiogram.filters import Command, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    Message,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
    WebAppInfo,
)

logging.basicConfig(level=logging.INFO)

# ---------- Ayarlar (hostingdə "Variables" bölməsində yazılır) ----------
BOT_TOKEN = os.environ["BOT_TOKEN"]
GROUP_ID = int(os.environ["GROUP_ID"])                          # taksi sürücüləri qrupu
COURIER_GROUP_ID = int(os.environ.get("COURIER_GROUP_ID", "0")) or GROUP_ID  # kuryer qrupu (yoxdursa eyni qrup)
ADMIN_ID = int(os.environ["ADMIN_ID"])
ORS_KEY = os.environ["ORS_KEY"]
DB_PATH = os.environ.get("DB_PATH", "taxi.db")
PORT = int(os.environ.get("PORT", "8080"))
WEBAPP_URL = os.environ.get("WEBAPP_URL", "").strip().rstrip("/")
if WEBAPP_URL and not WEBAPP_URL.startswith("http"):
    WEBAPP_URL = "https://" + WEBAPP_URL

RADIUS_KM = float(os.environ.get("RADIUS_KM", "1.3"))
LOC_MAX_AGE_MIN = int(os.environ.get("LOC_MAX_AGE_MIN", "12"))
CANCEL_WARN = int(os.environ.get("CANCEL_WARN", "3"))           # 24 saatda bu qədər imtinadan sonra admin xəbərdar olunur
BAKU_LAT, BAKU_LON = 40.4093, 49.8671
GEO_RADIUS_KM = float(os.environ.get("GEO_RADIUS_KM", "25"))

# ---------- Tarif ----------
PER_KM = float(os.environ.get("PER_KM", "0.2"))
MIN_PRICE = float(os.environ.get("MIN_PRICE", "2.0"))
PEAK_MULT = float(os.environ.get("PEAK_MULT", "1.3"))
PEAK_HOURS = [(7 * 60 + 30, 10 * 60), (17 * 60, 20 * 60)]
TZ = ZoneInfo("Asia/Baku")

ORS_BASE = "https://api.heigit.org/openrouteservice/v2"
GEOCODE_URL = "https://api.heigit.org/pelias/v1/search"

router = Router()
pending: dict[int, dict] = {}


def group_for(kind: str) -> int:
    return COURIER_GROUP_ID if kind == "courier" else GROUP_ID


def is_group_chat(chat_id) -> bool:
    return chat_id in (GROUP_ID, COURIER_GROUP_ID)


# ---------- Baza ----------
def execute(sql, args=()):
    conn = sqlite3.connect(DB_PATH)
    try:
        cur = conn.execute(sql, args)
        conn.commit()
        return cur.rowcount, cur.lastrowid
    finally:
        conn.close()


def fetch(sql, args=()):
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    try:
        return conn.execute(sql, args).fetchone()
    finally:
        conn.close()


def fetchall(sql, args=()):
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    try:
        return conn.execute(sql, args).fetchall()
    finally:
        conn.close()


def init_db():
    conn = sqlite3.connect(DB_PATH)
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS drivers(
            user_id INTEGER PRIMARY KEY,
            name TEXT, phone TEXT, car TEXT, plate TEXT,
            approved INTEGER DEFAULT 0,
            lat REAL, lon REAL, loc_time REAL,
            online INTEGER DEFAULT 0,
            kind TEXT DEFAULT 'taxi'
        );
        CREATE TABLE IF NOT EXISTS orders(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            customer_id INTEGER, customer_name TEXT,
            plat REAL, plon REAL, dlat REAL, dlon REAL, dest_label TEXT,
            km REAL, price REAL,
            status TEXT DEFAULT 'new',
            driver_id INTEGER, group_msg_id INTEGER,
            created TEXT,
            kind TEXT DEFAULT 'taxi', note TEXT,
            cust_msg_id INTEGER, drv_msg_id INTEGER
        );
        CREATE TABLE IF NOT EXISTS notifs(
            order_id INTEGER, chat_id INTEGER, msg_id INTEGER, driver_id INTEGER
        );
        CREATE TABLE IF NOT EXISTS order_cancels(
            order_id INTEGER, driver_id INTEGER, who TEXT, created REAL
        );
        """
    )
    # köhnə bazadan yeniləmə (sütun varsa xəta verməz)
    for table, col, typ in (
        ("drivers", "lat", "REAL"), ("drivers", "lon", "REAL"), ("drivers", "loc_time", "REAL"),
        ("drivers", "online", "INTEGER DEFAULT 0"), ("drivers", "kind", "TEXT DEFAULT 'taxi'"),
        ("orders", "kind", "TEXT DEFAULT 'taxi'"), ("orders", "note", "TEXT"),
        ("orders", "cust_msg_id", "INTEGER"), ("orders", "drv_msg_id", "INTEGER"),
    ):
        try:
            conn.execute(f"ALTER TABLE {table} ADD COLUMN {col} {typ}")
        except sqlite3.OperationalError:
            pass
    conn.commit()
    conn.close()


# ---------- Məsafə və format ----------
def dist_km(lat1, lon1, lat2, lon2) -> float:
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dphi = p2 - p1
    dl = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def fmt_num(x, nd=1) -> str:
    return f"{x:.{nd}f}".replace(".", ",")


def fmt_dist(km: float) -> str:
    """1 km-dən azdırsa metr (750 metr), çoxdursa km (1,3 km)."""
    m = int(round(km * 100) * 10)
    if m < 1000:
        return f"{max(m, 10)} metr"
    return f"{fmt_num(km)} km"


def nearby_drivers(lat, lon, kind="taxi"):
    """Düz xətt radiusundakı təsdiqlənmiş, onlayn, yeri təzə olan işçilər: [(km, sürücü)]."""
    rows = fetchall(
        "SELECT * FROM drivers WHERE approved=1 AND online=1 AND kind=? AND lat IS NOT NULL AND loc_time>?",
        (kind, time.time() - LOC_MAX_AGE_MIN * 60),
    )
    res = []
    for d in rows:
        km = dist_km(lat, lon, d["lat"], d["lon"])
        if km <= RADIUS_KM:
            res.append((km, d))
    res.sort(key=lambda x: x[0])
    return res


async def road_distances(plat, plon, drivers):
    """Hər sürücüdən götürülmə nöqtəsinə yol məsafəsi (km); alınmasa düz xətt."""
    fallback = [dist_km(plat, plon, d["lat"], d["lon"]) for d in drivers]
    if not drivers:
        return []
    locs = [[plon, plat]] + [[d["lon"], d["lat"]] for d in drivers]
    body = {"locations": locs, "sources": list(range(1, len(locs))), "destinations": [0],
            "metrics": ["distance"], "units": "km"}
    try:
        async with aiohttp.ClientSession() as s:
            async with s.post(f"{ORS_BASE}/matrix/driving-car", json=body,
                              headers={"Authorization": ORS_KEY},
                              timeout=aiohttp.ClientTimeout(total=20)) as r:
                data = await r.json()
        return [row[0] if row and row[0] is not None else fb for row, fb in zip(data["distances"], fallback)]
    except Exception:
        logging.exception("matrix error")
        return fallback


def calc_price(km: float):
    now = datetime.now(TZ)
    minutes = now.hour * 60 + now.minute
    mult = 1.0
    for a, b in PEAK_HOURS:
        if a <= minutes < b:
            mult = PEAK_MULT
    return round(max(MIN_PRICE, km * PER_KM * mult), 1), mult


async def route_km(plat, plon, dlat, dlon):
    try:
        async with aiohttp.ClientSession() as s:
            async with s.post(f"{ORS_BASE}/directions/driving-car",
                              json={"coordinates": [[plon, plat], [dlon, dlat]]},
                              headers={"Authorization": ORS_KEY},
                              timeout=aiohttp.ClientTimeout(total=20)) as r:
                data = await r.json()
        return data["routes"][0]["summary"]["distance"] / 1000
    except Exception:
        logging.exception("route error")
        return None


# ---------- Ünvan axtarışı (Bakı daxilində, latın hərfləri ilə də) ----------
_TR = str.maketrans({
    "ə": "e", "ı": "i", "ş": "s", "ç": "c", "ö": "o", "ü": "u", "ğ": "g",
    "Ə": "e", "İ": "i", "Ş": "s", "Ç": "c", "Ö": "o", "Ü": "u", "Ğ": "g",
})
_SKIP = {"baku", "baki", "azerbaijan", "azerbaycan"}


def norm(s) -> str:
    """Azərbaycan hərflərini və diakritikləri latın hərflərinə çevirib kiçildir."""
    t = unicodedata.normalize("NFKD", str(s or "").translate(_TR))
    return "".join(c for c in t if not unicodedata.combining(c)).lower()


# Yalnız düzgün yazılış siyahısı (koordinat yoxdur): latın hərfləri ilə yazılanı düzəltmək üçün
AZ_NAMES = [
    "Binəqədi", "Xətai", "Xəzər", "Qaradağ", "Nərimanov", "Nəsimi", "Nizami", "Pirallahı", "Sabunçu",
    "Səbail", "Suraxanı", "Yasamal", "Dərnəgül", "Əhmədli", "Neftçilər", "Memar Əcəmi", "Gənclik",
    "Elmlər Akademiyası", "Xalqlar Dostluğu", "28 May", "Koroğlu", "Qara Qarayev", "Həzi Aslanov",
    "Avtovağzal", "Ulduz", "İçərişəhər", "Sahil", "Cəfər Cabbarlı", "20 Yanvar", "İnşaatçılar", "Bakmil",
    "Şah İsmayıl Xətai", "Nəriman Nərimanov", "Bayıl", "Badamdar", "Bibiheybət", "Bilgəh", "Mərdəkan",
    "Şüvəlan", "Buzovna", "Zığ", "Qala", "Türkan", "Pirşağı", "Novxanı", "Binə", "Əmircan", "Balaxanı",
    "Zabrat", "Maştağa", "Bülbülə", "Ramana", "Hövsan", "Lökbatan", "Xırdalan", "Masazır", "Biləcəri",
    "Günəşli", "Yeni Günəşli", "Sulutəpə", "Kürdəxanı", "Mehdiabad", "Şağan", "Şıxov", "Bakıxanov",
    "Əzizbəyov", "Qobu", "Fatmayı", "Hökməli", "Dənizkənarı Milli Park", "Fəvvarələr meydanı",
    "Heydər Əliyev Hava Limanı", "Bakı Dəmir Yol Vağzalı", "Gənclik Mall", "Park Bulvar",
    "Azadlıq prospekti", "Tbilisi prospekti", "Neftçilər prospekti", "Nizami küçəsi", "Bəhruz Nuriyev",
    "Rəşid Behbudov", "Üzeyir Hacıbəyov", "Fizuli", "Xaqani", "Səməd Vurğun", "Şərifzadə",
    "Zərifə Əliyeva", "Cavadxan", "Mir Cəlal", "Bakı Olimpiya Stadionu", "Sumqayıt", "Yaşıl Bazar",
    "Təzə Bazar", "Azərbaycan prospekti", "Bülbül prospekti", "Heydər Əliyev prospekti",
    "Babək prospekti", "Mehdi Hüseyn", "Yusif Səfərov", "Məktəb", "Xəstəxana", "Poliklinika",
]
_FOLDED_NAMES = {norm(n): n for n in AZ_NAMES}
_SINGLE_KEYS = [k for k in _FOLDED_NAMES if " " not in k and len(k) >= 5]


def correct_query(text: str) -> str:
    """Latın hərfləri ilə yazılmış tanınmış adları düzgün Azərbaycan yazılışına çevirir
    (dernegul -> Dərnəgül, neftciler -> Neftçilər, xetai -> Xətai)."""
    words = text.split()
    folded = [norm(w) for w in words]
    out, i = [], 0
    while i < len(words):
        hit = None
        for n in (4, 3, 2, 1):
            if i + n <= len(words):
                key = " ".join(folded[i:i + n])
                if key in _FOLDED_NAMES:
                    hit = (n, _FOLDED_NAMES[key])
                    break
        if hit:
            out.append(hit[1])
            i += hit[0]
            continue
        w = folded[i]
        if len(w) >= 5 and w.isalpha():
            m = difflib.get_close_matches(w, _SINGLE_KEYS, n=1, cutoff=0.86)
            if m:
                out.append(_FOLDED_NAMES[m[0]])
                i += 1
                continue
        out.append(words[i])
        i += 1
    return " ".join(out)


def schwa_variants(text: str):
    """Xəritə axtarışı ə hərfini e ilə eyniləşdirmir: e->ə olan variantlar."""
    words = text.split()

    def conv(w, keep_first):
        if not (w.isascii() and "e" in w.lower() and not w.isdigit()):
            return w
        out, seen = [], False
        for ch in w:
            if ch in "eE":
                if keep_first and not seen:
                    seen = True
                    out.append(ch)
                else:
                    out.append("ə" if ch == "e" else "Ə")
            else:
                out.append(ch)
        return "".join(out)

    v_all = " ".join(conv(w, False) for w in words)
    v_keep = " ".join(conv(w, True) for w in words)
    res = []
    for v in (v_all, v_keep):
        if v != text and v not in res:
            res.append(v)
    return res


def query_tokens(text: str):
    return [t for t in re.split(r"\W+", norm(text)) if (len(t) >= 2 or t.isdigit()) and t not in _SKIP]


def match_score(tokens, label: str):
    """Sorğudakı sözlərin neçə faizi adda var (1.0 = hamısı).
    Rəqəmlər tam uyğun olmalıdır (27 sorğusu 272-ni tapmır); uyğun deyilsə None qaytarır."""
    if not tokens:
        return 0.0
    nl = norm(label)
    label_nums = set(re.findall(r"\d+", nl))
    nums = [t for t in tokens if t.isdigit()]
    if nums and not all(n in label_nums for n in nums):
        return None
    alpha = [t for t in tokens if not t.isdigit()]

    def hit(t):  # "bazarı" sorğusu "bazar" adını da tapsın
        return t in nl or (len(t) >= 5 and (t[:-1] in nl or t[:-2] in nl))

    return (len(nums) + sum(1 for t in alpha if hit(t))) / len(tokens)


async def _pelias(q: str):
    params = {
        "api_key": ORS_KEY, "text": q, "boundary.country": "AZ",
        "boundary.circle.lat": str(BAKU_LAT), "boundary.circle.lon": str(BAKU_LON),
        "boundary.circle.radius": str(GEO_RADIUS_KM), "size": "10",
    }
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get(GEOCODE_URL, params=params, timeout=aiohttp.ClientTimeout(total=20)) as r:
                data = await r.json()
        return data.get("features") or []
    except Exception:
        logging.exception("geocode error")
        return []


def _collect(found: dict, features, toks, text):
    for f in features:
        try:
            lon, lat = f["geometry"]["coordinates"]
        except Exception:
            continue
        if dist_km(BAKU_LAT, BAKU_LON, lat, lon) > GEO_RADIUS_KM:
            continue
        label = f.get("properties", {}).get("label") or text
        score = match_score(toks, label)
        if score is None:
            continue
        key = (round(lat, 4), round(lon, 4))
        if key in found:
            continue
        nl = norm(label)
        found[key] = {"lat": lat, "lon": lon, "label": label, "score": score,
                      "baku": ("baku" in nl or "baki" in nl), "order": len(found)}


async def geocode(text: str):
    """Ünvanı axtarır (yalnız Bakı radiusu). Nəticə: [{lat, lon, label, score, baku}], ən çoxu 5."""
    toks = query_tokens(text)
    primary = correct_query(text)
    found: dict = {}
    stage1 = [f"{primary}, Baku, Azerbaijan"] + ([primary] if primary else [])
    for feats in await asyncio.gather(*[_pelias(q) for q in stage1]):
        _collect(found, feats, toks, text)
    if not any(c["score"] >= 1 for c in found.values()):
        variants = schwa_variants(primary)[:2]
        if variants:
            for feats in await asyncio.gather(*[_pelias(v) for v in variants]):
                _collect(found, feats, toks, text)
    cands = sorted(found.values(), key=lambda c: (-c["score"], not c["baku"], c["order"]))
    return cands[:5]


# ---------- Mesaj köməkçiləri ----------
def esc(s) -> str:
    return html.escape(str(s or ""))


def waze(lat, lon) -> str:
    return f"https://waze.com/ul?ll={lat:.6f},{lon:.6f}&navigate=yes"


def kind_title(kind) -> str:
    return "Kuryer" if kind == "courier" else "Taksi"


def order_text(o, road_km=None) -> str:
    """Sürücüyə gedən mesaj. İki link heç vaxt alt-alta düşmür, son sətir müştərinin yolunun məsafəsidir.
    Fərdi mesajda götürülmə yerinin yanında mötərizədə sürücüdən yol məsafəsi yazılır."""
    near = f" ({fmt_dist(road_km)})" if road_km is not None else ""
    lines = [
        f"<b>{kind_title(o['kind'])} sifarişi #{o['id']}</b>",
        f"<a href=\"{waze(o['plat'], o['plon'])}\">Götürülmə yeri</a>{near}",
        f"Ödəniş məbləği: {fmt_num(o['price'])} ₼",
    ]
    if o["note"]:
        lines.append(f"Qeyd: {esc(o['note'])}")
    lines.append(f"<a href=\"{waze(o['dlat'], o['dlon'])}\">Gediləcək yer</a>: {esc(o['dest_label'])}")
    lines.append(f"Məsafə: {fmt_num(o['km'])} km")
    return "\n".join(lines)


def accept_kb(oid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Qəbul et", callback_data=f"acc:{oid}"),
        InlineKeyboardButton(text="❌ İmtina", callback_data=f"rej:{oid}"),
    ]])


def role_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="1. Sürücüyəm", callback_data="role:driver")],
        [InlineKeyboardButton(text="2. Kuryerəm", callback_data="role:courier")],
        [InlineKeyboardButton(text="3. Müştəriyəm", callback_data="role:customer")],
    ])


def customer_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="1. Taksi çağır", callback_data="order:taxi")],
        [InlineKeyboardButton(text="2. Kuryer çağır", callback_data="order:courier")],
    ])


def start_kb():
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="📍 Yerimi göndər", request_location=True)]],
        resize_keyboard=True,
    )


def order_customer_kb(oid: int) -> InlineKeyboardMarkup:
    rows = []
    if WEBAPP_URL:
        rows.append([InlineKeyboardButton(text="📍 İzlə", web_app=WebAppInfo(url=f"{WEBAPP_URL}/map?order={oid}"))])
    rows.append([InlineKeyboardButton(text="🚫 İmtina et", callback_data=f"cxa:{oid}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def order_driver_kb(oid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Sifariş bitdi", callback_data=f"fin:{oid}")],
        [InlineKeyboardButton(text="🚫 İmtina et", callback_data=f"dcx:{oid}")],
    ])


def set_driver_live(uid: int, loc) -> int:
    n, _ = execute(
        "UPDATE drivers SET online=1, lat=?, lon=?, loc_time=? WHERE user_id=? AND approved=1",
        (loc.latitude, loc.longitude, time.time(), uid),
    )
    return n


def update_driver_location(uid: int, loc) -> int:
    n, _ = execute(
        "UPDATE drivers SET lat=?, lon=?, loc_time=? WHERE user_id=? AND approved=1 AND online=1",
        (loc.latitude, loc.longitude, time.time(), uid),
    )
    return n


def recent_cancels(driver_id: int, who: str) -> int:
    row = fetch(
        "SELECT COUNT(*) AS c FROM order_cancels WHERE driver_id=? AND who=? AND created>?",
        (driver_id, who, time.time() - 86400),
    )
    return row["c"] if row else 0


# ---------- Xəritə (Telegram mini səhifə) ----------
LAT_STEP, LON_STEP = 0.0009, 0.0012   # təxminən 100 metr


def snap(lat, lon):
    """Koordinatı ~100 metrlik şəbəkə xanasının mərkəzinə yuvarlaqlaşdırır (ümumi xəritə üçün)."""
    return ((math.floor(lat / LAT_STEP) + 0.5) * LAT_STEP, (math.floor(lon / LON_STEP) + 0.5) * LON_STEP)


def verify_init_data(init_data: str, token: str, max_age=86400, now=None):
    """Telegram mini səhifənin imzasını yoxlayır; düzgündürsə istifadəçi ID-sini qaytarır."""
    try:
        pairs = dict(parse_qsl(init_data or "", keep_blank_values=True))
        got = pairs.pop("hash", None)
        if not got:
            return None
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", token.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, got):
            return None
        if (now or time.time()) - int(pairs.get("auth_date", "0")) > max_age:
            return None
        return int(json.loads(pairs["user"])["id"])
    except Exception:
        return None


MAP_PAGE = """<!doctype html>
<html lang="az"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no">
<title>Xəritə</title>
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.css">
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.js"></script>
<style>
:root{--bg:#fff;--fg:#111827;--bar:#f3f4f6;--mut:#6b7280}
@media (prefers-color-scheme: dark){:root{--bg:#111827;--fg:#f3f4f6;--bar:#1f2937;--mut:#9ca3af}}
html,body{margin:0;height:100%;background:var(--bg);color:var(--fg);font:15px/1.4 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
#bar{position:fixed;top:0;left:0;right:0;z-index:1000;box-sizing:border-box;height:62px;padding:10px 16px;background:var(--bar);box-shadow:0 1px 4px rgba(0,0,0,.25)}
#status{font-weight:600}
#hint{color:var(--mut);font-size:12px;margin-top:2px}
#map{position:absolute;top:62px;bottom:0;left:0;right:0}
.pin{font-size:26px;line-height:30px;text-align:center;filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))}
</style></head><body>
<div id="bar"><div id="status">Yüklənir…</div><div id="hint"></div></div>
<div id="map"></div>
<script>
(function(){
var tg = window.Telegram && window.Telegram.WebApp;
if (tg) { try { tg.ready(); tg.expand(); } catch(e){} }
var q = new URLSearchParams(location.search);
var order = q.get('order');
var kind = q.get('kind') === 'courier' ? 'courier' : 'taxi';
var EMO = {taxi: '🚕', courier: '🛵'};
var statusEl = document.getElementById('status'), hintEl = document.getElementById('hint');
var map = L.map('map').setView([40.4093, 49.8671], 12);
L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {maxZoom: 19, attribution: '&copy; OpenStreetMap'}).addTo(map);
var layer = L.layerGroup().addTo(map);
var fitted = false, timer = null;
function pin(lat, lon, emoji){
  return L.marker([lat, lon], {icon: L.divIcon({className: 'pin', html: emoji, iconSize: [30, 30], iconAnchor: [15, 15]})});
}
function api(path){
  return fetch(path, {headers: {'X-Init-Data': tg ? tg.initData : ''}, cache: 'no-store'}).then(function(r){
    if (!r.ok) throw new Error(String(r.status));
    return r.json();
  });
}
function fail(e){
  statusEl.textContent = (e && e.message === '401') ? 'Bu səhifə yalnız Telegram daxilində açılır.' : 'Bağlantı xətası, yenidən cəhd edilir…';
}
function online(){
  api('/api/online?kind=' + kind).then(function(d){
    layer.clearLayers();
    d.drivers.forEach(function(p){ pin(p.lat, p.lon, EMO[kind]).addTo(layer); });
    statusEl.textContent = d.count ? ('Onlayn ' + (kind === 'courier' ? 'kuryer' : 'taksi') + ': ' + d.count) : 'Hazırda onlayn yoxdur';
    hintEl.textContent = 'Yerlər təxminən (~100 m) göstərilir';
  }).catch(fail);
}
function track(){
  api('/api/track?order=' + encodeURIComponent(order)).then(function(d){
    if (d.status !== 'accepted') {
      clearInterval(timer);
      statusEl.textContent = d.status === 'done' ? 'Sifariş tamamlandı' : (d.status === 'cancelled' ? 'Sifariş ləğv edildi' : 'Sifariş aktiv deyil');
      hintEl.textContent = '';
      return;
    }
    layer.clearLayers();
    var pts = [];
    pin(d.pickup.lat, d.pickup.lon, '📍').addTo(layer); pts.push([d.pickup.lat, d.pickup.lon]);
    pin(d.dest.lat, d.dest.lon, '🏁').addTo(layer); pts.push([d.dest.lat, d.dest.lon]);
    if (d.driver) {
      pin(d.driver.lat, d.driver.lon, EMO[d.kind] || '🚕').addTo(layer);
      pts.push([d.driver.lat, d.driver.lon]);
      statusEl.textContent = (d.kind === 'courier' ? 'Kuryer' : 'Sürücü') + ' yoldadır';
      hintEl.textContent = d.driver.age > 60 ? ('Yer ' + d.driver.age + ' saniyə əvvəl yenilənib') : 'Canlı izləmə';
    } else {
      statusEl.textContent = 'Yer hələ gəlməyib';
      hintEl.textContent = '';
    }
    if (!fitted && pts.length) { map.fitBounds(pts, {padding: [40, 40], maxZoom: 16}); fitted = true; }
  }).catch(fail);
}
if (order) { track(); timer = setInterval(track, 4000); } else { online(); timer = setInterval(online, 10000); }
})();
</script></body></html>"""


async def web_health(request):
    return web.Response(text="ok")


async def web_page(request):
    return web.Response(text=MAP_PAGE, content_type="text/html", charset="utf-8")


def _auth(request):
    return verify_init_data(request.headers.get("X-Init-Data", ""), BOT_TOKEN)


async def api_online(request):
    if _auth(request) is None:
        return web.json_response({"error": "auth"}, status=401)
    kind = "courier" if request.query.get("kind") == "courier" else "taxi"
    rows = fetchall(
        "SELECT lat, lon FROM drivers WHERE approved=1 AND online=1 AND kind=? AND lat IS NOT NULL AND loc_time>?",
        (kind, time.time() - LOC_MAX_AGE_MIN * 60),
    )
    pts = []
    for r in rows:
        la, lo = snap(r["lat"], r["lon"])   # ümumi xəritədə dəqiq yer göstərilmir
        pts.append({"lat": la, "lon": lo})
    return web.json_response({"count": len(pts), "drivers": pts}, headers={"Cache-Control": "no-store"})


async def api_track(request):
    uid = _auth(request)
    if uid is None:
        return web.json_response({"error": "auth"}, status=401)
    try:
        oid = int(request.query.get("order", ""))
    except ValueError:
        return web.json_response({"error": "bad"}, status=400)
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    if not o or o["customer_id"] != uid:           # dəqiq yeri yalnız sifarişin müştərisi görür
        return web.json_response({"error": "forbidden"}, status=403)
    if o["status"] != "accepted":
        return web.json_response({"status": o["status"]}, headers={"Cache-Control": "no-store"})
    d = fetch("SELECT lat, lon, loc_time FROM drivers WHERE user_id=?", (o["driver_id"],))
    drv = None
    if d and d["lat"] is not None:
        drv = {"lat": d["lat"], "lon": d["lon"], "age": int(time.time() - (d["loc_time"] or 0))}
    return web.json_response({
        "status": "accepted", "kind": o["kind"], "driver": drv,
        "pickup": {"lat": o["plat"], "lon": o["plon"]},
        "dest": {"lat": o["dlat"], "lon": o["dlon"]},
    }, headers={"Cache-Control": "no-store"})


async def start_web():
    app = web.Application()
    app.add_routes([
        web.get("/", web_health), web.get("/map", web_page),
        web.get("/api/online", api_online), web.get("/api/track", api_track),
    ])
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()
    return runner


# ---------- Əsas menyu və rollar ----------
LIVE_HELP = (
    "📎 → <b>Yer</b> (Location) → <b>Canlı yeri paylaş</b> (Share Live Location) → <b>Mən söndürənə qədər</b> seçin.\n"
    "Paylaşım başlayan kimi avtomatik onlayn olacaqsınız.\n"
    "Android-də Telegram üçün məkan icazəsi «Həmişə icazə ver» olmalıdır, yoxsa tətbiq bağlananda yer dayanır."
)


@router.message(Command("start", "menu"), F.chat.type == ChatType.PRIVATE)
async def start(m: Message, state: FSMContext):
    await state.clear()
    pending.pop(m.from_user.id, None)
    await m.answer("Salam! 👋 Kimsiniz?\n\n1. Sürücüyəm\n2. Kuryerəm\n3. Müştəriyəm", reply_markup=role_kb())


@router.message(Command("id"))
async def get_id(m: Message):
    await m.answer(f"Chat ID: <code>{m.chat.id}</code>")


@router.callback_query(F.data.in_({"role:driver", "role:courier"}))
async def role_worker(cb: CallbackQuery):
    kind = "courier" if cb.data == "role:courier" else "taxi"
    d = fetch("SELECT * FROM drivers WHERE user_id=?", (cb.from_user.id,))
    registered = d is not None and d["kind"] == kind
    lines = [f"<b>{'🛵 Kuryer' if kind == 'courier' else '🚕 Sürücü'} bölməsi</b>", ""]
    if not registered:
        lines.append("Əvvəlcə qeydiyyatdan keçin. Admin təsdiqləyəndən sonra işə başlaya bilərsiniz.")
    elif not d["approved"]:
        lines.append("Qeydiyyatınız admin təsdiqini gözləyir.")
    else:
        lines.append("Siz təsdiqlənmisiniz.")
    lines += ["", "İşə başlamaq: 🟢 Onlayn düyməsi və ya /onlayn", "Dayandırmaq: 🔴 Oflayn düyməsi və ya /oflayn"]
    rows = [[InlineKeyboardButton(text="🟢 Onlayn", callback_data="on"),
             InlineKeyboardButton(text="🔴 Oflayn", callback_data="off")]]
    if not registered:
        rows.append([InlineKeyboardButton(text="📝 Qeydiyyat", callback_data=f"reg:{kind}")])
    await cb.message.edit_text("\n".join(lines), reply_markup=InlineKeyboardMarkup(inline_keyboard=rows))
    await cb.answer()


async def _go_online(target: Message, uid: int):
    d = fetch("SELECT * FROM drivers WHERE user_id=? AND approved=1", (uid,))
    if not d:
        await target.answer("Əvvəlcə qeydiyyatdan keçin (/driver sürücü, /kuryer kuryer) və admin təsdiqini gözləyin.")
        return
    await target.answer("🟢 İşə başlamaq üçün canlı yerinizi göndərin:\n\n" + LIVE_HELP)


async def _go_offline(target: Message, uid: int):
    execute("UPDATE drivers SET online=0 WHERE user_id=?", (uid,))
    await target.answer(
        "🔴 Oflayn oldunuz. Sifarişlər gəlməyəcək.\n"
        "Telegram-da canlı yer paylaşımını da dayandırın. Yenidən başlamaq üçün canlı yer paylaşın."
    )


@router.callback_query(F.data == "on")
async def cb_on(cb: CallbackQuery):
    await _go_online(cb.message, cb.from_user.id)
    await cb.answer()


@router.callback_query(F.data == "off")
async def cb_off(cb: CallbackQuery):
    await _go_offline(cb.message, cb.from_user.id)
    await cb.answer()


@router.message(Command("onlayn", "online"), F.chat.type == ChatType.PRIVATE)
async def cmd_on(m: Message):
    await _go_online(m, m.from_user.id)


@router.message(Command("oflayn", "offline"), F.chat.type == ChatType.PRIVATE)
async def cmd_off(m: Message):
    await _go_offline(m, m.from_user.id)


@router.callback_query(F.data == "role:customer")
async def role_customer(cb: CallbackQuery):
    await cb.message.edit_text("Nə lazımdır?", reply_markup=customer_menu_kb())
    await cb.answer()


@router.callback_query(F.data.in_({"order:taxi", "order:courier"}))
async def choose_service(cb: CallbackQuery):
    kind = "courier" if cb.data == "order:courier" else "taxi"
    pending[cb.from_user.id] = {"kind": kind}
    what = "kuryer" if kind == "courier" else "taksi"
    rows = []
    if WEBAPP_URL:
        rows.append([InlineKeyboardButton(text="🟢 Onlayn olanlar", web_app=WebAppInfo(url=f"{WEBAPP_URL}/map?kind={kind}"))])
    await cb.message.edit_text(
        f"{kind_title(kind)} çağırmaq üçün yerinizi göndərin. İstəsəniz əvvəlcə onlayn {what}lərə xəritədə baxın.",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=rows) if rows else None,
    )
    await cb.message.answer("📍 Yerinizi göndərmək üçün aşağıdakı düyməyə basın:", reply_markup=start_kb())
    await cb.answer()


# ---------- Müştəri: yer, ünvan, qiymət ----------
@router.message(F.location, F.chat.type == ChatType.PRIVATE, StateFilter(None))
async def on_location(m: Message):
    uid = m.from_user.id
    loc = m.location

    # Canlı yer = sürücü/kuryer işə başlayır
    if loc.live_period:
        if set_driver_live(uid, loc):
            await m.answer(
                f"🟢 Onlayn oldunuz. {fmt_num(RADIUS_KM)} km radiusdakı sifarişlər sizə gələcək.\n"
                "Dayandırmaq üçün /oflayn yazın və canlı yer paylaşımını söndürün."
            )
        else:
            await m.answer(
                "Canlı yer yalnız təsdiqlənmiş sürücü və kuryerlər üçündür (/driver, /kuryer).\n"
                "Sifariş vermək üçün 📍 düyməsi ilə adi yer göndərin."
            )
        return

    p = pending.get(uid)
    kind = (p or {}).get("kind")
    if not kind:
        await m.answer("Nə lazımdır?", reply_markup=customer_menu_kb())
        return
    if "dlat" in p or "plat" not in p:
        pending[uid] = {"kind": kind, "plat": loc.latitude, "plon": loc.longitude}
        await m.answer(
            "Haraya gedəcəksiniz? Ünvanı yazın (məs. <i>28 Mall</i>) "
            "və ya 📎 → Yer vasitəsilə xəritədən nöqtə göndərin.",
            reply_markup=ReplyKeyboardRemove(),
        )
    else:
        await quote(m, p, loc.latitude, loc.longitude, "Xəritədən seçilmiş nöqtə")


@router.edited_message(F.location, F.chat.type == ChatType.PRIVATE)
async def on_live_location_update(m: Message):
    update_driver_location(m.from_user.id, m.location)


@router.message(F.text, ~F.text.startswith("/"), F.chat.type == ChatType.PRIVATE, StateFilter(None))
async def on_text(m: Message):
    uid = m.from_user.id
    p = pending.get(uid)

    # Kuryer: "nə çatdırılacaq" qeydi
    if p and p.get("await_note"):
        t = m.text.strip()
        p["note"] = "" if t in ("-", "—") else t[:200]
        p.pop("await_note", None)
        pending.pop(uid, None)
        await dispatch_order(m.bot, uid, m.from_user.full_name, p)
        return

    if not p or "plat" not in p or "dlat" in p:
        if p and p.get("kind") and "plat" not in p:
            await m.answer("Əvvəlcə yerinizi göndərin 👇", reply_markup=start_kb())
        else:
            await m.answer("Menyudan seçin:", reply_markup=role_kb())
        return

    cands = await geocode(m.text)
    if not cands:
        await m.answer(
            "Bakı daxilində bu ünvanı tapa bilmədim. Daha dəqiq yazın "
            "və ya 📎 → Yer vasitəsilə xəritədən nöqtə göndərin."
        )
        return
    best = cands[0]
    if best["score"] >= 1 and (len(cands) == 1 or cands[1]["score"] < 1):
        await quote(m, p, best["lat"], best["lon"], best["label"])
        return
    p["cands"] = cands
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"{i + 1}. {c['label'][:55]}", callback_data=f"g:{i}")]
        for i, c in enumerate(cands)
    ])
    note = ("Bir neçə uyğun ünvan tapdım." if best["score"] >= 1
            else "Dəqiq uyğunluq tapa bilmədim. Bunlardan biri sizin yerinizdir?")
    await m.answer(f"{note}\nSeçin və ya 📎 → Yer ilə xəritədən nöqtə göndərin:", reply_markup=kb)


async def quote(m: Message, p: dict, dlat, dlon, label):
    km = await route_km(p["plat"], p["plon"], dlat, dlon)
    if km is None:
        await m.answer("Marşrutu hesablaya bilmədim. Bir az sonra yenidən cəhd edin.")
        return
    price, mult = calc_price(km)
    p.update(dlat=dlat, dlon=dlon, label=label, km=km, price=price)
    note = f" (pik saat ×{fmt_num(PEAK_MULT)})" if mult > 1 else ""
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Təsdiq et", callback_data="q_ok"),
        InlineKeyboardButton(text="❌ Ləğv et", callback_data="q_no"),
    ]])
    await m.answer(f"🏁 Təyinat: {esc(label)}\n💰 Qiymət: <b>{fmt_num(price)} ₼</b>{note}", reply_markup=kb)


@router.callback_query(F.data.startswith("g:"))
async def pick_candidate(cb: CallbackQuery):
    p = pending.get(cb.from_user.id)
    try:
        c = p["cands"][int(cb.data[2:])]
    except Exception:
        await cb.answer("Vaxt keçib. Ünvanı yenidən yazın.", show_alert=True)
        return
    p.pop("cands", None)
    await cb.message.edit_reply_markup(reply_markup=None)
    await quote(cb.message, p, c["lat"], c["lon"], c["label"])
    await cb.answer()


@router.callback_query(F.data == "q_no")
async def quote_cancel(cb: CallbackQuery):
    pending.pop(cb.from_user.id, None)
    await cb.message.edit_text("Ləğv edildi. Yenidən sifariş üçün /start")
    await cb.answer()


@router.callback_query(F.data == "q_ok")
async def quote_ok(cb: CallbackQuery):
    uid = cb.from_user.id
    p = pending.get(uid)
    if not p or "price" not in p:
        await cb.answer("Sifariş vaxtı keçib. Yenidən /start yazın.", show_alert=True)
        return
    try:
        await cb.message.edit_reply_markup(reply_markup=None)
    except Exception:
        pass
    if p.get("kind") == "courier" and "note" not in p:
        p["await_note"] = True
        await cb.message.answer("📦 Nə çatdırılacaq? Qısa yazın (məs. sənəd, paket). Keçmək üçün «-» yazın.")
        await cb.answer()
        return
    pending.pop(uid, None)
    await dispatch_order(cb.bot, uid, cb.from_user.full_name, p)
    await cb.answer()


# ---------- Sifarişin yaradılması və təklif edilməsi ----------
async def offer_order(bot, oid: int, exclude=()):
    """Radiusdakı uyğun sürücülərə fərdi, həmçinin qrupa təklif göndərir. (göndərilən, qrup_ok) qaytarır."""
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    near = [(km, d) for km, d in nearby_drivers(o["plat"], o["plon"], o["kind"]) if d["user_id"] not in exclude]
    roads = await road_distances(o["plat"], o["plon"], [d for _, d in near])
    sent = 0
    for (_, d), rkm in zip(near, roads):
        try:
            msg = await bot.send_message(d["user_id"], order_text(o, rkm), reply_markup=accept_kb(oid))
            execute("INSERT INTO notifs(order_id,chat_id,msg_id,driver_id) VALUES(?,?,?,?)",
                    (oid, d["user_id"], msg.message_id, d["user_id"]))
            sent += 1
        except Exception:
            logging.warning("driver %s bildiriş ala bilmədi (botu başlatmayıb?)", d["user_id"])
    group_ok = False
    try:
        gmsg = await bot.send_message(group_for(o["kind"]), order_text(o), reply_markup=accept_kb(oid))
        execute("INSERT INTO notifs(order_id,chat_id,msg_id,driver_id) VALUES(?,?,?,NULL)",
                (oid, group_for(o["kind"]), gmsg.message_id))
        group_ok = True
    except Exception:
        logging.exception("group send failed")
    return sent, group_ok


def cancel_kb(oid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🚫 Sifarişi ləğv et", callback_data=f"cx:{oid}")]])


async def dispatch_order(bot, uid: int, uname: str, p: dict):
    _, oid = execute(
        "INSERT INTO orders(customer_id,customer_name,kind,plat,plon,dlat,dlon,dest_label,km,price,note,created) "
        "VALUES(?,?,?,?,?,?,?,?,?,?,?,?)",
        (uid, uname, p.get("kind", "taxi"), p["plat"], p["plon"], p["dlat"], p["dlon"], p["label"],
         p["km"], p["price"], p.get("note", ""), datetime.now(TZ).isoformat()),
    )
    sent, group_ok = await offer_order(bot, oid)
    if sent == 0 and not group_ok:
        execute("UPDATE orders SET status='nodriver' WHERE id=?", (oid,))
        await bot.send_message(uid, "😕 Sifarişi sürücülərə çatdıra bilmədim. Bir az sonra yenidən cəhd edin: /start")
        return
    parts = []
    if sent:
        parts.append(f"{sent} yaxın sürücüyə")
    if group_ok:
        parts.append("sürücülər qrupuna")
    await bot.send_message(
        uid, f"✅ Sifariş #{oid} {' və '.join(parts)} göndərildi. Qəbul edən kimi məlumat gələcək.",
        reply_markup=cancel_kb(oid),
    )


@router.callback_query(F.data.startswith("cx:"))
async def customer_cancel(cb: CallbackQuery):
    oid = int(cb.data[3:])
    n, _ = execute("UPDATE orders SET status='cancelled' WHERE id=? AND customer_id=? AND status='new'",
                   (oid, cb.from_user.id))
    if not n:
        await cb.answer("Sifariş artıq qəbul olunub və ya ləğv edilib.", show_alert=True)
        return
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    for r in fetchall("SELECT * FROM notifs WHERE order_id=?", (oid,)):
        try:
            await cb.bot.edit_message_text(order_text(o) + "\n\n🚫 Müştəri ləğv etdi",
                                           chat_id=r["chat_id"], message_id=r["msg_id"], reply_markup=None)
        except Exception:
            logging.warning("edit failed for chat %s", r["chat_id"])
    await cb.message.edit_text(f"Sifariş #{oid} ləğv edildi.")
    await cb.answer()


# ---------- Sürücü: qəbul / imtina / bitirmə ----------
def driver_card(d, o) -> str:
    price = f"💰 {fmt_num(o['price'])} ₼"
    if o["kind"] == "courier":
        lines = ["✅ <b>Kuryer tapıldı!</b>", f"👤 {esc(d['name'])}", f"📞 {esc(d['phone'])}", f"🛵 {esc(d['car'])}"]
        if d["plate"] and norm(d["plate"]) not in ("yoxdur", "-"):
            lines.append(f"🔢 {esc(d['plate'])}")
        return "\n".join(lines + [price])
    return "\n".join(["✅ <b>Sürücü tapıldı!</b>", f"👤 {esc(d['name'])}", f"📞 {esc(d['phone'])}",
                      f"🚗 {esc(d['car'])}", f"🔢 {esc(d['plate'])}", price])


@router.callback_query(F.data.startswith("acc:"))
async def accept(cb: CallbackQuery):
    oid = int(cb.data[4:])
    d = fetch("SELECT * FROM drivers WHERE user_id=? AND approved=1", (cb.from_user.id,))
    if not d:
        await cb.answer("Siz təsdiqlənmiş deyilsiniz. Botda qeydiyyatdan keçin: /start", show_alert=True)
        return
    o0 = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    if not o0:
        await cb.answer("Sifariş tapılmadı.", show_alert=True)
        return
    if o0["kind"] != d["kind"]:
        await cb.answer("Bu sifariş sizin xidmət növünüz üçün deyil.", show_alert=True)
        return
    n, _ = execute("UPDATE orders SET status='accepted', driver_id=? WHERE id=? AND status='new'",
                   (d["user_id"], oid))
    if not n:
        await cb.answer("Bu sifariş artıq götürülüb və ya ləğv edilib.", show_alert=True)
        return
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))

    for r in fetchall("SELECT * FROM notifs WHERE order_id=?", (oid,)):
        if is_group_chat(r["chat_id"]):
            text = order_text(o) + f"\n\n✅ Qəbul etdi: {esc(d['name'])} ({esc(d['plate'])})"
        elif r["driver_id"] == d["user_id"]:
            text = order_text(o) + "\n\n✅ Siz qəbul etdiniz"
        else:
            text = order_text(o) + "\n\n⛔ Sifariş başqa sürücü tərəfindən götürüldü"
        try:
            await cb.bot.edit_message_text(text, chat_id=r["chat_id"], message_id=r["msg_id"], reply_markup=None)
        except Exception:
            logging.warning("edit failed for chat %s", r["chat_id"])

    cmsg = await cb.bot.send_message(o["customer_id"], driver_card(d, o), reply_markup=order_customer_kb(oid))
    execute("UPDATE orders SET cust_msg_id=? WHERE id=?", (cmsg.message_id, oid))
    try:
        dmsg = await cb.bot.send_message(
            d["user_id"],
            "✅ <b>Sifariş sizə verildi</b>\n\n" + order_text(o)
            + f"\n\nMüştəri: <a href=\"tg://user?id={o['customer_id']}\">{esc(o['customer_name'])}</a>",
            reply_markup=order_driver_kb(oid),
        )
        execute("UPDATE orders SET drv_msg_id=? WHERE id=?", (dmsg.message_id, oid))
        await cb.answer("Qəbul etdiniz ✅")
    except Exception:
        await cb.answer("Qəbul etdiniz ✅. Məlumatı şəxsidə almaq üçün mənə botda /start yazın.", show_alert=True)


@router.callback_query(F.data.startswith("rej:"))
async def reject(cb: CallbackQuery):
    oid = int(cb.data[4:])
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    if not is_group_chat(cb.message.chat.id) and o:
        try:
            await cb.message.edit_text(order_text(o) + "\n\n❌ İmtina etdiniz", reply_markup=None)
        except Exception:
            pass
    await cb.answer("İmtina etdiniz.")


@router.callback_query(F.data.startswith("fin:"))
async def finish(cb: CallbackQuery):
    oid = int(cb.data[4:])
    n, _ = execute("UPDATE orders SET status='done' WHERE id=? AND status='accepted' AND driver_id=?",
                   (oid, cb.from_user.id))
    if not n:
        await cb.answer("Sifariş aktiv deyil.", show_alert=True)
        return
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    try:
        await cb.message.edit_reply_markup(reply_markup=None)
    except Exception:
        pass
    await cb.message.answer(f"✅ Sifariş #{oid} tamamlandı. Təşəkkür edirik!")
    if o["cust_msg_id"]:
        try:
            await cb.bot.edit_message_reply_markup(chat_id=o["customer_id"], message_id=o["cust_msg_id"], reply_markup=None)
        except Exception:
            pass
    await cb.bot.send_message(o["customer_id"], f"✅ Sifariş #{oid} tamamlandı. Təşəkkür edirik!")
    await cb.answer()


# ---------- Təsdiqdən sonra imtina (xəbərdarlıqla) ----------
def confirm_kb(yes: str, no: str, oid: int, yes_text: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text=yes_text, callback_data=f"{yes}:{oid}"),
        InlineKeyboardButton(text="↩️ Xeyr", callback_data=f"{no}:{oid}"),
    ]])


@router.callback_query(F.data.startswith("dcx:"))
async def driver_cancel_ask(cb: CallbackQuery):
    oid = int(cb.data[4:])
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    if not o or o["status"] != "accepted" or o["driver_id"] != cb.from_user.id:
        await cb.answer("Sifariş aktiv deyil.", show_alert=True)
        return
    n = recent_cancels(cb.from_user.id, "driver")
    await cb.message.answer(
        "⚠️ <b>Diqqət!</b> Çox imtina etmək olmaz.\n"
        f"Son 24 saatda {n} dəfə imtina etmisiniz. Tez-tez imtina hesabınıza mənfi təsir edə bilər.\n\n"
        "Sifarişdən imtina etmək istəyirsiniz?",
        reply_markup=confirm_kb("dcy", "dcn", oid, "✅ Bəli, imtina et"),
    )
    await cb.answer()


@router.callback_query(F.data.startswith("dcn:") | F.data.startswith("cyn:"))
async def cancel_dismiss(cb: CallbackQuery):
    try:
        await cb.message.delete()
    except Exception:
        pass
    await cb.answer()


@router.callback_query(F.data.startswith("dcy:"))
async def driver_cancel_do(cb: CallbackQuery):
    oid = int(cb.data[4:])
    uid = cb.from_user.id
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    n, _ = execute("UPDATE orders SET status='new', driver_id=NULL WHERE id=? AND status='accepted' AND driver_id=?",
                   (oid, uid))
    if not n:
        await cb.answer("Sifariş aktiv deyil.", show_alert=True)
        return
    d = fetch("SELECT * FROM drivers WHERE user_id=?", (uid,))
    execute("INSERT INTO order_cancels(order_id,driver_id,who,created) VALUES(?,?,?,?)", (oid, uid, "driver", time.time()))
    cnt = recent_cancels(uid, "driver")
    await cb.message.edit_text("❌ Sifarişdən imtina etdiniz. Sifariş başqa sürücüyə təklif olunur.")
    if o["drv_msg_id"]:
        try:
            await cb.bot.edit_message_reply_markup(chat_id=uid, message_id=o["drv_msg_id"], reply_markup=None)
        except Exception:
            pass
    # müştəriyə xəbər + köhnə kartı bağla
    if o["cust_msg_id"]:
        try:
            await cb.bot.edit_message_text("Sürücü sifarişdən imtina etdi.", chat_id=o["customer_id"],
                                           message_id=o["cust_msg_id"], reply_markup=None)
        except Exception:
            pass
    # qrupdakı köhnə mesajı yenilə, bildirişləri təmizlə
    for r in fetchall("SELECT * FROM notifs WHERE order_id=?", (oid,)):
        if is_group_chat(r["chat_id"]):
            try:
                await cb.bot.edit_message_text(
                    order_text(o) + f"\n\n↩️ {esc(d['name'])} imtina etdi, sifariş yenidən təklif olunur",
                    chat_id=r["chat_id"], message_id=r["msg_id"], reply_markup=None)
            except Exception:
                pass
    execute("DELETE FROM notifs WHERE order_id=?", (oid,))
    excl = {r["driver_id"] for r in fetchall(
        "SELECT driver_id FROM order_cancels WHERE order_id=? AND who='driver'", (oid,))}
    sent, group_ok = await offer_order(cb.bot, oid, exclude=excl)
    if sent == 0 and not group_ok:
        await cb.bot.send_message(o["customer_id"], "😕 Sürücü imtina etdi, yeni sürücü tapa bilmədim. /start ilə yenidən cəhd edin.")
        execute("UPDATE orders SET status='nodriver' WHERE id=?", (oid,))
    else:
        await cb.bot.send_message(o["customer_id"], "⚠️ Sürücü imtina etdi. Sizə yeni sürücü axtarırıq…",
                                  reply_markup=cancel_kb(oid))
    if cnt >= CANCEL_WARN:
        await cb.bot.send_message(uid, f"⚠️ Son 24 saatda {cnt} dəfə imtina etmisiniz. Çox imtina etmək olmaz.")
        try:
            await cb.bot.send_message(ADMIN_ID, f"⚠️ {d['name']} ({d['phone']}) son 24 saatda {cnt} dəfə sifarişdən imtina edib.")
        except Exception:
            pass
    await cb.answer()


@router.callback_query(F.data.startswith("cxa:"))
async def customer_cancel_ask(cb: CallbackQuery):
    oid = int(cb.data[4:])
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    if not o or o["status"] != "accepted" or o["customer_id"] != cb.from_user.id:
        await cb.answer("Sifariş aktiv deyil.", show_alert=True)
        return
    await cb.message.answer(
        "⚠️ <b>Diqqət!</b> Sürücü artıq sizə yönəlib. Çox imtina etmək olmaz.\n\nSifarişi ləğv etmək istəyirsiniz?",
        reply_markup=confirm_kb("cyy", "cyn", oid, "✅ Bəli, ləğv et"),
    )
    await cb.answer()


@router.callback_query(F.data.startswith("cyy:"))
async def customer_cancel_do(cb: CallbackQuery):
    oid = int(cb.data[4:])
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    n, _ = execute("UPDATE orders SET status='cancelled' WHERE id=? AND customer_id=? AND status='accepted'",
                   (oid, cb.from_user.id))
    if not n:
        await cb.answer("Sifariş aktiv deyil.", show_alert=True)
        return
    execute("INSERT INTO order_cancels(order_id,driver_id,who,created) VALUES(?,?,?,?)",
            (oid, o["driver_id"], "customer", time.time()))
    await cb.message.edit_text(f"Sifariş #{oid} ləğv edildi.")
    if o["cust_msg_id"]:
        try:
            await cb.bot.edit_message_reply_markup(chat_id=o["customer_id"], message_id=o["cust_msg_id"], reply_markup=None)
        except Exception:
            pass
    if o["drv_msg_id"]:
        try:
            await cb.bot.edit_message_reply_markup(chat_id=o["driver_id"], message_id=o["drv_msg_id"], reply_markup=None)
        except Exception:
            pass
    try:
        await cb.bot.send_message(o["driver_id"], f"🚫 Müştəri #{oid} sifarişini ləğv etdi.")
    except Exception:
        pass
    await cb.answer()


# ---------- Qeydiyyat ----------
class Reg(StatesGroup):
    name = State()
    phone = State()
    car = State()
    plate = State()


async def _reg_start(target: Message, state: FSMContext, kind: str):
    await state.set_state(Reg.name)
    await state.update_data(kind=kind)
    await target.answer(f"{'Kuryer' if kind == 'courier' else 'Sürücü'} qeydiyyatı. Ad və soyadınızı yazın:",
                        reply_markup=ReplyKeyboardRemove())


@router.message(Command("driver"), F.chat.type == ChatType.PRIVATE)
async def cmd_driver(m: Message, state: FSMContext):
    await _reg_start(m, state, "taxi")


@router.message(Command("kuryer"), F.chat.type == ChatType.PRIVATE)
async def cmd_kuryer(m: Message, state: FSMContext):
    await _reg_start(m, state, "courier")


@router.callback_query(F.data.startswith("reg:"))
async def cb_reg(cb: CallbackQuery, state: FSMContext):
    await _reg_start(cb.message, state, "courier" if cb.data == "reg:courier" else "taxi")
    await cb.answer()


@router.message(Reg.name, F.text)
async def reg_name(m: Message, state: FSMContext):
    await state.update_data(name=m.text.strip())
    await state.set_state(Reg.phone)
    await m.answer("Mobil nömrənizi yazın (məs. +994501234567):")


@router.message(Reg.phone, F.text)
async def reg_phone(m: Message, state: FSMContext):
    await state.update_data(phone=m.text.strip())
    await state.set_state(Reg.car)
    kind = (await state.get_data()).get("kind", "taxi")
    await m.answer("Nəqliyyat növü (velosiped, moto, avtomobil):" if kind == "courier"
                   else "Maşın modeli və rəngi (məs. Hyundai Elantra, ağ):")


@router.message(Reg.car, F.text)
async def reg_car(m: Message, state: FSMContext):
    await state.update_data(car=m.text.strip())
    await state.set_state(Reg.plate)
    kind = (await state.get_data()).get("kind", "taxi")
    await m.answer("Dövlət nömrəsi (yoxdursa «yoxdur» yazın):" if kind == "courier"
                   else "Dövlət nömrəsi (məs. 10-AA-123):")


@router.message(Reg.plate, F.text)
async def reg_plate(m: Message, state: FSMContext):
    data = await state.get_data()
    await state.clear()
    uid = m.from_user.id
    kind = data.get("kind", "taxi")
    approved = 1 if uid == ADMIN_ID else 0
    execute(
        "INSERT INTO drivers(user_id,name,phone,car,plate,approved,kind) VALUES(?,?,?,?,?,?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET name=excluded.name, phone=excluded.phone, car=excluded.car, "
        "plate=excluded.plate, approved=excluded.approved, kind=excluded.kind",
        (uid, data["name"], data["phone"], data["car"], m.text.strip(), approved, kind),
    )
    if approved:
        await m.answer("✅ Qeydiyyat tamamlandı, siz təsdiqlənmisiniz. İşə başlamaq üçün /onlayn yazın.")
        return
    await m.answer("Qeydiyyat göndərildi. Admin təsdiqləyəndən sonra /onlayn yazıb işə başlaya biləcəksiniz.")
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Təsdiq et", callback_data=f"appr:{uid}"),
        InlineKeyboardButton(text="🚫 Rədd et", callback_data=f"deny:{uid}"),
    ]])
    await m.bot.send_message(
        ADMIN_ID,
        f"🆕 <b>Yeni {'kuryer' if kind == 'courier' else 'taksi sürücüsü'}</b>\n"
        f"👤 {esc(data['name'])}\n📞 {esc(data['phone'])}\n"
        f"🚗 {esc(data['car'])}\n🔢 {esc(m.text.strip())}",
        reply_markup=kb,
    )


@router.callback_query(F.data.startswith("appr:") | F.data.startswith("deny:"))
async def admin_decision(cb: CallbackQuery):
    if cb.from_user.id != ADMIN_ID:
        await cb.answer("Yalnız admin.", show_alert=True)
        return
    action, uid = cb.data.split(":")
    uid = int(uid)
    if action == "appr":
        execute("UPDATE drivers SET approved=1 WHERE user_id=?", (uid,))
        await cb.message.edit_text(cb.message.html_text + "\n\n✅ Təsdiqləndi")
        note = "✅ Qeydiyyatınız təsdiqləndi. İşə başlamaq üçün canlı yer paylaşın (/onlayn)."
    else:
        execute("UPDATE drivers SET approved=0, online=0 WHERE user_id=?", (uid,))
        await cb.message.edit_text(cb.message.html_text + "\n\n🚫 Rədd edildi")
        note = "Qeydiyyatınız rədd edildi."
    try:
        await cb.bot.send_message(uid, note)
    except Exception:
        pass
    await cb.answer()


# ---------- Başlat ----------
async def main():
    init_db()
    runner = await start_web()
    bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML, link_preview_is_disabled=True))
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    await bot.delete_webhook(drop_pending_updates=True)
    try:
        await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
    finally:
        await runner.cleanup()


if __name__ == "__main__":
    asyncio.run(main())
