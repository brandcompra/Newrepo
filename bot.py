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
from datetime import datetime, timedelta
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
    ChatMemberUpdated,
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
BAKU_LAT, BAKU_LON = 40.46866, 50.01917          # axtarış mərkəzi (Abşeron, Zabrat-Mərdəkan arası)
GEO_RADIUS_KM = float(os.environ.get("GEO_RADIUS_KM", "35"))
SUMGAIT_LAT, SUMGAIT_LON, SUMGAIT_ZONE_KM = 40.589, 49.669, 8.0   # bu dairədəki nəticələr atılır
CITY_LAT, CITY_LON = 40.4093, 49.8671             # şəhər mərkəzi (yalnız yoxlama üçün)
HEAVY_KG = float(os.environ.get("HEAVY_KG", "6"))        # bundan ağır bağlamada əmsal
HEAVY_MULT = float(os.environ.get("HEAVY_MULT", "1.3"))
MAX_KG = float(os.environ.get("MAX_KG", "12"))            # bundan ağır bağlama qəbul olunmur
FAR_KM = float(os.environ.get("FAR_KM", "15"))    # bundan uzaq təyinatda müştəridən təsdiq istənilir

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
            user_id INTEGER,
            name TEXT, phone TEXT, car TEXT, plate TEXT,
            approved INTEGER DEFAULT 0,
            lat REAL, lon REAL, loc_time REAL,
            online INTEGER DEFAULT 0,
            kind TEXT DEFAULT 'taxi',
            PRIMARY KEY (user_id, kind)
        );
        CREATE TABLE IF NOT EXISTS active_role(
            user_id INTEGER PRIMARY KEY, kind TEXT
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
        CREATE TABLE IF NOT EXISTS places(
            id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, lat REAL, lon REAL
        );
        CREATE TABLE IF NOT EXISTS customers(
            user_id INTEGER PRIMARY KEY, name TEXT, phone TEXT
        );
        CREATE TABLE IF NOT EXISTS notifs(
            order_id INTEGER, chat_id INTEGER, msg_id INTEGER, driver_id INTEGER
        );
        CREATE TABLE IF NOT EXISTS order_cancels(
            order_id INTEGER, driver_id INTEGER, who TEXT, created REAL
        );
        CREATE TABLE IF NOT EXISTS ratings(
            order_id INTEGER, target TEXT, rater_id INTEGER, ratee_id INTEGER,
            stars INTEGER, comment TEXT, created TEXT,
            PRIMARY KEY (order_id, target)
        );
        """
    )
    # köhnə bazadan yeniləmə (sütun varsa xəta verməz)
    for table, col, typ in (
        ("drivers", "lat", "REAL"), ("drivers", "lon", "REAL"), ("drivers", "loc_time", "REAL"),
        ("drivers", "online", "INTEGER DEFAULT 0"), ("drivers", "kind", "TEXT DEFAULT 'taxi'"),
        ("orders", "kind", "TEXT DEFAULT 'taxi'"), ("orders", "note", "TEXT"),
        ("orders", "cust_msg_id", "INTEGER"), ("orders", "drv_msg_id", "INTEGER"),
        ("orders", "weight", "REAL"), ("orders", "recv_phone", "TEXT"),
        ("orders", "stage", "TEXT"), ("orders", "arrived_at", "TEXT"), ("orders", "started_at", "TEXT"),
        ("orders", "finished_at", "TEXT"), ("orders", "pickup_label", "TEXT"),
    ):
        try:
            conn.execute(f"ALTER TABLE {table} ADD COLUMN {col} {typ}")
        except sqlite3.OperationalError:
            pass
    conn.commit()
    # köhnə baza: hər istifadəçiyə bir qeyd idi -> indi (istifadəçi, rol) üzrə ayrı qeyd
    pk = [c[1] for c in conn.execute("PRAGMA table_info(drivers)").fetchall() if c[5]]
    if pk == ["user_id"]:
        conn.executescript(
            """
            ALTER TABLE drivers RENAME TO drivers_old;
            CREATE TABLE drivers(
                user_id INTEGER, name TEXT, phone TEXT, car TEXT, plate TEXT,
                approved INTEGER DEFAULT 0, lat REAL, lon REAL, loc_time REAL,
                online INTEGER DEFAULT 0, kind TEXT DEFAULT 'taxi',
                PRIMARY KEY (user_id, kind)
            );
            INSERT INTO drivers(user_id,name,phone,car,plate,approved,lat,lon,loc_time,online,kind)
              SELECT user_id,name,phone,car,plate,approved,lat,lon,loc_time,online,COALESCE(kind,'taxi')
              FROM drivers_old;
            DROP TABLE drivers_old;
            """
        )
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
    return f"{x:.{nd}f}"


def fmt_money(x) -> str:
    """Tam məbləğ qəpiksiz (3 ₼), qəpikli olanda iki rəqəmlə və nöqtə ilə (2.70 ₼)."""
    x = round(float(x or 0), 2)
    if abs(x - round(x)) < 0.005:
        return f"{int(round(x))} ₼"
    return f"{x:.2f} ₼"


def fmt_dist(km: float) -> str:
    """1 km-dən azdırsa metr (750 metr), çoxdursa km (1.3 km)."""
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
    """Yol məsafəsi (km). Xəritə servisi cavab verməsə, düz xətt x 1,35 ilə təxmin edilir."""
    body = {"coordinates": [[plon, plat], [dlon, dlat]], "radiuses": [-1, -1]}   # -1: istənilən məsafədən yola bağla
    try:
        async with aiohttp.ClientSession() as s:
            async with s.post(f"{ORS_BASE}/directions/driving-car", json=body,
                              headers={"Authorization": ORS_KEY},
                              timeout=aiohttp.ClientTimeout(total=20)) as r:
                data = await r.json()
        return data["routes"][0]["summary"]["distance"] / 1000
    except Exception:
        logging.exception("route error; cavab: %s", locals().get("data"))
    est = dist_km(plat, plon, dlat, dlon) * 1.35
    logging.warning("marşrut hesablanmadı, düz xətt x1.35 təxmini: %.1f km", est)
    return est


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


# Say ilə işlənən obyektlər: "27 məktəb" -> "27 nömrəli məktəb" və s.
_TYPE_WORDS = {
    "school": ["mekteb", "mektebi", "lisey", "liseyi", "gimnaziya", "gimnaziyasi", "school"],
    "clinic": ["poliklinika", "poliklinikasi", "xestexana", "xestexanasi", "hospital", "clinic"],
    "kindergarten": ["bagca", "bagcasi", "kindergarten"],
}
_SYNONYMS = {
    "mekteb": ["school", "mekteb", "lisey", "gimnaziya"],
    "lisey": ["licey", "lyceum", "lisey", "mekteb"],
    "gimnaziya": ["gymnasium", "gimnaziya", "mekteb"],
    "xestexana": ["hospital", "xestexana"],
    "poliklinika": ["clinic", "poliklinika"],
    "bagca": ["kindergarten", "bagca"],
}


def numbered_variants(text: str, toks):
    """Yalnız rəqəm (27, 55) və ya rəqəm + məktəb/poliklinika/bağça yazılıbsa, Azərbaycanda
    qəbul olunmuş adlarla bir neçə axtarış variantı yaradır."""
    nums = [t for t in toks if t.isdigit()]
    alpha = [t for t in toks if not t.isdigit()]
    if len(nums) != 1:
        return []
    n = nums[0]
    kind = None
    for k, words in _TYPE_WORDS.items():
        if any(a in words for a in alpha):
            kind = k
            break
    if alpha and not kind:
        return []
    if kind in (None, "school"):
        return [f"{n} nömrəli məktəb", f"{n} nömrəli tam orta məktəb", f"{n} saylı məktəb",
                f"Məktəb {n}", f"{n} nömrəli lisey", f"{n} nömrəli gimnaziya", f"School {n}"]
    if kind == "clinic":
        return [f"{n} nömrəli poliklinika", f"{n} saylı poliklinika", f"{n} nömrəli xəstəxana",
                f"Poliklinika {n}"]
    return [f"{n} nömrəli uşaq bağçası", f"{n} saylı uşaq bağçası", f"Uşaq bağçası {n}"]


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

    def hit(t):  # "bazarı" sorğusu "bazar" adını da tapsın; məktəb ~ school
        if t in nl or (len(t) >= 5 and (t[:-1] in nl or t[:-2] in nl)):
            return True
        return any(w in nl for w in _SYNONYMS.get(t, ()))

    return (len(nums) + sum(1 for t in alpha if hit(t))) / len(tokens)


_NOT_BAKU = ("sumqayit", "sumgait", "sumqayıt")


def in_baku(props: dict, label: str) -> bool:
    """Sumqayıt və s. şəhərlərin nəticələrini atır (25 km radiusa sərhəd hissələri düşə bilir)."""
    blob = norm(" ".join(str(props.get(k, "")) for k in ("locality", "localadmin", "county", "macrocounty")) + " " + label)
    if any(norm(w) in blob for w in _NOT_BAKU):
        return False
    return True


async def _pelias(q: str, near=None):
    params = {
        "api_key": ORS_KEY, "text": q, "boundary.country": "AZ",
        "boundary.circle.lat": str(BAKU_LAT), "boundary.circle.lon": str(BAKU_LON),
        "boundary.circle.radius": str(GEO_RADIUS_KM), "size": "10",
    }
    if near:
        params["focus.point.lat"] = str(near[0])
        params["focus.point.lon"] = str(near[1])
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get(GEOCODE_URL, params=params, timeout=aiohttp.ClientTimeout(total=20)) as r:
                data = await r.json()
        return data.get("features") or []
    except Exception:
        logging.exception("geocode error")
        return []


def _collect(found: dict, features, toks, text, near=None):
    for f in features:
        try:
            lon, lat = f["geometry"]["coordinates"]
        except Exception:
            continue
        if dist_km(BAKU_LAT, BAKU_LON, lat, lon) > GEO_RADIUS_KM:
            continue
        props = f.get("properties", {}) or {}
        label = props.get("label") or text
        if not in_baku(props, label):
            continue
        if dist_km(SUMGAIT_LAT, SUMGAIT_LON, lat, lon) < SUMGAIT_ZONE_KM:
            continue
        # rayon/şəhər göstərilməyən ("..., Azerbaijan") nəticə şəhərdən kənarda ola bilər: mərkəzdən 12 km-dən uzaqdırsa at
        located = any(props.get(k) for k in ("locality", "localadmin", "county", "borough", "neighbourhood",
                                              "macroregion", "region")) or "baku" in norm(label) or "baki" in norm(label)
        if not located and dist_km(CITY_LAT, CITY_LON, lat, lon) > 12:
            continue
        score = match_score(toks, label)
        if score is None:
            continue
        key = (round(lat, 4), round(lon, 4))
        if key in found:
            continue
        nl = norm(label)
        found[key] = {"lat": lat, "lon": lon, "label": make_label(props, label), "score": score,
                      "pname": props.get("name") if props.get("layer") == "venue" else None,
                      "baku": ("baku" in nl or "baki" in nl), "order": len(found),
                      "dist": dist_km(near[0], near[1], lat, lon) if near else 0.0}


def search_places(toks, near=None):
    """Adminin əlavə etdiyi yerlər (məktəb, mall və s.): bütün sözlər uyğun gələnlər."""
    out = []
    for r in fetchall("SELECT * FROM places"):
        sc = match_score(toks, r["name"])
        if sc is None or sc < 1:
            continue
        out.append({"lat": r["lat"], "lon": r["lon"], "label": r["name"], "score": 1.0, "baku": True,
                    "order": r["id"], "dist": dist_km(near[0], near[1], r["lat"], r["lon"]) if near else 0.0})
    out.sort(key=lambda c: (c["dist"], c["order"]))
    return out


def _disambiguate(cands):
    """Eyni adlı nəticələr (məs. bir neçə filial) düymədə müştərinin yerindən məsafə ilə fərqləndirilir."""
    cnt = {}
    for c in cands:
        cnt[norm(c["label"])] = cnt.get(norm(c["label"]), 0) + 1
    for c in cands:
        c["btn"] = c["label"]
        if cnt[norm(c["label"])] > 1 and c.get("dist"):
            c["btn"] = f"{c['label']} · {fmt_dist(c['dist'])}"
    return cands


async def geocode(text: str, near=None):
    """Ünvanı axtarır (yalnız Bakı radiusu). near=(lat, lon) müştərinin yeridir: eyni dərəcədə uyğun
    nəticələrdən ona yaxın olan öndə göstərilir. Nəticə: [{lat, lon, label, score, baku}], ən çoxu 5."""
    toks = query_tokens(text)
    own = search_places(toks, near)
    if own:  # öz siyahımız həmişə birincidir
        return own[:5]
    primary = correct_query(text)
    found: dict = {}
    numbered = numbered_variants(text, toks)
    pure_number = bool(toks) and all(t.isdigit() for t in toks)
    if numbered:
        # "27", "27 məktəb", "55" -> nömrəli obyekt adları ilə axtar
        queries = [f"{v}, Baku" for v in numbered[:5]] + numbered[5:7]
        for feats in await asyncio.gather(*[_pelias(q, near) for q in queries]):
            _collect(found, feats, toks, text, near)
    if not (pure_number and found):
        stage1 = [f"{primary}, Baku, Azerbaijan"] + ([primary] if primary else [])
        for feats in await asyncio.gather(*[_pelias(q, near) for q in stage1]):
            _collect(found, feats, toks, text, near)
    if not any(c["score"] >= 1 for c in found.values()):
        variants = schwa_variants(primary)[:2]
        if variants:
            for feats in await asyncio.gather(*[_pelias(v, near) for v in variants]):
                _collect(found, feats, toks, text, near)
    if pure_number:
        # yalnız rəqəm yazılıbsa: məktəb/lisey/gimnaziya kimi nömrəli obyektləri üstün tut
        def is_inst(c):
            nl = norm(c["label"])
            return any(w in nl for ws in _TYPE_WORDS.values() for w in ws)
        inst = [c for c in found.values() if is_inst(c)]
        pool = inst or list(found.values())
        cands = sorted(pool, key=lambda c: (not c["baku"], c["dist"], c["order"]))
        for c in cands:
            c["score"] = max(c["score"], 1.0)
    else:
        cands = sorted(found.values(), key=lambda c: (-c["score"], not c["baku"], c["order"]))
    cands = cands[:5]
    await _enrich_labels(cands)
    return _disambiguate(cands)


# ---------- Mesaj köməkçiləri ----------
def esc(s) -> str:
    return html.escape(str(s or ""))


NOMINATIM_URL = os.environ.get("NOMINATIM_URL", "https://nominatim.openstreetmap.org/reverse")
_TYPE_SUFFIX = re.compile(r"\s+(rayonu|rayon|raion|district|region|şəhəri|kəndi|qəsəbəsi|city|municipality)$", re.I)
_POI_CATS = {"amenity", "shop", "tourism", "leisure", "office", "craft", "healthcare", "historic", "man_made", "emergency"}


def _nice(s) -> str:
    """Ad təmizlənir: «Baku»→«Bakı», sonundakı «rayonu/kəndi/District» kimi növ sözləri atılır."""
    s = str(s or "").strip()
    s = _TYPE_SUFFIX.sub("", s).strip(" ,")
    return "Bakı" if norm(s) in ("baku", "baki") else s


def _join_parts(parts, limit=90) -> str:
    """Təkrarsız birləşdirir (eyni ad iki dəfə yazılmır), ümumi uzunluq məhdudlaşdırılır."""
    out, seen = [], set()
    for p in parts:
        p = _nice(p)
        k = norm(p)
        if not p or k in seen or k in ("azerbaijan", "azerbaycan", "ba"):
            continue
        if any(k in x or x in k for x in seen if len(x) > 3 and len(k) > 3):   # «Nəsimi» və «Nəsimi rayonu» kimi təkrarlar
            continue
        seen.add(k)
        out.append(p)
    return ", ".join(out)[:limit].rstrip(" ,")


def make_label(props: dict, fallback: str = "") -> str:
    """Pelias nəticəsindən ünvan: obyekt/küçə adı + məhəllə/rayon + şəhər/kənd (+ rayon). «BA, Azerbaijan» yazılmır."""
    props = props or {}
    name, street, hn = props.get("name"), props.get("street"), props.get("housenumber")
    if props.get("layer") == "address" and street:
        head = f"{street} {hn}".strip() if hn else street
    else:
        head = name or ""
    near_part = next((props.get(k) for k in ("neighbourhood", "borough") if props.get(k)), None)
    town = next((props.get(k) for k in ("locality", "localadmin") if props.get(k)), None)
    county = props.get("county")
    parts = [head]
    if street and head != street and not (hn and head.startswith(street)) and not near_part:
        parts.append(street)               # filial aydın olsun deyə küçə (məhəllə yoxdursa)
    parts += [near_part, town]
    if not town or norm(_nice(town)) != "baki":
        parts.append(county)               # kənd/qəsəbədə rayon da yazılır: «Söyüdlü, Gədəbəy»
    out = _join_parts(parts)
    if out:
        return out
    raw = re.sub(r",\s*(?:BA|Azerbaijan)\b", "", fallback or "")
    return _join_parts([x for x in raw.split(",")]) or (fallback or "")


def label_from_nominatim(data: dict, poi=None) -> str:
    """OpenStreetMap-ın (Nominatim) cavabından qısa ünvan: obyekt/küçə, məhəllə, kənd/şəhər, rayon.
    poi verilibsə (məs. «Domino's Pizza»), ünvanın başı həmin addır."""
    addr = (data or {}).get("address") or {}
    head = ""
    if poi:
        head = poi
    elif (data or {}).get("category") in _POI_CATS and data.get("name"):
        head = data["name"]
    elif addr.get("road"):
        head = f"{addr['road']} {addr['house_number']}".strip() if addr.get("house_number") else addr["road"]
    near_part = next((addr.get(k) for k in ("suburb", "neighbourhood", "quarter", "city_district") if addr.get(k)), None)
    skey = next((k for k in ("village", "hamlet", "town", "city", "municipality") if addr.get(k)), None)
    parts = [head, near_part, addr.get(skey) if skey else None]
    if skey != "city":
        parts.append(addr.get("county") or addr.get("state_district"))
    return _join_parts(parts)


NOM_GAP = 1.05                      # Nominatim qaydası: saniyədə ən çoxu 1 sorğu
_nom = {"last": 0.0, "block": 0.0, "lock": None, "cache": {}}


async def _nominatim_raw(lat, lon):
    """Nominatim cavabı (dict) və ya None. Sorğular ardıcıl və ≥1 san aralıqla gedir, nəticə yadda qalır;
    xəta/limit olarsa 1 dəqiqə ərzində yenidən cəhd edilmir (gözləmə yaranmasın)."""
    key = (round(float(lat), 5), round(float(lon), 5))
    if key in _nom["cache"]:
        return _nom["cache"][key]
    if time.time() < _nom["block"]:
        return None
    if _nom["lock"] is None:
        _nom["lock"] = asyncio.Lock()
    params = {"format": "jsonv2", "lat": str(lat), "lon": str(lon), "zoom": "18", "addressdetails": "1",
              "accept-language": "az,en"}
    ua = {"User-Agent": f"YoltTaxiBot/1.0 ({WEBAPP_URL or 'telegram bot'})"}
    async with _nom["lock"]:
        wait = NOM_GAP - (time.monotonic() - _nom["last"])
        if wait > 0:
            await asyncio.sleep(wait)
        _nom["last"] = time.monotonic()
        try:
            async with aiohttp.ClientSession() as s:
                async with s.get(NOMINATIM_URL, params=params, headers=ua, timeout=aiohttp.ClientTimeout(total=5)) as r:
                    status = getattr(r, "status", 200)
                    if status != 200:
                        raise RuntimeError(f"HTTP {status}")
                    data = await r.json()
        except Exception as e:
            logging.warning("nominatim reverse alınmadı: %s", e)
            _nom["block"] = time.time() + 60
            return None
    if len(_nom["cache"]) > 500:
        _nom["cache"].clear()
    _nom["cache"][key] = data
    return data


async def _nominatim_label(lat, lon):
    data = await _nominatim_raw(lat, lon)
    return (label_from_nominatim(data) if data else "") or None


async def _enrich_labels(cands):
    """Eyni adlı (filiallar) və ya yeri bilinməyən («Kapital Bank») nəticələrə məhəllə/rayon əlavə edir:
    «Domino's Pizza, Bakı» -> «Domino's Pizza, Gənclik, Bakı». Müddət məhduddur; alınmasa ad olduğu kimi qalır."""
    cnt = {}
    for c in cands:
        cnt[norm(c["label"])] = cnt.get(norm(c["label"]), 0) + 1
    todo = [c for c in cands if c.get("pname") and (cnt[norm(c["label"])] > 1 or "," not in c["label"])]
    if not todo:
        return

    async def work():
        for c in todo:
            data = await _nominatim_raw(c["lat"], c["lon"])
            lab = label_from_nominatim(data, poi=c["pname"]) if data else ""
            if lab and "," in lab:
                c["label"] = lab
    try:
        await asyncio.wait_for(work(), 8)
    except Exception:
        logging.warning("ünvan dəqiqləşdirilməsi yarımçıq qaldı")


async def _pelias_reverse_label(lat, lon):
    """Ehtiyat yol: Pelias. Əvvəl 150 m, sonra 600 m, sonda kənd/rayon (coğrafi sahə) səviyyəsi."""
    base = {"api_key": ORS_KEY, "point.lat": str(lat), "point.lon": str(lon), "size": "3", "boundary.country": "AZ"}
    tries = [{"boundary.circle.radius": "0.15"}, {"boundary.circle.radius": "0.6"},
             {"layers": "neighbourhood,locality,localadmin,county"}]
    for extra in tries:
        try:
            async with aiohttp.ClientSession() as s:
                async with s.get(GEOCODE_URL.replace("/search", "/reverse"), params={**base, **extra},
                                 timeout=aiohttp.ClientTimeout(total=6)) as r:
                    data = await r.json()
        except Exception:
            logging.warning("reverse geocode alınmadı")
            return None
        for f in data.get("features") or []:
            props = f.get("properties", {}) or {}
            if props.get("layer") in ("region", "macroregion", "macrocounty", "country"):
                continue                      # «Ganja - Gazakh» kimi iri bölgə adları ünvan sayılmır
            label = make_label(props, props.get("label") or "")
            if label and norm(label) not in ("baku", "baki", "azerbaijan", "azerbaycan"):
                return label
    return None


async def reverse_label(lat, lon):
    """Koordinatın real ünvanı. Əvvəl OpenStreetMap-ın öz xidməti (kənd və rayon adlarını da verir), alınmasa Pelias."""
    return await _nominatim_label(lat, lon) or await _pelias_reverse_label(lat, lon)


async def fill_pickup_label(oid: int, lat, lon):
    label = await reverse_label(lat, lon)
    if label:
        execute("UPDATE orders SET pickup_label=? WHERE id=?", (label, oid))


WAZE_BASE = os.environ.get("WAZE_BASE", "https://waze.com/ul").rstrip("?")


def waze(lat, lon) -> str:
    return f"{WAZE_BASE}?ll={lat:.6f},{lon:.6f}&navigate=yes"


def fmt_kg(w) -> str:
    """2 -> '2', 2.5 -> '2.5' (vergül yox, nöqtə)."""
    w = round(float(w), 1)
    return str(int(w)) if w == int(w) else f"{w:.1f}"


def kind_title(kind) -> str:
    return "Kuryer" if kind == "courier" else "Taksi"


def order_text(o, road_km=None) -> str:
    """Sürücüyə gedən mesaj. İki link heç vaxt alt-alta düşmür, son sətir müştərinin yolunun məsafəsidir.
    Fərdi mesajda götürülmə yerinin yanında mötərizədə sürücüdən yol məsafəsi yazılır."""
    near = f" ({fmt_dist(road_km)})" if road_km is not None else ""
    try:
        pl = o["pickup_label"]
    except (KeyError, IndexError):
        pl = None
    where = f": {esc(pl)}" if pl else ""
    lines = [
        f"<b>🔔 {kind_title(o['kind'])} sifarişi #{o['id']}</b>",
        f"<a href=\"{waze(o['plat'], o['plon'])}\">📍 Götürülmə yeri</a>{where}{near} 👈",
        f"💸 Ödəniş məbləği: {fmt_money(o['price'])}",
    ]
    if o["note"]:
        lines.append(f"📝 Qeyd: {esc(o['note'])}")
    if o["weight"]:
        lines.append(f"⚖️ Təxmini çəki: {fmt_kg(o['weight'])} kq")
    lines.append(f"<a href=\"{waze(o['dlat'], o['dlon'])}\">🏁 Gediləcək yer</a>: {esc(o['dest_label'])}")
    lines.append(f"Məsafə: {fmt_dist(o['km'])}")
    return "\n".join(lines)


def accept_kb(oid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Qəbul et", callback_data=f"acc:{oid}"),
        InlineKeyboardButton(text="❌ İmtina", callback_data=f"rej:{oid}"),
    ]])


def role_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="1. Müştəriyəm", callback_data="role:customer")],
        [InlineKeyboardButton(text="2. Sürücüyəm", callback_data="role:driver")],
        [InlineKeyboardButton(text="3. Kuryerəm", callback_data="role:courier")],
    ])


def customer_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🚕 Taksi çağır", callback_data="order:taxi")],
        [InlineKeyboardButton(text="🛵 Kuryer çağır", callback_data="order:courier")],
        [InlineKeyboardButton(text="📋 Sifarişlərim", callback_data="my")],
    ])


BACK_TEXT = "🏠 Əvvələ qayıt"
ROLES_TEXT = "Salam 👋 Kimsiniz?"


def home_kb():
    """Aşağıda daimi duran «Əvvələ qayıt» düyməsi."""
    return ReplyKeyboardMarkup(keyboard=[[KeyboardButton(text=BACK_TEXT)]], resize_keyboard=True, is_persistent=True)


def with_home(rows=None):
    """Mesajın inline düymələri (varsa). «Əvvələ qayıt» artıq aşağıdakı daimi düymədir."""
    rows = [list(r) for r in (rows or [])]
    return InlineKeyboardMarkup(inline_keyboard=rows) if rows else None


def kb_home(kb=None):
    return kb


def start_kb():
    """Yalnız WEBAPP_URL yoxdursa: köhnə üsul (aşağıda daimi «Yerimi göndər» düyməsi)."""
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="📍 Yerimi göndər", request_location=True)], [KeyboardButton(text=BACK_TEXT)]],
        resize_keyboard=True, is_persistent=True,
    )


def customer_phone(uid: int):
    r = fetch("SELECT phone FROM customers WHERE user_id=?", (uid,))
    return r["phone"] if r and r["phone"] else None


PHONE_ASK = ("📱 Sifarişi göndərmək üçün telefon nömrənizi yazın (məs. 0501234567). "
             "Nömrə yalnız sifarişi qəbul edən sürücü və ya kuryerə göstərilir. Bir dəfə yazmaq kifayətdir.")


def parse_phone(text: str):
    """Azərbaycan nömrəsini +994XXXXXXXXX formasına salır; düz deyilsə None."""
    d = re.sub(r"\D", "", text or "")
    if d.startswith("994") and len(d) == 12:
        pass
    elif d.startswith("0") and len(d) == 10:
        d = "994" + d[1:]
    elif len(d) == 9:
        d = "994" + d
    else:
        return None
    return "+" + d


PHONES_ASK = ("📱 Telefon nömrələrini alt-alta yazın:\n"
              "1. Sizin nömrəniz\n"
              "2. Bağlamanı qəbul edən şəxsin nömrəsi\n\n"
              "Nümunə:\n0501234567\n0557654321")
WEIGHT_ASK = "📦 Bağlamanın təxmini çəkisi neçə kq-dır? Rəqəmlə yazın."


def parse_two_phones(text: str):
    """Alt-alta (və ya vergüllə) yazılmış iki nömrə: (öz nömrəsi, qəbul edənin nömrəsi) və ya None."""
    parts = [x for x in re.split(r"[\n,;]+", text or "") if x.strip()]
    if len(parts) < 2:
        return None
    nums = []
    for x in parts[:2]:
        ph = parse_phone(re.sub(r"^\s*[12][.)]\s*", "", x))
        if not ph:
            return None
        nums.append(ph)
    return nums[0], nums[1]


async def next_order_step(m: Message, uid: int, uname: str, p: dict):
    """Təsdiqdən sonra son tələb: telefon nömrələri. Nömrə(lər) yazılandan sonra sifariş yaradılır."""
    if p.get("kind") == "courier":
        p["await_phones"] = True
        p["uname"] = uname
        if WEBAPP_URL:
            own = customer_phone(uid) or ""
            kb = with_home([[InlineKeyboardButton(
                text="📱 Nömrələri yaz",
                web_app=WebAppInfo(url=f"{WEBAPP_URL}/phones?own={own.replace('+', '%2B')}"))]])
            await m.answer("📱 Aşağıdakı düyməyə basın, açılan səhifədə iki nömrəni yazıb göndərin.\n\n"
                           "Səhifə açılmasa, nömrələri bura alt-alta yazın:\n"
                           "1. Sizin nömrəniz\n2. Bağlamanı qəbul edən şəxsin nömrəsi", reply_markup=kb)
        else:
            await m.answer(PHONES_ASK, reply_markup=with_home())
        return
    if not customer_phone(uid):
        p["await_phone"] = True
        await m.answer(PHONE_ASK, reply_markup=with_home())
        return
    pending.pop(uid, None)
    await dispatch_order(m.bot, uid, uname, p)


def order_customer_kb(oid: int, stage=None) -> InlineKeyboardMarkup:
    rows = []
    if WEBAPP_URL:
        rows.append([InlineKeyboardButton(text="📍 İzlə", web_app=WebAppInfo(url=f"{WEBAPP_URL}/map?order={oid}"))])
    if stage != "started":                      # gediş başlayandan sonra müştəri ləğv edə bilmir
        rows.append([InlineKeyboardButton(text="🚫 İmtina et", callback_data=f"cxa:{oid}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def order_driver_kb(o) -> InlineKeyboardMarkup:
    """Sürücünün/kuryerin sifariş mesajındakı düymələr mərhələyə görədir:
    qəbul -> Çatdım -> Gedişə başla -> Sifarişi bitir."""
    oid, stage = o["id"], o["stage"]
    if stage == "started":
        return InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text=f"✅ Sifarişi bitir · {fmt_money(o['price'])}", callback_data=f"fin:{oid}")],
        ])
    if stage == "arrived":
        go = "🛵 Çatdırılmaya başla" if o["kind"] == "courier" else "▶️ Gedişə başla"
        return InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text=go, callback_data=f"go:{oid}")],
            [InlineKeyboardButton(text="🚫 İmtina et", callback_data=f"dcx:{oid}")],
        ])
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📍 Çatdım", callback_data=f"arr:{oid}")],
        [InlineKeyboardButton(text="🚫 İmtina et", callback_data=f"dcx:{oid}")],
    ])


def driver_dm_text(o) -> str:
    """Sifarişi qəbul edənin şəxsi mesajı (mərhələ sonda qısa sətirlə göstərilir)."""
    txt = ("✅ <b>Sifariş sizə verildi</b>\n\n" + order_text(o)
           + f"\n\nMüştəri: <a href=\"tg://user?id={o['customer_id']}\">{esc(o['customer_name'])}</a>"
           + (f"\nTelefon: {esc(customer_phone(o['customer_id']))}" if customer_phone(o["customer_id"]) else "")
           + (f"\nQəbul edən şəxsin telefonu: {esc(o['recv_phone'])}" if o["recv_phone"] else ""))
    if o["status"] == "done":
        txt += "\n\n✅ Tamamlandı"
    elif o["stage"] == "started":
        txt += "\n\n" + ("🛵 Çatdırılma davam edir" if o["kind"] == "courier" else "▶️ Gediş davam edir")
    elif o["stage"] == "arrived":
        txt += "\n\n📍 Çatdınız, müştəri xəbərdar edildi"
    return txt


def set_active_role(uid: int, kind: str):
    execute("INSERT INTO active_role(user_id,kind) VALUES(?,?) "
            "ON CONFLICT(user_id) DO UPDATE SET kind=excluded.kind", (uid, kind))


def approved_kinds(uid: int) -> set:
    return {r["kind"] for r in fetchall("SELECT kind FROM drivers WHERE user_id=? AND approved=1", (uid,))}


def pick_kind(uid: int):
    """İşləyəcəyi rol: yalnız biri təsdiqlənibsə o, ikisi də təsdiqlənibsə axırıncı seçilən; yoxdursa None."""
    kinds = approved_kinds(uid)
    if len(kinds) == 1:
        return next(iter(kinds))
    if len(kinds) > 1:
        a = fetch("SELECT kind FROM active_role WHERE user_id=?", (uid,))
        if a and a["kind"] in kinds:
            return a["kind"]
    return None


def set_driver_live(uid: int, loc) -> int:
    kind = pick_kind(uid)
    if not kind:
        return 0
    execute("UPDATE drivers SET online=0 WHERE user_id=? AND kind!=?", (uid, kind))   # eyni anda yalnız bir rolda onlayn
    n, _ = execute(
        "UPDATE drivers SET online=1, lat=?, lon=?, loc_time=? WHERE user_id=? AND kind=? AND approved=1",
        (loc.latitude, loc.longitude, time.time(), uid, kind),
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
      var who = (d.kind === 'courier' ? 'Kuryer' : 'Sürücü');
      statusEl.textContent = d.stage === 'arrived' ? (who + ' çatdı, sizi gözləyir') :
                             d.stage === 'started' ? (d.kind === 'courier' ? 'Çatdırılma gedir' : 'Gediş gedir') : (who + ' yoldadır');
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
    d = fetch("SELECT lat, lon, loc_time FROM drivers WHERE user_id=? AND kind=?", (o["driver_id"], o["kind"]))
    drv = None
    if d and d["lat"] is not None:
        drv = {"lat": d["lat"], "lon": d["lon"], "age": int(time.time() - (d["loc_time"] or 0))}
    return web.json_response({
        "status": "accepted", "kind": o["kind"], "driver": drv, "stage": o["stage"],
        "pickup": {"lat": o["plat"], "lon": o["plon"]},
        "dest": {"lat": o["dlat"], "lon": o["dlon"]},
    }, headers={"Cache-Control": "no-store"})


PHONES_PAGE = """<!doctype html>
<html lang="az"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no">
<title>Telefon nömrələri</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
:root{--bg:#fff;--fg:#111827;--box:#f3f4f6;--line:#d1d5db;--mut:#6b7280;--btn:#2563eb}
@media (prefers-color-scheme: dark){:root{--bg:#111827;--fg:#f3f4f6;--box:#1f2937;--line:#374151;--mut:#9ca3af}}
html,body{margin:0;background:var(--bg);color:var(--fg);font:16px/1.4 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
main{padding:20px 16px;max-width:480px;margin:0 auto}
h1{font-size:19px;margin:0 0 16px}
label{display:block;font-weight:600;margin:14px 0 6px}
input{width:100%;box-sizing:border-box;padding:13px 12px;font-size:18px;border:1px solid var(--line);border-radius:10px;background:var(--box);color:var(--fg)}
.hint{color:var(--mut);font-size:13px;margin-top:4px}
button{width:100%;margin-top:22px;padding:14px;font-size:17px;font-weight:600;border:0;border-radius:10px;background:var(--btn);color:#fff}
button:disabled{opacity:.6}
#err{color:#dc2626;margin-top:12px;min-height:20px}
</style></head><body><main>
<h1>📱 Telefon nömrələri</h1>
<label for="own">1. Sizin nömrəniz</label>
<input id="own" type="tel" inputmode="tel" placeholder="0501234567" autocomplete="tel">
<label for="recv">2. Bağlamanı qəbul edən şəxsin nömrəsi</label>
<input id="recv" type="tel" inputmode="tel" placeholder="0557654321">
<div class="hint">Nömrələr yalnız sifarişi götürən kuryerə göstərilir.</div>
<div id="err"></div>
<button id="go">Göndər</button>
</main>
<script>
(function(){
var tg = window.Telegram && window.Telegram.WebApp;
if (tg) { try { tg.ready(); tg.expand(); } catch(e){} }
var q = new URLSearchParams(location.search);
var own = document.getElementById('own'), recv = document.getElementById('recv');
own.value = q.get('own') || '';
var err = document.getElementById('err'), btn = document.getElementById('go');
function ok(v){ var d = (v||'').replace(/\\D/g,''); return (d.indexOf('994')===0 && d.length===12) || (d[0]==='0' && d.length===10) || d.length===9; }
btn.onclick = function(){
  err.textContent = '';
  if (!ok(own.value)) { err.textContent = '1-ci nömrə düzgün deyil. Məsələn: 0501234567'; own.focus(); return; }
  if (!ok(recv.value)) { err.textContent = '2-ci nömrə düzgün deyil. Məsələn: 0557654321'; recv.focus(); return; }
  btn.disabled = true;
  fetch('/api/phones', {method:'POST', headers:{'Content-Type':'application/json','X-Init-Data': tg ? tg.initData : ''},
        body: JSON.stringify({own: own.value, recv: recv.value})})
  .then(function(r){ return r.json().then(function(j){ return {s:r.status, j:j}; }); })
  .then(function(x){
    if (x.s === 200) { if (tg) tg.close(); else err.textContent = 'Göndərildi ✅'; return; }
    btn.disabled = false;
    err.textContent = x.j.error === 'expired' ? 'Sifariş vaxtı keçib. Botda yenidən sifariş verin.' :
                      x.j.error === 'bad' ? 'Nömrələr düzgün deyil.' : 'Xəta baş verdi. Yenidən cəhd edin.';
  })
  .catch(function(){ btn.disabled = false; err.textContent = 'Bağlantı xətası. Yenidən cəhd edin.'; });
};
})();
</script></body></html>"""

BOT_REF = {}
_tasks: set = set()


def spawn(coro):
    """Arxa planda işləyən tapşırıq (yığılıb silinməsin deyə saxlanılır)."""
    t = asyncio.create_task(coro)
    _tasks.add(t)
    t.add_done_callback(_tasks.discard)
    return t


async def phones_page(request):
    return web.Response(text=PHONES_PAGE, content_type="text/html", headers={"Cache-Control": "no-store"})


async def api_phones(request):
    uid = _auth(request)
    if uid is None:
        return web.json_response({"error": "auth"}, status=401)
    p = pending.get(uid)
    if not p or not p.get("await_phones"):
        return web.json_response({"error": "expired"}, status=409)
    try:
        body = await request.json()
    except Exception:
        return web.json_response({"error": "bad"}, status=400)
    own, recv = parse_phone(str(body.get("own", ""))), parse_phone(str(body.get("recv", "")))
    if not own or not recv:
        return web.json_response({"error": "bad"}, status=400)
    uname = p.get("uname", "")
    execute("INSERT INTO customers(user_id,name,phone) VALUES(?,?,?) "
            "ON CONFLICT(user_id) DO UPDATE SET name=excluded.name, phone=excluded.phone", (uid, uname, own))
    p["recv_phone"] = recv
    p.pop("await_phones", None)
    pending.pop(uid, None)
    spawn(dispatch_order(BOT_REF["bot"], uid, uname, p))
    return web.json_response({"ok": True})


LOCATE_PAGE = """<!doctype html>
<html lang="az"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no">
<title>Yerim</title>
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.css">
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/leaflet/1.9.4/leaflet.js"></script>
<style>
:root{--bg:#fff;--fg:#111827;--bar:#f3f4f6;--mut:#6b7280;--btn:#2563eb}
@media (prefers-color-scheme: dark){:root{--bg:#111827;--fg:#f3f4f6;--bar:#1f2937;--mut:#9ca3af}}
html,body{margin:0;height:100%;background:var(--bg);color:var(--fg);font:15px/1.4 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
#bar{position:fixed;top:0;left:0;right:0;z-index:1000;box-sizing:border-box;height:62px;padding:10px 16px;background:var(--bar);box-shadow:0 1px 4px rgba(0,0,0,.25)}
#status{font-weight:600}
#hint{color:var(--mut);font-size:12px;margin-top:2px}
#map{position:absolute;top:62px;bottom:72px;left:0;right:0}
#foot{position:fixed;left:0;right:0;bottom:0;z-index:1000;box-sizing:border-box;height:72px;padding:10px 16px;background:var(--bar)}
button{width:100%;height:100%;font-size:17px;font-weight:600;border:0;border-radius:10px;background:var(--btn);color:#fff}
button:disabled{opacity:.5}
.pin{font-size:30px;line-height:34px;text-align:center;filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))}
</style></head><body>
<div id="bar"><div id="status">Yeriniz təyin edilir…</div><div id="hint"></div></div>
<div id="map"></div>
<div id="foot"><button id="go" disabled>✅ Təsdiq et</button></div>
<script>
(function(){
var tg = window.Telegram && window.Telegram.WebApp;
if (tg) { try { tg.ready(); tg.expand(); } catch(e){} }
var statusEl = document.getElementById('status'), hintEl = document.getElementById('hint'), btn = document.getElementById('go');
var map = L.map('map').setView([40.4093, 49.8671], 12);
L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {maxZoom: 19, attribution: '&copy; OpenStreetMap'}).addTo(map);
var marker = null, point = null;
function setPoint(lat, lon, move){
  point = {lat: lat, lon: lon};
  if (!marker) {
    marker = L.marker([lat, lon], {draggable: true, icon: L.divIcon({className: 'pin', html: '📍', iconSize: [34, 34], iconAnchor: [17, 32]})}).addTo(map);
    marker.on('dragend', function(){ var p = marker.getLatLng(); point = {lat: p.lat, lon: p.lng}; });
  } else { marker.setLatLng([lat, lon]); }
  if (move) map.setView([lat, lon], 17);
  btn.disabled = false;
}
map.on('click', function(e){ setPoint(e.latlng.lat, e.latlng.lng, false); statusEl.textContent = 'Nöqtə seçildi'; hintEl.textContent = 'İstəsəniz nişanı sürüşdürüb dəqiqləşdirin'; });
function getPos(){
  return new Promise(function(res){
    var done = false;
    function fin(v){ if (!done) { done = true; res(v); } }
    setTimeout(function(){ fin(null); }, 15000);
    function viaBrowser(){
      if (!navigator.geolocation) return fin(null);
      navigator.geolocation.getCurrentPosition(
        function(p){ fin({lat: p.coords.latitude, lon: p.coords.longitude}); },
        function(){ fin(null); }, {enableHighAccuracy: true, timeout: 12000});
    }
    var lm = tg && tg.LocationManager;
    if (lm && lm.init) {
      try {
        lm.init(function(){
          if (lm.isLocationAvailable) {
            lm.getLocation(function(d){ if (d && d.latitude != null) fin({lat: d.latitude, lon: d.longitude}); else viaBrowser(); });
          } else viaBrowser();
        });
      } catch(e) { viaBrowser(); }
    } else { viaBrowser(); }
  });
}
getPos().then(function(p){
  if (p) {
    setPoint(p.lat, p.lon, true);
    statusEl.textContent = 'Yeriniz tapıldı';
    hintEl.textContent = 'Düzdürsə «Təsdiq et»ə basın. Dəyişmək üçün xəritədə toxunun.';
  } else {
    statusEl.textContent = 'Yeri tapa bilmədik. Xəritədə nöqtəni özünüz seçin';
    hintEl.textContent = 'Xəritəyə toxunub götürülmə nöqtəsini göstərin';
  }
});
btn.onclick = function(){
  if (!point) return;
  btn.disabled = true;
  fetch('/api/pickup', {method: 'POST', headers: {'Content-Type': 'application/json', 'X-Init-Data': tg ? tg.initData : ''},
        body: JSON.stringify(point)})
  .then(function(r){ return r.json().then(function(j){ return {s: r.status, j: j}; }); })
  .then(function(x){
    if (x.s === 200) { if (tg) tg.close(); else statusEl.textContent = 'Göndərildi ✅'; return; }
    btn.disabled = false;
    statusEl.textContent = x.j.error === 'expired' ? 'Sifariş vaxtı keçib. Botda yenidən sifariş verin.' : 'Xəta baş verdi. Yenidən cəhd edin.';
  })
  .catch(function(){ btn.disabled = false; statusEl.textContent = 'Bağlantı xətası. Yenidən cəhd edin.'; });
};
})();
</script></body></html>"""


async def locate_page(request):
    return web.Response(text=LOCATE_PAGE, content_type="text/html", charset="utf-8", headers={"Cache-Control": "no-store"})


async def api_pickup(request):
    """Mini Appdan gələn götürülmə nöqtəsi: sifarişi davam etdirir (təyinat soruşulur)."""
    uid = _auth(request)
    if uid is None:
        return web.json_response({"error": "auth"}, status=401)
    try:
        body = await request.json()
        lat, lon = float(body["lat"]), float(body["lon"])
    except Exception:
        return web.json_response({"error": "bad"}, status=400)
    if not (math.isfinite(lat) and math.isfinite(lon) and -90 <= lat <= 90 and -180 <= lon <= 180):
        return web.json_response({"error": "bad"}, status=400)
    p = pending.get(uid)
    busy = p and any(k in p for k in ("dlat", "await_phone", "await_phones", "await_weight"))
    if not p or not p.get("kind") or busy:
        return web.json_response({"error": "expired"}, status=409)
    bot = BOT_REF["bot"]

    async def send(text, reply_markup=None):
        await bot.send_message(uid, text, reply_markup=reply_markup)

    try:
        await bot.send_location(uid, lat, lon)       # xəritə yenə mesaj kimi görünsün
    except Exception:
        logging.warning("location message failed")
    await set_pickup(send, uid, p["kind"], lat, lon)
    return web.json_response({"ok": True})


async def start_web():
    app = web.Application()
    app.add_routes([
        web.get("/", web_health), web.get("/map", web_page),
        web.get("/api/online", api_online), web.get("/api/track", api_track),
        web.get("/phones", phones_page), web.post("/api/phones", api_phones),
        web.get("/locate", locate_page), web.post("/api/pickup", api_pickup),
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
    await m.answer("Aşağıdakı «Əvvələ qayıt» düyməsi istənilən vaxt əsas menyuya qaytarır.", reply_markup=home_kb())
    await m.answer(ROLES_TEXT, reply_markup=role_kb())


@router.message(F.text == BACK_TEXT, F.chat.type == ChatType.PRIVATE)
async def go_home(m: Message, state: FSMContext):
    await state.clear()
    pending.pop(m.from_user.id, None)
    awaiting_comment.pop(m.from_user.id, None)
    await m.answer(ROLES_TEXT, reply_markup=role_kb())


@router.callback_query(F.data == "home")
async def cb_home(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    pending.pop(cb.from_user.id, None)
    awaiting_comment.pop(cb.from_user.id, None)
    await cb.message.answer(ROLES_TEXT, reply_markup=role_kb())
    await cb.answer()


@router.my_chat_member()
async def bot_membership(ev: ChatMemberUpdated):
    """Bot qrupa əlavə olunanda/çıxarılanda adminə qrupun ID-sini göndərir."""
    if ev.chat.type == ChatType.PRIVATE:
        return
    st = ev.new_chat_member.status
    state = "əlavə olundu ✅" if st in ("member", "administrator") else "qrupdan çıxarıldı ❌"
    try:
        await ev.bot.send_message(
            ADMIN_ID, f"Bot qrupa {state}\nQrup: {esc(ev.chat.title)}\nQrup ID: <code>{ev.chat.id}</code>")
    except Exception:
        logging.exception("admin notice failed")


@router.message(Command("id"))
async def get_id(m: Message):
    await m.answer(f"Chat ID: <code>{m.chat.id}</code>")


@router.callback_query(F.data.in_({"role:driver", "role:courier"}))
async def role_worker(cb: CallbackQuery):
    kind = "courier" if cb.data == "role:courier" else "taxi"
    d = fetch("SELECT * FROM drivers WHERE user_id=? AND kind=?", (cb.from_user.id, kind))
    registered = d is not None
    if registered and d["approved"]:
        set_active_role(cb.from_user.id, kind)
    lines = [f"<b>{'🛵 Kuryer' if kind == 'courier' else '🚕 Sürücü'} bölməsi</b>", ""]
    if not registered:
        lines.append("Əvvəlcə qeydiyyatdan keçin. Admin təsdiqləyəndən sonra işə başlaya bilərsiniz.")
    elif not d["approved"]:
        lines.append("Qeydiyyatınız admin təsdiqini gözləyir.")
    else:
        lines.append("Siz təsdiqlənmisiniz.")
        if len(approved_kinds(cb.from_user.id)) > 1:
            lines.append("Hər iki rolunuz var. İşə başlayanda bu rolda onlayn olacaqsınız. Digər rola keçmək üçün /start yazıb onu seçin.")
    lines += ["", "İşə başlamaq: 🟢 Onlayn düyməsi və ya /onlayn", "Dayandırmaq: 🔴 Oflayn düyməsi və ya /oflayn"]
    rows = [[InlineKeyboardButton(text="🟢 Onlayn", callback_data="on"),
             InlineKeyboardButton(text="🔴 Oflayn", callback_data="off")]]
    if not registered:
        rows.append([InlineKeyboardButton(text="📝 Qeydiyyat", callback_data=f"reg:{kind}")])
    elif d["approved"]:
        rows.append([InlineKeyboardButton(text="👤 Profilim", callback_data=f"prof:{kind}")])
    await cb.message.edit_text("\n".join(lines), reply_markup=with_home(rows))
    await cb.answer()


async def _go_online(target: Message, uid: int):
    if not approved_kinds(uid):
        await target.answer("Əvvəlcə qeydiyyatdan keçin (/driver sürücü, /kuryer kuryer) və admin təsdiqini gözləyin.",
                            reply_markup=with_home())
        return
    kind = pick_kind(uid)
    if not kind:
        await target.answer("Hər iki rolunuz var. Əvvəlcə /start yazıb «Sürücüyəm» və ya «Kuryerəm» bölməsini açın, sonra işə başlayın.",
                            reply_markup=with_home())
        return
    role = "kuryer" if kind == "courier" else "sürücü"
    await target.answer(f"🟢 {role.capitalize()} kimi işə başlamaq üçün canlı yerinizi göndərin:\n\n" + LIVE_HELP,
                        reply_markup=with_home())


async def _go_offline(target: Message, uid: int):
    execute("UPDATE drivers SET online=0 WHERE user_id=?", (uid,))
    await target.answer(
        "🔴 Oflayn oldunuz. Sifarişlər gəlməyəcək.\n"
        "Telegram-da canlı yer paylaşımını da dayandırın. Yenidən başlamaq üçün canlı yer paylaşın.",
        reply_markup=with_home(),
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
    await cb.message.edit_text("Nə lazımdır?", reply_markup=kb_home(customer_menu_kb()))
    await cb.answer()


def loc_rows(kind: str):
    """«Yerimi göndər» (Mini App) və «Onlayn olanlar» düymələri."""
    rows = []
    if WEBAPP_URL:
        rows.append([InlineKeyboardButton(text="📍 Yerimi göndər", web_app=WebAppInfo(url=f"{WEBAPP_URL}/locate"))])
        rows.append([InlineKeyboardButton(text="🟢 Onlayn olanlar", web_app=WebAppInfo(url=f"{WEBAPP_URL}/map?kind={kind}"))])
    return rows


async def ask_location(target: Message, kind: str, first: str = ""):
    """Götürülmə yerini istəyir. Düymə mesajın altındadır, «Əvvələ qayıt» ən sonda.
    WEBAPP_URL yoxdursa köhnə üsula (aşağıdakı düymə) qayıdır."""
    ask = "📍 Yerinizi göndərmək üçün aşağıdakı düyməyə basın:"
    if WEBAPP_URL:
        await target.answer((first + "\n\n" if first else "") + ask, reply_markup=with_home(loc_rows(kind)))
    else:
        await target.answer((first + "\n\n" if first else "") + ask, reply_markup=start_kb())


@router.callback_query(F.data.in_({"order:taxi", "order:courier"}))
async def choose_service(cb: CallbackQuery):
    kind = "courier" if cb.data == "order:courier" else "taxi"
    pending[cb.from_user.id] = {"kind": kind}
    what = "kuryer" if kind == "courier" else "taksi"
    first = (f"{kind_title(kind)} çağırmaq üçün götürülmə yerini göndərin: 📍 düyməsi ilə öz yerinizi və ya 📎 → Yer ilə "
             f"istənilən nöqtəni. İstəsəniz əvvəlcə onlayn {what}lərə xəritədə baxın.")
    if WEBAPP_URL:
        await cb.message.edit_text(first + "\n\n📍 Yerinizi göndərmək üçün aşağıdakı düyməyə basın:",
                                   reply_markup=with_home(loc_rows(kind)))
    else:
        await cb.message.edit_text(first, reply_markup=with_home())
        await ask_location(cb.message, kind)
    await cb.answer()


# ---------- Müştəri: yer, ünvan, qiymət ----------
async def _set_plabel(p: dict, lat, lon):
    label = await reverse_label(lat, lon)
    p["plabel"] = label or ""


async def send_map(bot, chat_id, lat, lon, title=None, address=None):
    """Xəritə mesajı göndərir. title verilibsə, xəritənin altında yazı ilə (məs. «Götürülmə yeri») görünür."""
    try:
        if title:
            await bot.send_venue(chat_id, lat, lon, title=str(title)[:100] or "Yer", address=str(address or "—")[:200])
        else:
            await bot.send_location(chat_id, lat, lon)
    except Exception:
        logging.warning("map message to %s failed", chat_id)


async def set_pickup(send, uid: int, kind: str, lat: float, lon: float):
    """Götürülmə nöqtəsini yadda saxlayır və təyinatı soruşur. send(text, reply_markup=...) mesaj göndərən funksiyadır."""
    p = pending[uid] = {"kind": kind, "plat": lat, "plon": lon}
    spawn(_set_plabel(p, lat, lon))           # götürülmə ünvanı arxa planda tapılır (sifarişdə və tarixçədə görünür)
    if kind == "courier":
        ask = "Bağlama hara göndəriləcək? Ünvanı yazın və ya 📎 → Yer vasitəsilə xəritədən nöqtə göndərin."
    else:
        ask = ("Haraya gedəcəksiniz? Ünvanı yazın (məs. <i>28 Mall</i>) "
               "və ya 📎 → Yer vasitəsilə xəritədən nöqtə göndərin.")
    await send(ask, reply_markup=home_kb())


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
        elif len(approved_kinds(uid)) > 1:
            await m.answer("Hər iki rolunuz var. Əvvəlcə /start yazıb «Sürücüyəm» və ya «Kuryerəm» bölməsini açın, sonra canlı yer paylaşın.")
        else:
            await m.answer(
                "Canlı yer yalnız təsdiqlənmiş sürücü və kuryerlər üçündür (/driver, /kuryer).\n"
                "Sifariş vermək üçün 📍 düyməsi ilə adi yer göndərin."
            )
        return

    p = pending.get(uid)
    kind = (p or {}).get("kind")
    if not kind:
        await m.answer("Nə lazımdır?", reply_markup=kb_home(customer_menu_kb()))
        return
    if "plat" not in p:
        await set_pickup(m.answer, uid, kind, loc.latitude, loc.longitude)
    else:
        label = await reverse_label(loc.latitude, loc.longitude) or f"{loc.latitude:.5f}, {loc.longitude:.5f}"
        await quote(m, p, loc.latitude, loc.longitude, label, show_map=False)


@router.edited_message(F.location, F.chat.type == ChatType.PRIVATE)
async def on_live_location_update(m: Message):
    update_driver_location(m.from_user.id, m.location)


@router.message(F.text, ~F.text.startswith("/"), F.chat.type == ChatType.PRIVATE, StateFilter(None))
async def on_text(m: Message):
    uid = m.from_user.id
    p = pending.get(uid)

    if uid in awaiting_comment and await save_comment(m):
        return

    if p and p.get("await_phone"):
        phone = parse_phone(m.text)
        if not phone:
            await m.answer("Nömrə düzgün deyil. Məsələn: 0501234567", reply_markup=with_home())
            return
        execute("INSERT INTO customers(user_id,name,phone) VALUES(?,?,?) "
                "ON CONFLICT(user_id) DO UPDATE SET name=excluded.name, phone=excluded.phone",
                (uid, m.from_user.full_name, phone))
        p.pop("await_phone", None)
        pending.pop(uid, None)
        await dispatch_order(m.bot, uid, m.from_user.full_name, p)
        return

    if p and p.get("await_phones"):
        two = parse_two_phones(m.text)
        if not two:
            await m.answer("Hər iki nömrəni alt-alta yazın, məsələn:\n0501234567\n0557654321", reply_markup=with_home())
            return
        own, recv = two
        execute("INSERT INTO customers(user_id,name,phone) VALUES(?,?,?) "
                "ON CONFLICT(user_id) DO UPDATE SET name=excluded.name, phone=excluded.phone",
                (uid, m.from_user.full_name, own))
        p["recv_phone"] = recv
        p.pop("await_phones", None)
        pending.pop(uid, None)
        await dispatch_order(m.bot, uid, m.from_user.full_name, p)
        return

    if p and p.get("await_weight"):
        w = parse_weight(m.text)
        if w is None:
            await m.answer("Çəkini rəqəmlə yazın, məsələn: 2 və ya 2.5", reply_markup=with_home())
            return
        if w > MAX_KG:
            await m.answer(f"Bağlamanın çəkisi {fmt_kg(MAX_KG)} kq-dan çox ola bilməz. Daha yüngül çəki yazın.",
                           reply_markup=with_home())
            return
        p["weight"] = w
        p.pop("await_weight", None)
        await quote(m, p, p["dlat"], p["dlon"], p["label"])
        return

    if not p or "plat" not in p:
        if p and p.get("kind") and "plat" not in p:
            await ask_location(m, p["kind"], "Əvvəlcə yerinizi göndərin 👇")
        else:
            await m.answer(ROLES_TEXT, reply_markup=role_kb())
        return

    if "dlat" in p:  # təyinat artıq seçilmişdi, istifadəçi yenisini yazır
        for k in ("dlat", "dlon", "label", "km", "price", "cands", "far_ok", "mult", "heavy"):
            p.pop(k, None)
    cands = await geocode(m.text, near=(p["plat"], p["plon"]))
    if not cands:
        await m.answer(
            "Bakı daxilində bu ünvanı tapa bilmədim. Daha dəqiq yazın "
            "və ya 📎 → Yer vasitəsilə xəritədən nöqtə göndərin.",
            reply_markup=with_home(),
        )
        return
    best = cands[0]
    if best["score"] >= 1 and (len(cands) == 1 or cands[1]["score"] < 1):
        await quote(m, p, best["lat"], best["lon"], best["label"])
        return
    p["cands"] = cands
    kb = with_home([
        [InlineKeyboardButton(text=f"{i + 1}. {c.get('btn', c['label'])[:62]}", callback_data=f"g:{i}")]
        for i, c in enumerate(cands)
    ])
    note = ("Bir neçə uyğun ünvan tapdım." if best["score"] >= 1
            else "Dəqiq uyğunluq tapa bilmədim. Bunlardan biri sizin yerinizdir?")
    await m.answer(f"{note}\nSeçin və ya 📎 → Yer ilə xəritədən nöqtə göndərin:", reply_markup=kb)


def parse_weight(text: str):
    m = re.search(r"\d+(?:[.,]\d+)?", text or "")
    if not m:
        return None
    w = float(m.group().replace(",", "."))
    return round(w, 1) if 0 < w <= 200 else None


async def quote(m: Message, p: dict, dlat, dlon, label, show_map=True):
    """show_map=False: müştəri təyinatı özü xəritə nöqtəsi kimi göndərib (onun öz mesajı artıq xəritədir)."""
    if show_map and p.get("map_for") != (dlat, dlon):         # eyni təyinat üçün xəritə təkrar göndərilmir
        p["map_for"] = (dlat, dlon)
        await send_map(m.bot, m.chat.id, dlat, dlon, title=label, address="🏁 Gediləcək yer")
    if p.get("kind") == "courier" and "weight" not in p:   # kuryerdə qiymətdən əvvəl çəki soruşulur
        p.update(dlat=dlat, dlon=dlon, label=label, await_weight=True)
        await m.answer(WEIGHT_ASK, reply_markup=with_home())
        return
    km = await route_km(p["plat"], p["plon"], dlat, dlon)
    if km is None:
        await m.answer("Marşrutu hesablaya bilmədim. Bir az sonra yenidən cəhd edin.", reply_markup=with_home())
        return
    price, mult = calc_price(km)
    heavy = p.get("weight", 0) > HEAVY_KG
    if heavy:
        price = round(price * HEAVY_MULT, 1)
    p.update(dlat=dlat, dlon=dlon, label=label, km=km, price=price, mult=mult, heavy=heavy)
    if km > FAR_KM and not p.get("far_ok"):
        kb = with_home([
            [InlineKeyboardButton(text="✅ Bəli, davam et", callback_data="q_far")],
            [InlineKeyboardButton(text="✏️ Başqa ünvan yaz", callback_data="q_edit")],
        ])
        await m.answer(f"⚠️ Məsafə {fmt_num(km)} km-dir, bu uzaq məsafədir.\n🏁 Təyinat: {esc(label)}\n"
                       "Ünvan düzgündür?", reply_markup=kb)
        return
    await show_quote(m, p)


async def show_quote(m: Message, p: dict):
    price, mult, label = p["price"], p.get("mult", 1), p["label"]
    note = f" (pik saat ×{fmt_num(PEAK_MULT)})" if mult > 1 else ""
    kb = with_home([[
        InlineKeyboardButton(text="✅ Təsdiq et", callback_data="q_ok"),
        InlineKeyboardButton(text="❌ Ləğv et", callback_data="q_no"),
    ], [InlineKeyboardButton(text="✏️ Ünvanı dəyiş", callback_data="q_edit")]])
    await m.answer(f"🏁 Təyinat: {esc(label)}\n💰 Qiymət: <b>{fmt_money(price)}</b>{note}", reply_markup=kb)


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


@router.callback_query(F.data == "q_far")
async def quote_far(cb: CallbackQuery):
    p = pending.get(cb.from_user.id)
    if not p or "price" not in p:
        await cb.answer("Vaxt keçib. /start yazın.", show_alert=True)
        return
    p["far_ok"] = True
    await cb.message.edit_reply_markup(reply_markup=None)
    await show_quote(cb.message, p)
    await cb.answer()


@router.callback_query(F.data == "q_edit")
async def quote_edit(cb: CallbackQuery):
    p = pending.get(cb.from_user.id)
    if not p or "plat" not in p:
        await cb.answer("Vaxt keçib. /start yazın.", show_alert=True)
        return
    for k in ("dlat", "dlon", "label", "km", "price", "cands", "far_ok", "mult", "heavy"):
        p.pop(k, None)
    await cb.message.edit_reply_markup(reply_markup=None)
    await cb.message.answer("Yeni təyinat ünvanını yazın və ya 📎 → Yer ilə xəritədən nöqtə göndərin.",
                            reply_markup=with_home())
    await cb.answer()


@router.callback_query(F.data == "q_no")
async def quote_cancel(cb: CallbackQuery):
    pending.pop(cb.from_user.id, None)
    await cb.message.edit_text("Ləğv edildi.", reply_markup=with_home())
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
    await next_order_step(cb.message, uid, cb.from_user.full_name, p)
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
    except Exception as e:
        logging.error("group send failed: chat_id=%s xəta=%s: %s", group_for(o["kind"]), type(e).__name__, e)
        try:
            await bot.send_message(ADMIN_ID, f"⚠️ Sifariş #{oid} qrupa göndərilə bilmədi.\n"
                                   f"Qrup ID: <code>{group_for(o['kind'])}</code>\nXəta: {esc(type(e).__name__)}: {esc(e)}"[:900])
        except Exception:
            pass
    return sent, group_ok


def cancel_kb(oid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🚫 Sifarişi ləğv et", callback_data=f"cx:{oid}")]])


async def dispatch_order(bot, uid: int, uname: str, p: dict):
    plabel = p.get("plabel")
    if plabel is None:                                         # hələ tapılmayıbsa qısa gözlə
        try:
            plabel = await asyncio.wait_for(reverse_label(p["plat"], p["plon"]), 5)
        except Exception:
            plabel = None
    _, oid = execute(
        "INSERT INTO orders(customer_id,customer_name,kind,plat,plon,dlat,dlon,dest_label,km,price,note,weight,recv_phone,"
        "created,pickup_label) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
        (uid, uname, p.get("kind", "taxi"), p["plat"], p["plon"], p["dlat"], p["dlon"], p["label"],
         p["km"], p["price"], p.get("note", ""), p.get("weight"), p.get("recv_phone"), datetime.now(TZ).isoformat(),
         plabel or None),
    )
    if not plabel:
        spawn(fill_pickup_label(oid, p["plat"], p["plon"]))   # alınmayıbsa sonradan tarixçə üçün doldurulur
    sent, group_ok = await offer_order(bot, oid)
    if sent == 0 and not group_ok:
        execute("UPDATE orders SET status='nodriver' WHERE id=?", (oid,))
        await bot.send_message(uid, "😕 Sifarişi çatdıra bilmədim. Bir az sonra yenidən cəhd edin.",
                               reply_markup=with_home())
        return
    cour = p.get("kind") == "courier"
    parts = []
    if sent:
        parts.append(f"{sent} yaxın {'kuryerə' if cour else 'sürücüyə'}")
    if group_ok:
        parts.append("kuryerlər qrupuna" if cour else "sürücülər qrupuna")
    await bot.send_message(
        uid, f"✅ Sifariş #{oid} {' və '.join(parts)} göndərildi. Qəbul edən kimi məlumat gələcək.",
        reply_markup=kb_home(cancel_kb(oid)),
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
    price = f"💸 {fmt_money(o['price'])}"
    avg, cnt = rating_of_worker(d["user_id"], o["kind"])
    star = [f"⭐ {avg:.1f}"] if cnt >= MIN_RATINGS_SHOWN else []
    if o["kind"] == "courier":
        lines = ["✅ <b>Kuryer tapıldı!</b>", f"👤 {esc(d['name'])}", f"📞 {esc(d['phone'])}", f"🛵 {esc(d['car'])}"]
        if d["plate"] and norm(d["plate"]) not in ("yoxdur", "-"):
            lines.append(f"🔢 {esc(d['plate'])}")
        return "\n".join(lines + star + [price])
    return "\n".join(["✅ <b>Sürücü tapıldı!</b>", f"👤 {esc(d['name'])}", f"📞 {esc(d['phone'])}",
                      f"🚗 {esc(d['car'])}", f"🔢 {esc(d['plate'])}"] + star + [price])


@router.callback_query(F.data.startswith("acc:"))
async def accept(cb: CallbackQuery):
    oid = int(cb.data[4:])
    o0 = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    if not o0:
        await cb.answer("Sifariş tapılmadı.", show_alert=True)
        return
    d = fetch("SELECT * FROM drivers WHERE user_id=? AND kind=? AND approved=1", (cb.from_user.id, o0["kind"]))
    if not d:
        msg = ("Bu sifariş sizin xidmət növünüz üçün deyil." if approved_kinds(cb.from_user.id)
               else "Siz təsdiqlənmiş deyilsiniz. Botda qeydiyyatdan keçin: /start")
        await cb.answer(msg, show_alert=True)
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
    # qəbul edənə iki xəritə mesajı: götürülmə yeri və gediləcək yer (düymələr olan mesaj ən sonda qalır)
    await send_map(cb.bot, d["user_id"], o["plat"], o["plon"], title="📍 Götürülmə yeri",
                   address=o["pickup_label"] or "Müştərinin yeri")
    await send_map(cb.bot, d["user_id"], o["dlat"], o["dlon"], title="🏁 Gediləcək yer", address=o["dest_label"])
    try:
        dmsg = await cb.bot.send_message(d["user_id"], driver_dm_text(o), reply_markup=order_driver_kb(o))
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


async def _worker_order(cb: CallbackQuery, oid: int):
    """Düyməni basan sürücü/kuryerin aktiv sifarişi (yoxsa None)."""
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    if not o or o["status"] != "accepted" or o["driver_id"] != cb.from_user.id:
        await cb.answer("Sifariş aktiv deyil.", show_alert=True)
        return None
    return o


async def _refresh_driver_msg(cb: CallbackQuery, oid: int):
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    try:
        await cb.message.edit_text(driver_dm_text(o), reply_markup=order_driver_kb(o) if o["status"] == "accepted" else None)
    except Exception:
        logging.warning("driver message edit failed for order %s", oid)
    return o


@router.callback_query(F.data.startswith("arr:"))
async def arrived(cb: CallbackQuery):
    oid = int(cb.data[4:])
    if not await _worker_order(cb, oid):
        return
    n, _ = execute("UPDATE orders SET stage='arrived', arrived_at=? WHERE id=? AND status='accepted' "
                   "AND driver_id=? AND stage IS NULL", (datetime.now(TZ).isoformat(), oid, cb.from_user.id))
    if not n:
        await cb.answer("Bu mərhələ artıq keçilib.", show_alert=True)
        return
    o = await _refresh_driver_msg(cb, oid)
    who = "Kuryer" if o["kind"] == "courier" else "Sürücü"
    try:
        await cb.bot.send_message(o["customer_id"], f"📍 {who} çatdı, sizi gözləyir.")
    except Exception:
        logging.warning("customer %s notify failed", o["customer_id"])
    await cb.answer("Müştəri xəbərdar edildi ✅")


@router.callback_query(F.data.startswith("go:"))
async def trip_start(cb: CallbackQuery):
    oid = int(cb.data[3:])
    if not await _worker_order(cb, oid):
        return
    n, _ = execute("UPDATE orders SET stage='started', started_at=? WHERE id=? AND status='accepted' "
                   "AND driver_id=? AND stage='arrived'", (datetime.now(TZ).isoformat(), oid, cb.from_user.id))
    if not n:
        await cb.answer("Bu mərhələ artıq keçilib.", show_alert=True)
        return
    o = await _refresh_driver_msg(cb, oid)
    cour = o["kind"] == "courier"
    if o["cust_msg_id"]:        # müştərinin kartında ləğv düyməsi artıq yoxdur
        try:
            await cb.bot.edit_message_reply_markup(chat_id=o["customer_id"], message_id=o["cust_msg_id"],
                                                   reply_markup=order_customer_kb(oid, "started"))
        except Exception:
            pass
    try:
        await cb.bot.send_message(o["customer_id"], "🛵 Çatdırılma başladı." if cour else "▶️ Gediş başladı.")
    except Exception:
        logging.warning("customer %s notify failed", o["customer_id"])
    await cb.answer()


@router.callback_query(F.data.startswith("fin:"))
async def finish(cb: CallbackQuery):
    oid = int(cb.data[4:])
    n, _ = execute("UPDATE orders SET status='done', finished_at=? WHERE id=? AND status='accepted' AND driver_id=?",
                   (datetime.now(TZ).isoformat(), oid, cb.from_user.id))
    if not n:
        await cb.answer("Sifariş aktiv deyil.", show_alert=True)
        return
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    try:
        await cb.message.edit_text(driver_dm_text(o), reply_markup=None)
    except Exception:
        try:
            await cb.message.edit_reply_markup(reply_markup=None)
        except Exception:
            pass
    # sürücü/kuryer dərhal müştərini qiymətləndirir
    await cb.message.answer(f"✅ Sifariş #{oid} tamamlandı. 💸 {fmt_money(o['price'])}\n\n<b>Müştərini qiymətləndirin:</b>",
                            reply_markup=stars_kb(oid, "c"))
    if o["cust_msg_id"]:
        try:
            await cb.bot.edit_message_reply_markup(chat_id=o["customer_id"], message_id=o["cust_msg_id"], reply_markup=None)
        except Exception:
            pass
    who = "kuryeri" if o["kind"] == "courier" else "sürücünü"
    try:
        await cb.bot.send_message(o["customer_id"], f"✅ Sifariş #{oid} tamamlandı. Təşəkkür edirik! 🙏\n\n<b>{who.capitalize()} qiymətləndirin:</b>",
                                  reply_markup=stars_kb(oid, "w"))
    except Exception:
        logging.warning("customer %s notify failed", o["customer_id"])
    await cb.answer()


# ---------- Reytinq ----------
MIN_RATINGS_SHOWN = int(os.environ.get("MIN_RATINGS_SHOWN", "3"))   # reytinq müştəriyə bu qədər qiymətdən sonra göstərilir
LOW_STARS = 2                                                      # bu və ya aşağı qiymətdə admin xəbərdar olunur
awaiting_comment: dict[int, tuple] = {}                            # istifadəçi -> (sifariş, kim qiymətləndirilir, vaxt)


def stars_kb(oid: int, target: str) -> InlineKeyboardMarkup:
    """target: 'c' = müştəri qiymətləndirilir, 'w' = sürücü/kuryer qiymətləndirilir."""
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text=f"{n}⭐", callback_data=f"rt:{oid}:{target}:{n}") for n in range(1, 6)
    ]])


def rating_of_worker(uid: int, kind: str):
    r = fetch("SELECT AVG(r.stars) AS a, COUNT(*) AS c FROM ratings r JOIN orders o ON o.id=r.order_id "
              "WHERE r.target='w' AND o.driver_id=? AND o.kind=?", (uid, kind))
    return (r["a"] or 0.0, r["c"] or 0) if r else (0.0, 0)


def rating_of_customer(uid: int):
    r = fetch("SELECT AVG(r.stars) AS a, COUNT(*) AS c FROM ratings r JOIN orders o ON o.id=r.order_id "
              "WHERE r.target='c' AND o.customer_id=?", (uid,))
    return (r["a"] or 0.0, r["c"] or 0) if r else (0.0, 0)


@router.callback_query(F.data.startswith("rt:"))
async def rate(cb: CallbackQuery):
    try:
        _, oid, target, n = cb.data.split(":")
        oid, n = int(oid), int(n)
    except ValueError:
        await cb.answer()
        return
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    uid = cb.from_user.id
    ok = (o and o["status"] == "done" and 1 <= n <= 5 and
          ((target == "c" and o["driver_id"] == uid) or (target == "w" and o["customer_id"] == uid)))
    if not ok:
        await cb.answer("Qiymətləndirmək mümkün deyil.", show_alert=True)
        return
    ratee = o["customer_id"] if target == "c" else o["driver_id"]
    cnt, _ = execute("INSERT OR IGNORE INTO ratings(order_id,target,rater_id,ratee_id,stars,created) VALUES(?,?,?,?,?,?)",
                     (oid, target, uid, ratee, n, datetime.now(TZ).isoformat()))
    if not cnt:
        try:
            await cb.message.edit_reply_markup(reply_markup=None)
        except Exception:
            pass
        await cb.answer("Artıq qiymətləndirmisiniz.", show_alert=True)
        return
    what = "Müştəriyə" if target == "c" else ("Kuryerə" if o["kind"] == "courier" else "Sürücüyə")
    low = n <= LOW_STARS
    text = f"Təşəkkürlər! {what} {n}⭐ verdiniz."
    kb = None
    if low:
        text += "\nİstəsəniz səbəbi qısaca yazın (ixtiyari)."
        kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="➡️ Keç", callback_data=f"rs:{oid}:{target}")]])
        awaiting_comment[uid] = (oid, target, time.time())
    try:
        await cb.message.edit_text(text, reply_markup=kb)
    except Exception:
        pass
    if low:
        try:
            who = "Sürücü/kuryer" if target == "c" else "Müştəri"
            whom = "müştərini" if target == "c" else "sürücünü/kuryeri"
            await cb.bot.send_message(ADMIN_ID, f"⚠️ Aşağı reytinq: {who} {whom} {n}⭐ qiymətləndirdi.\n"
                                      f"Sifariş #{oid} ({kind_title(o['kind'])}), rater ID: {uid}, qiymətləndirilən ID: {ratee}")
        except Exception:
            pass
    await cb.answer()


@router.callback_query(F.data.startswith("rs:"))
async def rate_skip(cb: CallbackQuery):
    awaiting_comment.pop(cb.from_user.id, None)
    try:
        await cb.message.edit_text("Təşəkkürlər!", reply_markup=None)
    except Exception:
        pass
    await cb.answer()


async def save_comment(m: Message) -> bool:
    """Aşağı qiymətdən sonra yazılan səbəbi yadda saxlayır. Mətn səbəb kimi işlənibsə True qaytarır."""
    cur = awaiting_comment.pop(m.from_user.id, None)
    if not cur:
        return False
    oid, target, ts = cur
    if time.time() - ts > 600:          # 10 dəqiqədən sonra adi mətn kimi işlənir
        return False
    text = (m.text or "").strip()[:300]
    execute("UPDATE ratings SET comment=? WHERE order_id=? AND target=? AND rater_id=?", (text, oid, target, m.from_user.id))
    await m.answer("Təşəkkürlər, qeyd olundu.", reply_markup=with_home())
    try:
        await m.bot.send_message(ADMIN_ID, f"📝 Sifariş #{oid} üçün aşağı reytinqin səbəbi:\n{esc(text)}")
    except Exception:
        pass
    return True


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
    if not o or o["status"] != "accepted" or o["driver_id"] != cb.from_user.id or o["stage"] == "started":
        await cb.answer("Sifariş aktiv deyil və ya gediş artıq başlayıb.", show_alert=True)
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
    n, _ = execute("UPDATE orders SET status='new', driver_id=NULL, stage=NULL, arrived_at=NULL WHERE id=? "
                   "AND status='accepted' AND driver_id=? AND (stage IS NULL OR stage!='started')", (oid, uid))
    if not n:
        await cb.answer("Sifariş aktiv deyil.", show_alert=True)
        return
    d = fetch("SELECT * FROM drivers WHERE user_id=? AND kind=?", (uid, o["kind"]))
    wlabel = "Kuryer" if o["kind"] == "courier" else "Sürücü"
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
            await cb.bot.edit_message_text(f"{wlabel} sifarişdən imtina etdi.", chat_id=o["customer_id"],
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
        await cb.bot.send_message(o["customer_id"], f"😕 {wlabel} imtina etdi, yenisini tapa bilmədim. Yenidən cəhd edin.",
                                  reply_markup=with_home())
        execute("UPDATE orders SET status='nodriver' WHERE id=?", (oid,))
    else:
        await cb.bot.send_message(o["customer_id"], f"⚠️ {wlabel} imtina etdi. Sizə yenisini axtarırıq…",
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
    if not o or o["status"] != "accepted" or o["customer_id"] != cb.from_user.id or o["stage"] == "started":
        await cb.answer("Sifariş aktiv deyil və ya gediş artıq başlayıb.", show_alert=True)
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
    n, _ = execute("UPDATE orders SET status='cancelled' WHERE id=? AND customer_id=? AND status='accepted' "
                   "AND (stage IS NULL OR stage!='started')", (oid, cb.from_user.id))
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


# ---------- Profil və statistika ----------
def short(s, n=26) -> str:
    s = str(s or "").strip()
    return s if len(s) <= n else s[: n - 1].rstrip() + "…"


def fmt_when(iso) -> str:
    try:
        return datetime.fromisoformat(iso).strftime("%d.%m %H:%M")
    except Exception:
        return "—"


def route_line(o) -> str:
    return f"{esc(short(o['pickup_label'] or 'xəritə nöqtəsi'))} → {esc(short(o['dest_label']))}"


def first_name(s) -> str:
    parts = str(s or "").split()
    return parts[0] if parts else "—"


def worker_profile_text(uid: int, kind: str) -> str:
    d = fetch("SELECT * FROM drivers WHERE user_id=? AND kind=?", (uid, kind))
    rows = fetchall(
        "SELECT o.*, COALESCE(o.finished_at, o.created) AS t, r.stars AS got FROM orders o "
        "LEFT JOIN ratings r ON r.order_id=o.id AND r.target='w' "
        "WHERE o.driver_id=? AND o.kind=? AND o.status='done' ORDER BY o.id DESC", (uid, kind))
    now = datetime.now(TZ).date()
    marks = {"Bu gün": now.isoformat(), "Son 7 gün": (now - timedelta(days=6)).isoformat(),
             "Bu ay": now.replace(day=1).isoformat(), "Cəmi": ""}
    role = "🛵 Kuryer" if kind == "courier" else "🚕 Sürücü"
    avg, cnt = rating_of_worker(uid, kind)
    lines = [f"👤 <b>Profilim</b> · {role}", esc(d["name"] if d else "")]
    lines.append(f"⭐ {avg:.1f} ({cnt} qiymət)" if cnt else "⭐ Hələ qiymət yoxdur")
    lines += ["", "<b>Qazanc</b>"]
    for title, since in marks.items():
        sel = [r for r in rows if (r["t"] or "") >= since]
        lines.append(f"{title}: {len(sel)} sifariş · {fmt_money(sum(r['price'] or 0 for r in sel))}")
    c24 = recent_cancels(uid, "driver")
    lines.append(f"Son 24 saatda imtina: {c24}")
    lines += ["", "<b>Son sifarişlər</b>"]
    if not rows:
        lines.append("Hələ tamamlanmış sifariş yoxdur.")
    for i, o in enumerate(rows[:10], 1):
        star = f" · ⭐{o['got']}" if o["got"] else ""
        lines.append(f"{i}. {fmt_when(o['t'])} · {fmt_money(o['price'])} · {fmt_dist(o['km'])}{star}\n"
                     f"    {route_line(o)}\n    👤 {esc(first_name(o['customer_name']))}")
    return "\n".join(lines)


def customer_history_text(uid: int) -> str:
    rows = fetchall(
        "SELECT o.*, COALESCE(o.finished_at, o.created) AS t, d.name AS dname, d.plate AS dplate, r.stars AS got "
        "FROM orders o LEFT JOIN drivers d ON d.user_id=o.driver_id AND d.kind=o.kind "
        "LEFT JOIN ratings r ON r.order_id=o.id AND r.target='c' "
        "WHERE o.customer_id=? AND o.status IN ('done','cancelled') ORDER BY o.id DESC", (uid,))
    done = [r for r in rows if r["status"] == "done"]
    lines = ["📋 <b>Sifarişlərim</b>", f"Tamamlanan: {len(done)} · Ümumi: {fmt_money(sum(r['price'] or 0 for r in done))}"]
    avg, cnt = rating_of_customer(uid)
    if cnt >= MIN_RATINGS_SHOWN:
        lines.append(f"⭐ Reytinqiniz: {avg:.1f} ({cnt} qiymət)")
    lines += ["", "<b>Son sifarişlər</b>"]
    if not rows:
        lines.append("Hələ sifariş yoxdur.")
    for i, o in enumerate(rows[:10], 1):
        icon = "✅" if o["status"] == "done" else "🚫"
        kind = "🛵" if o["kind"] == "courier" else "🚕"
        who = f"\n    {kind} {esc(o['dname'])}" + (f" ({esc(o['dplate'])})" if o["dplate"] and norm(o["dplate"]) not in ("yoxdur", "-") else "") if o["dname"] else ""
        lines.append(f"{i}. {icon} {fmt_when(o['t'])} · {fmt_money(o['price'])}\n    {route_line(o)}{who}")
    return "\n".join(lines)


@router.callback_query(F.data.startswith("prof:"))
async def cb_profile(cb: CallbackQuery):
    kind = "courier" if cb.data == "prof:courier" else "taxi"
    if kind not in approved_kinds(cb.from_user.id):
        await cb.answer("Bu rol üçün təsdiqlənməmisiniz.", show_alert=True)
        return
    await cb.message.answer(worker_profile_text(cb.from_user.id, kind), reply_markup=with_home())
    await cb.answer()


@router.callback_query(F.data == "my")
async def cb_my_orders(cb: CallbackQuery):
    await cb.message.answer(customer_history_text(cb.from_user.id), reply_markup=with_home())
    await cb.answer()


@router.message(Command("profil"), F.chat.type == ChatType.PRIVATE)
async def cmd_profile(m: Message):
    kinds = sorted(approved_kinds(m.from_user.id))
    if not kinds:
        await m.answer("Profil yalnız təsdiqlənmiş sürücü və kuryerlər üçündür. Sifarişləriniz üçün /sifarisler")
        return
    for k in kinds:
        await m.answer(worker_profile_text(m.from_user.id, k), reply_markup=with_home())


@router.message(Command("sifarisler"), F.chat.type == ChatType.PRIVATE)
async def cmd_my_orders(m: Message):
    await m.answer(customer_history_text(m.from_user.id), reply_markup=with_home())


# ---------- Qeydiyyat ----------
class AddPlace(StatesGroup):
    pin = State()
    name = State()


def _is_admin(m: Message) -> bool:
    return m.from_user.id == ADMIN_ID and m.chat.type == ChatType.PRIVATE


@router.message(Command("yer_elave"))
async def cmd_place_add(m: Message, state: FSMContext):
    if not _is_admin(m):
        return
    await state.set_state(AddPlace.pin)
    await m.answer("📍 Yerin dəqiq nöqtəsini göndərin (📎 → Yer, xəritədə nöqtəni seçin). Ləğv etmək üçün /legv.")


@router.message(Command("legv"))
async def cmd_place_cancel(m: Message, state: FSMContext):
    if _is_admin(m):
        await state.clear()
        await m.answer("Ləğv edildi.")


@router.message(AddPlace.pin, F.location)
async def place_pin(m: Message, state: FSMContext):
    if not _is_admin(m):
        return
    await state.update_data(lat=m.location.latitude, lon=m.location.longitude)
    await state.set_state(AddPlace.name)
    await m.answer("Adını yazın. Müştəri bu sözlərlə axtaracaq, məs.: <i>27 nömrəli məktəb (Xətai)</i>")


@router.message(AddPlace.name, F.text, ~F.text.startswith("/"))
async def place_name(m: Message, state: FSMContext):
    if not _is_admin(m):
        return
    data = await state.get_data()
    name = m.text.strip()[:80]
    _, pid = execute("INSERT INTO places(name,lat,lon) VALUES(?,?,?)", (name, data["lat"], data["lon"]))
    await state.clear()
    await m.answer(f"✅ Əlavə olundu (#{pid}): {esc(name)}\nBaşqa yer üçün /yer_elave, siyahı üçün /yerler.")


@router.message(Command("yerler"))
async def cmd_places(m: Message):
    if not _is_admin(m):
        return
    rows = fetchall("SELECT * FROM places ORDER BY id")
    if not rows:
        await m.answer("Siyahı boşdur. Əlavə etmək üçün /yer_elave")
        return
    txt = "\n".join(f"#{r['id']} {esc(r['name'])}" for r in rows)
    await m.answer(f"<b>Yerlər</b>\n{txt[:3500]}\n\nSilmək üçün: /yer_sil nömrə")


@router.message(Command("yer_sil"))
async def cmd_place_del(m: Message):
    if not _is_admin(m):
        return
    arg = (m.text or "").split(maxsplit=1)[1:] or [""]
    if not arg[0].strip().lstrip("#").isdigit():
        await m.answer("Nömrə yazın, məs.: /yer_sil 3")
        return
    n, _ = execute("DELETE FROM places WHERE id=?", (int(arg[0].strip().lstrip("#")),))
    await m.answer("Silindi." if n else "Belə nömrə tapılmadı.")


class Reg(StatesGroup):
    name = State()
    phone = State()
    car = State()
    plate = State()


async def _reg_start(target: Message, state: FSMContext, kind: str):
    await state.set_state(Reg.name)
    await state.update_data(kind=kind)
    await target.answer(f"{'Kuryer' if kind == 'courier' else 'Sürücü'} qeydiyyatı. Ad və soyadınızı yazın:",
                        reply_markup=home_kb())


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
    await m.answer("Mobil nömrənizi yazın (məs. +994501234567):", reply_markup=with_home())


@router.message(Reg.phone, F.text)
async def reg_phone(m: Message, state: FSMContext):
    await state.update_data(phone=m.text.strip())
    await state.set_state(Reg.car)
    kind = (await state.get_data()).get("kind", "taxi")
    await m.answer("Nəqliyyat növü (velosiped, moto, avtomobil):" if kind == "courier"
                   else "Maşın modeli və rəngi (məs. Hyundai Elantra, ağ):", reply_markup=with_home())


@router.message(Reg.car, F.text)
async def reg_car(m: Message, state: FSMContext):
    await state.update_data(car=m.text.strip())
    await state.set_state(Reg.plate)
    kind = (await state.get_data()).get("kind", "taxi")
    await m.answer("Dövlət nömrəsi (yoxdursa «yoxdur» yazın):" if kind == "courier"
                   else "Dövlət nömrəsi (məs. 10-AA-123):", reply_markup=with_home())


@router.message(Reg.plate, F.text)
async def reg_plate(m: Message, state: FSMContext):
    data = await state.get_data()
    await state.clear()
    uid = m.from_user.id
    kind = data.get("kind", "taxi")
    approved = 1 if uid == ADMIN_ID else 0
    execute(
        "INSERT INTO drivers(user_id,name,phone,car,plate,approved,kind) VALUES(?,?,?,?,?,?,?) "
        "ON CONFLICT(user_id, kind) DO UPDATE SET name=excluded.name, phone=excluded.phone, car=excluded.car, "
        "plate=excluded.plate, approved=excluded.approved",
        (uid, data["name"], data["phone"], data["car"], m.text.strip(), approved, kind),
    )
    if approved:
        await m.answer("✅ Qeydiyyat tamamlandı, siz təsdiqlənmisiniz. İşə başlamaq üçün /onlayn yazın.",
                       reply_markup=with_home())
        return
    await m.answer("Qeydiyyat göndərildi. Admin təsdiqləyəndən sonra /onlayn yazıb işə başlaya biləcəksiniz.",
                   reply_markup=with_home())
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Təsdiq et", callback_data=f"appr:{uid}:{kind}"),
        InlineKeyboardButton(text="🚫 Rədd et", callback_data=f"deny:{uid}:{kind}"),
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
    parts = cb.data.split(":")
    action, uid = parts[0], int(parts[1])
    kind = parts[2] if len(parts) > 2 else None           # köhnə düymələrdə rol yoxdur: hamısına aid olur
    where, args = ("user_id=? AND kind=?", (uid, kind)) if kind else ("user_id=?", (uid,))
    if action == "appr":
        execute(f"UPDATE drivers SET approved=1 WHERE {where}", args)
        await cb.message.edit_text(cb.message.html_text + "\n\n✅ Təsdiqləndi")
        note = "✅ Qeydiyyatınız təsdiqləndi. İşə başlamaq üçün canlı yer paylaşın (/onlayn)."
    else:
        execute(f"UPDATE drivers SET approved=0, online=0 WHERE {where}", args)
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
    BOT_REF["bot"] = bot
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    await bot.delete_webhook(drop_pending_updates=True)
    try:
        await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
    finally:
        await runner.cleanup()


if __name__ == "__main__":
    asyncio.run(main())
