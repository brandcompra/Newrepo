import asyncio
import html
import logging
import math
import os
import sqlite3
import time
from datetime import datetime
from zoneinfo import ZoneInfo

import aiohttp
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ChatType, ParseMode
from aiogram.filters import Command, CommandStart, StateFilter
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
)

logging.basicConfig(level=logging.INFO)

# ---------- Ayarlar (hostingdə "Variables" bölməsində yazılır) ----------
BOT_TOKEN = os.environ["BOT_TOKEN"]
GROUP_ID = int(os.environ["GROUP_ID"])      # sürücülər qrupunun ID-si
ADMIN_ID = int(os.environ["ADMIN_ID"])      # sizin şəxsi Telegram ID-niz
ORS_KEY = os.environ["ORS_KEY"]             # OpenRouteService API açarı
DB_PATH = os.environ.get("DB_PATH", "taxi.db")

# Radius: şəxsi bildiriş yalnız bu düz xətt radiusundakı sürücülərə gedir
RADIUS_KM = float(os.environ.get("RADIUS_KM", "1.3"))
# Yeri bu müddətdən (dəqiqə) çox yenilənməyən sürücü oflayn sayılır
LOC_MAX_AGE_MIN = int(os.environ.get("LOC_MAX_AGE_MIN", "12"))

# Ünvan axtarışı yalnız Bakı mərkəzindən bu radiusda (km) aparılır
BAKU_LAT, BAKU_LON = 40.4093, 49.8671
GEO_RADIUS_KM = float(os.environ.get("GEO_RADIUS_KM", "25"))

# ---------- Tarif ----------
PER_KM = float(os.environ.get("PER_KM", "0.2"))
MIN_PRICE = float(os.environ.get("MIN_PRICE", "2.0"))
PEAK_MULT = float(os.environ.get("PEAK_MULT", "1.3"))
PEAK_HOURS = [(7 * 60 + 30, 10 * 60), (17 * 60, 20 * 60)]  # dəqiqə ilə
TZ = ZoneInfo("Asia/Baku")

ORS_BASE = "https://api.heigit.org/openrouteservice/v2"
GEOCODE_URL = "https://api.heigit.org/pelias/v1/search"

router = Router()
pending: dict[int, dict] = {}  # müştərinin hazırda yaradılan sifarişi


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
            online INTEGER DEFAULT 0
        );
        CREATE TABLE IF NOT EXISTS orders(
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            customer_id INTEGER, customer_name TEXT,
            plat REAL, plon REAL, dlat REAL, dlon REAL, dest_label TEXT,
            km REAL, price REAL,
            status TEXT DEFAULT 'new',
            driver_id INTEGER, group_msg_id INTEGER,
            created TEXT
        );
        CREATE TABLE IF NOT EXISTS notifs(
            order_id INTEGER, chat_id INTEGER, msg_id INTEGER, driver_id INTEGER
        );
        """
    )
    # köhnə bazadan yeniləmə: yeni sütunları əlavə et (varsa, xəta verməz)
    for col, typ in (("lat", "REAL"), ("lon", "REAL"), ("loc_time", "REAL"), ("online", "INTEGER DEFAULT 0")):
        try:
            conn.execute(f"ALTER TABLE drivers ADD COLUMN {col} {typ}")
        except sqlite3.OperationalError:
            pass
    conn.commit()
    conn.close()


# ---------- Məsafə ----------
def dist_km(lat1, lon1, lat2, lon2) -> float:
    """İki nöqtə arasındakı düz xətt məsafəsi (km), haversine."""
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dphi = p2 - p1
    dl = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def fmt_dist(km: float) -> str:
    """1 km-dən azdırsa metr ilə (məs. 750 metr), çoxdursa km ilə (məs. 1.3 km)."""
    m = int(round(km * 100) * 10)  # 10 metrə yuvarlaqlaşdır
    if m < 1000:
        return f"{max(m, 10)} metr"
    return f"{km:.1f} km"


def nearby_drivers(lat, lon):
    """Düz xətt radiusundakı təsdiqlənmiş, onlayn və yeri təzə olan sürücülər: [(düz_xətt_km, sürücü)]."""
    rows = fetchall(
        "SELECT * FROM drivers WHERE approved=1 AND online=1 AND lat IS NOT NULL AND loc_time>?",
        (time.time() - LOC_MAX_AGE_MIN * 60,),
    )
    res = []
    for d in rows:
        km = dist_km(lat, lon, d["lat"], d["lon"])
        if km <= RADIUS_KM:
            res.append((km, d))
    res.sort(key=lambda x: x[0])
    return res


async def road_distances(plat, plon, drivers):
    """Hər sürücüdən götürülmə nöqtəsinə yol məsafəsi (km). Alınmasa düz xətt məsafəsi qaytarılır."""
    fallback = [dist_km(plat, plon, d["lat"], d["lon"]) for d in drivers]
    if not drivers:
        return []
    locs = [[plon, plat]] + [[d["lon"], d["lat"]] for d in drivers]
    body = {
        "locations": locs,
        "sources": list(range(1, len(locs))),
        "destinations": [0],
        "metrics": ["distance"],
        "units": "km",
    }
    try:
        async with aiohttp.ClientSession() as s:
            async with s.post(
                f"{ORS_BASE}/matrix/driving-car",
                json=body,
                headers={"Authorization": ORS_KEY},
                timeout=aiohttp.ClientTimeout(total=20),
            ) as r:
                data = await r.json()
        rows = data["distances"]
        return [row[0] if row and row[0] is not None else fb for row, fb in zip(rows, fallback)]
    except Exception:
        logging.exception("matrix error")
        return fallback


# ---------- Qiymət və marşrut ----------
def calc_price(km: float):
    now = datetime.now(TZ)
    minutes = now.hour * 60 + now.minute
    mult = 1.0
    for a, b in PEAK_HOURS:
        if a <= minutes < b:
            mult = PEAK_MULT
    price = max(MIN_PRICE, km * PER_KM * mult)
    return round(price, 1), mult


async def route_km(plat, plon, dlat, dlon):
    url = f"{ORS_BASE}/directions/driving-car"
    headers = {"Authorization": ORS_KEY}
    body = {"coordinates": [[plon, plat], [dlon, dlat]]}
    try:
        async with aiohttp.ClientSession() as s:
            async with s.post(url, json=body, headers=headers, timeout=aiohttp.ClientTimeout(total=20)) as r:
                data = await r.json()
        return data["routes"][0]["summary"]["distance"] / 1000
    except Exception:
        logging.exception("route error")
        return None


def pick_in_baku(features):
    """Nəticələr arasından Bakı radiusuna düşən ilk ünvanı seçir."""
    for f in features or []:
        try:
            lon, lat = f["geometry"]["coordinates"]
        except Exception:
            continue
        if dist_km(BAKU_LAT, BAKU_LON, lat, lon) <= GEO_RADIUS_KM:
            return lat, lon, f.get("properties", {}).get("label")
    return None


async def geocode(text: str):
    """Ünvanı koordinata çevirir; axtarış yalnız Bakı və ətrafı ilə məhdudlaşır."""
    for q in (f"{text}, Baku, Azerbaijan", text):
        params = {
            "api_key": ORS_KEY,
            "text": q,
            "boundary.country": "AZ",
            "boundary.circle.lat": str(BAKU_LAT),
            "boundary.circle.lon": str(BAKU_LON),
            "boundary.circle.radius": str(GEO_RADIUS_KM),
            "size": "10",
        }
        try:
            async with aiohttp.ClientSession() as s:
                async with s.get(GEOCODE_URL, params=params, timeout=aiohttp.ClientTimeout(total=20)) as r:
                    data = await r.json()
        except Exception:
            logging.exception("geocode error")
            continue
        res = pick_in_baku(data.get("features"))
        if res:
            lat, lon, label = res
            return lat, lon, label or text
    return None


# ---------- Köməkçilər ----------
def esc(s) -> str:
    return html.escape(str(s or ""))


def waze(lat, lon) -> str:
    return f"https://waze.com/ul?ll={lat:.6f},{lon:.6f}&navigate=yes"


def order_text(o, road_km=None) -> str:
    """Sürücüyə gedən mesaj. İki link heç vaxt alt-alta düşmür.
    Fərdi mesajda: götürülmə yeri / məsafə / gediləcək yer / ödəniş.
    Qrup mesajında (məsafə yoxdur): götürülmə yeri / ödəniş / gediləcək yer."""
    pickup = f"<a href=\"{waze(o['plat'], o['plon'])}\">Götürülmə yeri</a>"
    dest = f"<a href=\"{waze(o['dlat'], o['dlon'])}\">Gediləcək yer</a>: {esc(o['dest_label'])}"
    pay = f"Ödəniş məbləği: {o['price']:.1f} ₼"
    head = f"<b>Sifariş #{o['id']}</b>"
    if road_km is not None:
        return "\n".join([head, pickup, f"Məsafə: {fmt_dist(road_km)}", dest, pay])
    return "\n".join([head, pickup, pay, dest])


def accept_kb(oid: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[
            InlineKeyboardButton(text="✅ Qəbul et", callback_data=f"acc:{oid}"),
            InlineKeyboardButton(text="❌ İmtina", callback_data=f"rej:{oid}"),
        ]]
    )


def start_kb():
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="📍 Yerimi göndər (taksi çağır)", request_location=True)]],
        resize_keyboard=True,
    )


def set_driver_live(uid: int, loc) -> int:
    """Təsdiqlənmiş sürücü canlı yer paylaşanda onu onlayn edir və koordinatı saxlayır."""
    n, _ = execute(
        "UPDATE drivers SET online=1, lat=?, lon=?, loc_time=? WHERE user_id=? AND approved=1",
        (loc.latitude, loc.longitude, time.time(), uid),
    )
    return n


def update_driver_location(uid: int, loc) -> int:
    """Onlayn sürücünün koordinatını yeniləyir (oflayn olanın yeri yenilənmir)."""
    n, _ = execute(
        "UPDATE drivers SET lat=?, lon=?, loc_time=? WHERE user_id=? AND approved=1 AND online=1",
        (loc.latitude, loc.longitude, time.time(), uid),
    )
    return n


# ---------- Müştəri ----------
@router.message(CommandStart(), F.chat.type == ChatType.PRIVATE)
async def start(m: Message, state: FSMContext):
    await state.clear()
    await m.answer(
        "Salam! 🚕 Taksi çağırmaq üçün aşağıdakı düyməyə basıb yerinizi göndərin.\n\n"
        "Sürücüsünüzsə: qeydiyyat /driver, işə başlamaq üçün canlı yer paylaşın, dayandırmaq /oflayn",
        reply_markup=start_kb(),
    )


@router.message(Command("id"))
async def get_id(m: Message):
    await m.answer(f"Chat ID: <code>{m.chat.id}</code>")


@router.message(F.location, F.chat.type == ChatType.PRIVATE, StateFilter(None))
async def on_location(m: Message):
    uid = m.from_user.id
    loc = m.location

    # Canlı yer = sürücü işə başlayır
    if loc.live_period:
        if set_driver_live(uid, loc):
            await m.answer(
                f"🟢 Onlayn oldunuz. {RADIUS_KM:g} km radiusdakı sifarişlər sizə gələcək.\n"
                "Dayandırmaq üçün /oflayn yazın və canlı yer paylaşımını söndürün."
            )
        else:
            await m.answer(
                "Canlı yer yalnız təsdiqlənmiş sürücülər üçündür. Qeydiyyat: /driver\n"
                "Taksi çağırırsınızsa, 📍 düyməsi ilə adi yer göndərin."
            )
        return

    # Adi yer = müştəri sifariş yaradır
    p = pending.get(uid)
    if p is None or "dlat" in p:
        pending[uid] = {"plat": loc.latitude, "plon": loc.longitude}
        await m.answer(
            "Haraya gedəcəksiniz? Ünvanı yazın (məs. <i>28 Mall</i>) "
            "və ya 📎 → Yer vasitəsilə xəritədən nöqtə göndərin.",
            reply_markup=ReplyKeyboardRemove(),
        )
    else:
        await quote(m, p, loc.latitude, loc.longitude, "Xəritədən seçilmiş nöqtə")


@router.edited_message(F.location, F.chat.type == ChatType.PRIVATE)
async def on_live_location_update(m: Message):
    """Sürücünün canlı yeri hərəkət etdikcə Telegram bura yeniləmə göndərir."""
    update_driver_location(m.from_user.id, m.location)


@router.message(F.text, ~F.text.startswith("/"), F.chat.type == ChatType.PRIVATE, StateFilter(None))
async def on_text(m: Message):
    p = pending.get(m.from_user.id)
    if not p or "dlat" in p:
        await m.answer("Əvvəlcə yerinizi göndərin 👇", reply_markup=start_kb())
        return
    res = await geocode(m.text)
    if not res:
        await m.answer(
            "Bakı daxilində bu ünvanı tapa bilmədim. Daha dəqiq yazın "
            "və ya 📎 → Yer vasitəsilə xəritədən nöqtə göndərin."
        )
        return
    lat, lon, label = res
    await quote(m, p, lat, lon, label)


async def quote(m: Message, p: dict, dlat, dlon, label):
    km = await route_km(p["plat"], p["plon"], dlat, dlon)
    if km is None:
        await m.answer("Marşrutu hesablaya bilmədim. Bir az sonra yenidən cəhd edin.")
        return
    price, mult = calc_price(km)
    p.update(dlat=dlat, dlon=dlon, label=label, km=km, price=price)
    note = f" (pik saat ×{PEAK_MULT:g})" if mult > 1 else ""
    kb = InlineKeyboardMarkup(
        inline_keyboard=[[
            InlineKeyboardButton(text="✅ Təsdiq et", callback_data="q_ok"),
            InlineKeyboardButton(text="❌ Ləğv et", callback_data="q_no"),
        ]]
    )
    await m.answer(
        f"🏁 Təyinat: {esc(label)}\n💰 Qiymət: <b>{price:.1f} ₼</b>{note}",
        reply_markup=kb,
    )


@router.callback_query(F.data == "q_no")
async def quote_cancel(cb: CallbackQuery):
    pending.pop(cb.from_user.id, None)
    await cb.message.edit_text("Ləğv edildi. Yenidən sifariş üçün /start")
    await cb.answer()


@router.callback_query(F.data == "q_ok")
async def quote_ok(cb: CallbackQuery):
    p = pending.pop(cb.from_user.id, None)
    if not p or "price" not in p:
        await cb.answer("Sifariş vaxtı keçib. Yenidən /start yazın.", show_alert=True)
        return
    _, oid = execute(
        "INSERT INTO orders(customer_id,customer_name,plat,plon,dlat,dlon,dest_label,km,price,created) "
        "VALUES(?,?,?,?,?,?,?,?,?,?)",
        (cb.from_user.id, cb.from_user.full_name, p["plat"], p["plon"], p["dlat"], p["dlon"],
         p["label"], p["km"], p["price"], datetime.now(TZ).isoformat()),
    )
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))

    # 1) Düz xətt radiusundakı sürücülərə fərdi bildiriş (mesajda yol məsafəsi)
    near = nearby_drivers(o["plat"], o["plon"])
    roads = await road_distances(o["plat"], o["plon"], [d for _, d in near])
    sent = 0
    for (_, d), rkm in zip(near, roads):
        try:
            msg = await cb.bot.send_message(d["user_id"], order_text(o, rkm), reply_markup=accept_kb(oid))
            execute(
                "INSERT INTO notifs(order_id,chat_id,msg_id,driver_id) VALUES(?,?,?,?)",
                (oid, d["user_id"], msg.message_id, d["user_id"]),
            )
            sent += 1
        except Exception:
            logging.warning("driver %s bildiriş ala bilmədi (botu başlatmayıb?)", d["user_id"])

    # 2) Həmişə sürücülər qrupuna da (məsafəsiz, düymə ilə)
    group_ok = False
    try:
        gmsg = await cb.bot.send_message(GROUP_ID, order_text(o), reply_markup=accept_kb(oid))
        execute(
            "INSERT INTO notifs(order_id,chat_id,msg_id,driver_id) VALUES(?,?,?,NULL)",
            (oid, GROUP_ID, gmsg.message_id),
        )
        group_ok = True
    except Exception:
        logging.exception("group send failed")

    if sent == 0 and not group_ok:
        execute("UPDATE orders SET status='nodriver' WHERE id=?", (oid,))
        await cb.message.edit_text("😕 Sifarişi sürücülərə çatdıra bilmədim. Bir az sonra yenidən cəhd edin: /start")
        await cb.answer()
        return

    parts = []
    if sent:
        parts.append(f"{sent} yaxın sürücüyə")
    if group_ok:
        parts.append("sürücülər qrupuna")
    ckb = InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="🚫 Sifarişi ləğv et", callback_data=f"cx:{oid}")]]
    )
    await cb.message.edit_text(
        f"✅ Sifariş #{oid} {' və '.join(parts)} göndərildi. Sürücü qəbul edən kimi məlumat gələcək.",
        reply_markup=ckb,
    )
    await cb.answer()


@router.callback_query(F.data.startswith("cx:"))
async def customer_cancel(cb: CallbackQuery):
    oid = int(cb.data[3:])
    n, _ = execute(
        "UPDATE orders SET status='cancelled' WHERE id=? AND customer_id=? AND status='new'",
        (oid, cb.from_user.id),
    )
    if not n:
        await cb.answer("Sifariş artıq qəbul olunub və ya ləğv edilib.", show_alert=True)
        return
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    for r in fetchall("SELECT * FROM notifs WHERE order_id=?", (oid,)):
        try:
            await cb.bot.edit_message_text(
                order_text(o) + "\n\n🚫 Müştəri ləğv etdi",
                chat_id=r["chat_id"], message_id=r["msg_id"], reply_markup=None,
            )
        except Exception:
            logging.warning("edit failed for chat %s", r["chat_id"])
    await cb.message.edit_text(f"Sifariş #{oid} ləğv edildi.")
    await cb.answer()


# ---------- Sürücü: qəbul / imtina ----------
@router.callback_query(F.data.startswith("acc:"))
async def accept(cb: CallbackQuery):
    oid = int(cb.data[4:])
    d = fetch("SELECT * FROM drivers WHERE user_id=? AND approved=1", (cb.from_user.id,))
    if not d:
        await cb.answer("Siz təsdiqlənmiş sürücü deyilsiniz. Botda /driver yazıb qeydiyyatdan keçin.", show_alert=True)
        return
    n, _ = execute(
        "UPDATE orders SET status='accepted', driver_id=? WHERE id=? AND status='new'",
        (d["user_id"], oid),
    )
    if not n:
        await cb.answer("Bu sifariş artıq götürülüb və ya ləğv edilib.", show_alert=True)
        return
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))

    # Bütün bildiriş mesajlarını yenilə
    for r in fetchall("SELECT * FROM notifs WHERE order_id=?", (oid,)):
        if r["chat_id"] == GROUP_ID:
            text = order_text(o) + f"\n\n✅ Qəbul etdi: {esc(d['name'])} ({esc(d['plate'])})"
        elif r["driver_id"] == d["user_id"]:
            text = order_text(o) + "\n\n✅ Siz qəbul etdiniz"
        else:
            text = order_text(o) + "\n\n⛔ Sifariş başqa sürücü tərəfindən götürüldü"
        try:
            await cb.bot.edit_message_text(text, chat_id=r["chat_id"], message_id=r["msg_id"], reply_markup=None)
        except Exception:
            logging.warning("edit failed for chat %s", r["chat_id"])

    # müştəriyə sürücü məlumatı
    await cb.bot.send_message(
        o["customer_id"],
        "✅ <b>Sürücü tapıldı!</b>\n"
        f"👤 {esc(d['name'])}\n📞 {esc(d['phone'])}\n"
        f"🚗 {esc(d['car'])}\n🔢 {esc(d['plate'])}\n"
        f"💰 {o['price']:.1f} ₼",
    )
    # sürücüyə şəxsidə sifariş (Waze linkləri) və müştəri
    try:
        await cb.bot.send_message(
            d["user_id"],
            "✅ <b>Sifariş sizə verildi</b>\n\n"
            + order_text(o)
            + f"\n\nMüştəri: <a href=\"tg://user?id={o['customer_id']}\">{esc(o['customer_name'])}</a>",
        )
        await cb.answer("Qəbul etdiniz ✅")
    except Exception:
        await cb.answer("Qəbul etdiniz ✅. Məlumatı şəxsidə almaq üçün mənə botda /start yazın.", show_alert=True)


@router.callback_query(F.data.startswith("rej:"))
async def reject(cb: CallbackQuery):
    oid = int(cb.data[4:])
    o = fetch("SELECT * FROM orders WHERE id=?", (oid,))
    if cb.message.chat.id != GROUP_ID and o:
        # şəxsi çatda yalnız bu sürücünün mesajını bağla, sifariş digərləri üçün qalır
        try:
            await cb.message.edit_text(order_text(o) + "\n\n❌ İmtina etdiniz", reply_markup=None)
        except Exception:
            pass
    await cb.answer("İmtina etdiniz.")


# ---------- Sürücü: oflayn (onlayn olmaq üçün canlı yer paylaşmaq kifayətdir) ----------
@router.message(Command("oflayn", "offline"), F.chat.type == ChatType.PRIVATE)
async def go_offline(m: Message):
    execute("UPDATE drivers SET online=0 WHERE user_id=?", (m.from_user.id,))
    await m.answer(
        "🔴 Oflayn oldunuz. Sifarişlər gəlməyəcək.\n"
        "Telegram-da canlı yer paylaşımını da dayandırın. Yenidən işə başlamaq üçün canlı yer paylaşın."
    )


@router.message(Command("onlayn", "online"), F.chat.type == ChatType.PRIVATE)
async def go_online_help(m: Message):
    d = fetch("SELECT * FROM drivers WHERE user_id=? AND approved=1", (m.from_user.id,))
    if not d:
        await m.answer("Əvvəlcə /driver ilə qeydiyyatdan keçin və admin təsdiqini gözləyin.")
        return
    await m.answer(
        "İşə başlamaq üçün canlı yerinizi mənə göndərin:\n"
        "📎 → <b>Yer</b> (Location) → <b>Canlı yeri paylaş</b> → <b>Mən söndürənə qədər</b>.\n"
        "Paylaşım başlayan kimi avtomatik onlayn olacaqsınız."
    )


# ---------- Sürücü qeydiyyatı ----------
class Reg(StatesGroup):
    name = State()
    phone = State()
    car = State()
    plate = State()


@router.message(Command("driver"), F.chat.type == ChatType.PRIVATE)
async def driver_start(m: Message, state: FSMContext):
    await state.set_state(Reg.name)
    await m.answer("Sürücü qeydiyyatı. Ad və soyadınızı yazın:", reply_markup=ReplyKeyboardRemove())


@router.message(Reg.name, F.text)
async def reg_name(m: Message, state: FSMContext):
    await state.update_data(name=m.text.strip())
    await state.set_state(Reg.phone)
    await m.answer("Mobil nömrənizi yazın (məs. +994501234567):")


@router.message(Reg.phone, F.text)
async def reg_phone(m: Message, state: FSMContext):
    await state.update_data(phone=m.text.strip())
    await state.set_state(Reg.car)
    await m.answer("Maşın modeli və rəngi (məs. Hyundai Elantra, ağ):")


@router.message(Reg.car, F.text)
async def reg_car(m: Message, state: FSMContext):
    await state.update_data(car=m.text.strip())
    await state.set_state(Reg.plate)
    await m.answer("Dövlət nömrəsi (məs. 10-AA-123):")


@router.message(Reg.plate, F.text)
async def reg_plate(m: Message, state: FSMContext):
    data = await state.get_data()
    await state.clear()
    uid = m.from_user.id
    approved = 1 if uid == ADMIN_ID else 0
    execute(
        "INSERT INTO drivers(user_id,name,phone,car,plate,approved) VALUES(?,?,?,?,?,?) "
        "ON CONFLICT(user_id) DO UPDATE SET name=excluded.name, phone=excluded.phone, "
        "car=excluded.car, plate=excluded.plate, approved=excluded.approved",
        (uid, data["name"], data["phone"], data["car"], m.text.strip(), approved),
    )
    if approved:
        await m.answer("✅ Qeydiyyat tamamlandı, siz təsdiqlənmisiniz. İşə başlamaq üçün canlı yer paylaşın (/onlayn).")
        return
    await m.answer("Qeydiyyat göndərildi. Admin təsdiqləyəndən sonra canlı yer paylaşıb işə başlaya biləcəksiniz.")
    kb = InlineKeyboardMarkup(
        inline_keyboard=[[
            InlineKeyboardButton(text="✅ Təsdiq et", callback_data=f"appr:{uid}"),
            InlineKeyboardButton(text="🚫 Rədd et", callback_data=f"deny:{uid}"),
        ]]
    )
    await m.bot.send_message(
        ADMIN_ID,
        "🆕 <b>Yeni sürücü</b>\n"
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
    bot = Bot(
        BOT_TOKEN,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML, link_preview_is_disabled=True),
    )
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    await bot.delete_webhook(drop_pending_updates=True)
    await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())


if __name__ == "__main__":
    asyncio.run(main())
