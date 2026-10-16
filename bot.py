import asyncio
import html
import logging
import os
import sqlite3
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

# ---------- Tarif ----------
PER_KM = float(os.environ.get("PER_KM", "0.75"))
MIN_PRICE = float(os.environ.get("MIN_PRICE", "1.80"))
PEAK_MULT = float(os.environ.get("PEAK_MULT", "1.3"))
PEAK_HOURS = [(7 * 60 + 30, 10 * 60), (17 * 60, 20 * 60)]  # dəqiqə ilə
TZ = ZoneInfo("Asia/Baku")

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


def init_db():
    conn = sqlite3.connect(DB_PATH)
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS drivers(
            user_id INTEGER PRIMARY KEY,
            name TEXT, phone TEXT, car TEXT, plate TEXT,
            approved INTEGER DEFAULT 0
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
        """
    )
    conn.commit()
    conn.close()


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
    url = "https://api.openrouteservice.org/v2/directions/driving-car"
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


async def geocode(text: str):
    url = "https://api.openrouteservice.org/geocode/search"
    params = {
        "api_key": ORS_KEY,
        "text": f"{text}, Baku",
        "boundary.country": "AZ",
        "focus.point.lat": "40.4093",
        "focus.point.lon": "49.8671",
        "size": "1",
    }
    try:
        async with aiohttp.ClientSession() as s:
            async with s.get(url, params=params, timeout=aiohttp.ClientTimeout(total=20)) as r:
                data = await r.json()
        f = data["features"][0]
        lon, lat = f["geometry"]["coordinates"]
        return lat, lon, f["properties"].get("label", text)
    except Exception:
        return None


# ---------- Köməkçilər ----------
def esc(s) -> str:
    return html.escape(str(s or ""))


def maps(lat, lon) -> str:
    return f"https://www.google.com/maps?q={lat},{lon}"


def order_text(o) -> str:
    return (
        f"🚕 <b>Sifariş #{o['id']}</b>\n"
        f"📍 <a href=\"{maps(o['plat'], o['plon'])}\">Götürmə nöqtəsi</a>\n"
        f"🏁 <a href=\"{maps(o['dlat'], o['dlon'])}\">{esc(o['dest_label'])}</a>\n"
        f"🛣 {o['km']:.1f} km\n"
        f"💰 <b>{o['price']:.1f} ₼</b>"
    )


def start_kb():
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="📍 Yerimi göndər (taksi çağır)", request_location=True)]],
        resize_keyboard=True,
    )


# ---------- Müştəri ----------
@router.message(CommandStart(), F.chat.type == ChatType.PRIVATE)
async def start(m: Message, state: FSMContext):
    await state.clear()
    await m.answer(
        "Salam! 🚕 Taksi çağırmaq üçün aşağıdakı düyməyə basıb yerinizi göndərin.\n\n"
        "Sürücüsünüzsə: /driver",
        reply_markup=start_kb(),
    )


@router.message(Command("id"))
async def get_id(m: Message):
    await m.answer(f"Chat ID: <code>{m.chat.id}</code>")


@router.message(F.location, F.chat.type == ChatType.PRIVATE, StateFilter(None))
async def on_location(m: Message):
    uid = m.from_user.id
    p = pending.get(uid)
    loc = m.location
    if p is None or "dlat" in p:
        pending[uid] = {"plat": loc.latitude, "plon": loc.longitude}
        await m.answer(
            "Haraya gedəcəksiniz? Ünvanı yazın (məs. <i>28 Mall</i>) "
            "və ya 📎 → Yer vasitəsilə xəritədən nöqtə göndərin.",
            reply_markup=ReplyKeyboardRemove(),
        )
    else:
        await quote(m, p, loc.latitude, loc.longitude, "Xəritədən seçilmiş nöqtə")


@router.message(F.text, ~F.text.startswith("/"), F.chat.type == ChatType.PRIVATE, StateFilter(None))
async def on_text(m: Message):
    p = pending.get(m.from_user.id)
    if not p or "dlat" in p:
        await m.answer("Əvvəlcə yerinizi göndərin 👇", reply_markup=start_kb())
        return
    res = await geocode(m.text)
    if not res:
        await m.answer("Ünvan tapılmadı. Daha dəqiq yazın və ya xəritədən nöqtə göndərin.")
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
        f"🏁 Təyinat: {esc(label)}\n🛣 Məsafə: {km:.1f} km\n💰 Qiymət: <b>{price:.1f} ₼</b>{note}",
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
    gkb = InlineKeyboardMarkup(
        inline_keyboard=[[
            InlineKeyboardButton(text="✅ Qəbul et", callback_data=f"acc:{oid}"),
            InlineKeyboardButton(text="❌ İmtina", callback_data=f"rej:{oid}"),
        ]]
    )
    sent = await cb.bot.send_message(GROUP_ID, order_text(o), reply_markup=gkb)
    execute("UPDATE orders SET group_msg_id=? WHERE id=?", (sent.message_id, oid))
    ckb = InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="🚫 Sifarişi ləğv et", callback_data=f"cx:{oid}")]]
    )
    await cb.message.edit_text(
        f"✅ Sifariş #{oid} sürücülərə göndərildi. Sürücü qəbul edən kimi məlumat gələcək.",
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
    try:
        await cb.bot.edit_message_text(
            order_text(o) + "\n\n🚫 Müştəri ləğv etdi",
            chat_id=GROUP_ID, message_id=o["group_msg_id"], reply_markup=None,
        )
    except Exception:
        logging.exception("group edit failed")
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
    await cb.message.edit_text(
        order_text(o) + f"\n\n✅ Qəbul etdi: {esc(d['name'])} ({esc(d['plate'])})",
        reply_markup=None,
    )
    # müştəriyə sürücü məlumatı
    await cb.bot.send_message(
        o["customer_id"],
        "✅ <b>Sürücü tapıldı!</b>\n"
        f"👤 {esc(d['name'])}\n📞 {esc(d['phone'])}\n"
        f"🚗 {esc(d['car'])}\n🔢 {esc(d['plate'])}\n"
        f"💰 {o['price']:.1f} ₼",
    )
    # sürücüyə götürmə nöqtəsi
    try:
        await cb.bot.send_message(
            d["user_id"],
            f"Sifariş #{oid}. <a href=\"tg://user?id={o['customer_id']}\">{esc(o['customer_name'])}</a> "
            "sizi gözləyir. Götürmə nöqtəsi:",
        )
        await cb.bot.send_location(d["user_id"], o["plat"], o["plon"])
        await cb.answer("Qəbul etdiniz ✅")
    except Exception:
        await cb.answer("Qəbul etdiniz ✅. Məlumatı şəxsidə almaq üçün mənə botda /start yazın.", show_alert=True)


@router.callback_query(F.data.startswith("rej:"))
async def reject(cb: CallbackQuery):
    await cb.answer("İmtina etdiniz. Sifariş digər sürücülər üçün qalır.")


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
        await m.answer("✅ Qeydiyyat tamamlandı, siz təsdiqlənmisiniz.")
        return
    await m.answer("Qeydiyyat göndərildi. Admin təsdiqləyəndən sonra sifarişləri qəbul edə biləcəksiniz.")
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
        note = "✅ Qeydiyyatınız təsdiqləndi. Qrupdan sifarişləri qəbul edə bilərsiniz."
    else:
        execute("UPDATE drivers SET approved=0 WHERE user_id=?", (uid,))
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
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
