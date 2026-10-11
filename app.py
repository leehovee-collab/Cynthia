"""Cynthia's Homemade Teacakes - weekly pre-order web app."""

import hashlib
import hmac
import math
import os
import re
import secrets
import sqlite3
import threading
from datetime import date, datetime, timedelta
from urllib.parse import quote, quote_plus
from zoneinfo import ZoneInfo

import requests
from apscheduler.schedulers.background import BackgroundScheduler
from apscheduler.triggers.cron import CronTrigger
from dotenv import load_dotenv
from flask import Flask, abort, flash, g, redirect, render_template, request, session, url_for

load_dotenv()

# =============================================================================
#  SETTINGS - change products, prices, allergens, slots and the box cap here.
#  Save the file and restart the app for changes to show.
# =============================================================================

# Most boxes you will bake in one week (all products added together).
WEEKLY_BOX_CAP = 30

# Box sizes on offer (how many rolls or cookies in a box).
BOX_SIZES = [4, 6, 12]

# The most boxes of one product + size a customer can add in a single order.
MAX_BOXES_PER_CHOICE = 5

# Each product. "kind" must be "roll", "cookie" or "traybake" (used for the
# bake sheet; traybakes are counted in squares).
# "image" is optional: put a photo in the static/images folder and type its
# file name here, e.g. "image": "classic-roll.jpg". Leave it as "" for none.
# Prices are in pounds, one price per box size. THESE ARE PLACEHOLDERS.
# Allergens are PLACEHOLDERS too - check them against your real ingredients.
# If you ever replace a product, give the new one a new "id" so old orders
# aren't mixed up with it.
PRODUCTS = [
    {
        "id": "classic-roll",
        "name": "Classic Cinnamon Roll",
        "kind": "roll",
        "image": "",
        "description": "Soft, fluffy rolls with cinnamon sugar and cream cheese frosting.",
        "allergens": "Wheat (gluten), milk, egg",
        "prices": {4: 12.00, 6: 17.00, 12: 32.00},
    },
    {
        "id": "cookies-cream-traybake",
        "name": "Cookies & Cream Traybake",
        "kind": "traybake",
        "image": "",
        "description": "Soft vanilla traybake loaded with cookie pieces and a creamy topping.",
        "allergens": "Wheat (gluten), milk, egg, soya",
        "prices": {4: 14.00, 6: 20.00, 12: 38.00},
    },
    {
        "id": "nyc-cookie",
        "name": "NYC Chocolate Chip Cookie",
        "kind": "cookie",
        "image": "",
        "description": "Thick, gooey New York style cookies loaded with chocolate chips.",
        "allergens": "Wheat (gluten), milk, egg, soya",
        "prices": {4: 10.00, 6: 14.00, 12: 26.00},
    },
    {
        "id": "fudge-traybake",
        "name": "Fudge Traybake",
        "kind": "traybake",
        "image": "",
        "description": "Rich, soft traybake squares topped with a thick layer of fudge.",
        "allergens": "Wheat (gluten), milk, egg, soya",
        "prices": {4: 12.00, 6: 17.00, 12: 32.00},
    },
]

# Products no longer on sale. Old orders that contain them still show on the
# admin page and are counted under the right heading on the bake sheet.
RETIRED_PRODUCT_KINDS = {
    "biscoff-roll": "roll",
    "biscoff-cookie": "cookie",
}

# Shown under the menu.
ALLERGEN_NOTE = (
    "Everything is baked in a home kitchen that also handles nuts, peanuts and "
    "sesame, so we can't guarantee any product is free from traces."
)

# Friday collection slots customers can pick from.
COLLECTION_SLOTS = [
    "10:00 - 12:00",
    "12:00 - 14:00",
    "14:00 - 16:00",
    "16:00 - 18:00",
]

# Ordering window, UK time. 0 = Monday ... 6 = Sunday.
# Orders open at 00:00 on the first day and close at 23:59 on the last day.
ORDERS_OPEN_DAY = 0   # Monday
ORDERS_CLOSE_DAY = 2  # Wednesday
COLLECTION_DAY = 4    # Friday

# When the week's bake sheet is sent to Telegram, UK time.
BAKE_SHEET_DAY = "wed"  # mon, tue, wed, thu, fri, sat or sun
BAKE_SHEET_HOUR = 23
BAKE_SHEET_MINUTE = 59

# Order references look like CHT-0001.
REFERENCE_PREFIX = "CHT"

# =============================================================================
#  END OF SETTINGS
# =============================================================================

# Secrets and deployment options come from the .env file (or Railway variables).
ADMIN_KEY = os.getenv("ADMIN_KEY", "")
BANK_NAME = os.getenv("BANK_NAME", "")
SORT_CODE = os.getenv("SORT_CODE", "")
ACCOUNT_NUMBER = os.getenv("ACCOUNT_NUMBER", "")
# Telegram alerts are skipped if either of these is blank.
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "")

DB_PATH = os.getenv("DB_PATH") or "orders.db"
FORCE_OPEN = os.getenv("FORCE_OPEN", "").strip().lower() in ("1", "true", "yes", "on")


def env_number(name, default):
    """A number from .env; blank, missing or nonsense values fall back to the default."""
    try:
        return max(float(os.getenv(name, "").strip()), 0)
    except ValueError:
        return default


# Delivery. It is only offered when BAKERY_POSTCODE is filled in.
BAKERY_POSTCODE = os.getenv("BAKERY_POSTCODE", "").strip().upper()
MAX_DELIVERY_MILES = env_number("MAX_DELIVERY_MILES", 10)
DELIVERY_FEE_PENCE = int(round(env_number("DELIVERY_FEE", 0) * 100))
# Fuel cost is left out of alerts unless both of these are filled in.
CAR_MPG = env_number("CAR_MPG", 0)
FUEL_PRICE_PER_LITRE = env_number("FUEL_PRICE_PER_LITRE", 0)

LITRES_PER_GALLON = 4.546
METRES_PER_MILE = 1609.344

UK = ZoneInfo("Europe/London")
DAY_NAMES = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
KIND_LABELS = {"roll": "rolls", "cookie": "cookies", "traybake": "squares"}
PRODUCTS_BY_ID = {p["id"]: p for p in PRODUCTS}

app = Flask(__name__)
# Admin login cookies are signed with a key derived from ADMIN_KEY, so there is
# no extra secret to manage and changing ADMIN_KEY logs everyone out.
app.secret_key = (
    hashlib.sha256(("session:" + ADMIN_KEY).encode()).digest() if ADMIN_KEY else secrets.token_bytes(32)
)
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"


# ----------------------------------------------------------------------------
# Database
# ----------------------------------------------------------------------------

SCHEMA = """
CREATE TABLE IF NOT EXISTS orders (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    token       TEXT NOT NULL UNIQUE,
    week_start  TEXT NOT NULL,
    created_at  TEXT NOT NULL,
    name        TEXT NOT NULL,
    phone       TEXT NOT NULL,
    email       TEXT NOT NULL DEFAULT '',
    slot        TEXT NOT NULL,
    notes       TEXT NOT NULL DEFAULT '',
    total_pence INTEGER NOT NULL,
    paid        INTEGER NOT NULL DEFAULT 0,
    collected   INTEGER NOT NULL DEFAULT 0,
    cancelled   INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE IF NOT EXISTS order_items (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    order_id     INTEGER NOT NULL REFERENCES orders(id),
    product_id   TEXT NOT NULL,
    product_name TEXT NOT NULL,
    box_size     INTEGER NOT NULL,
    quantity     INTEGER NOT NULL,
    line_pence   INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS bake_sheets_sent (
    week_start TEXT PRIMARY KEY,
    sent_at    TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_orders_week ON orders(week_start);
CREATE INDEX IF NOT EXISTS idx_items_order ON order_items(order_id);
"""


ORDER_COLUMNS_ADDED_LATER = {
    "method": "TEXT NOT NULL DEFAULT 'collection'",  # 'collection' or 'delivery'
    "address1": "TEXT NOT NULL DEFAULT ''",
    "town": "TEXT NOT NULL DEFAULT ''",
    "postcode": "TEXT NOT NULL DEFAULT ''",
    "delivery_fee_pence": "INTEGER NOT NULL DEFAULT 0",  # already included in total_pence
    "distance_miles": "REAL",  # one way
    "distance_estimated": "INTEGER NOT NULL DEFAULT 0",
    "fuel_litres": "REAL",  # round trip
    "fuel_pence": "INTEGER",  # round trip
}


def connect_db():
    # isolation_level=None lets us control transactions ourselves (see place_order).
    db = sqlite3.connect(DB_PATH, timeout=10, isolation_level=None)
    db.row_factory = sqlite3.Row
    return db


def init_db():
    folder = os.path.dirname(DB_PATH)
    if folder:
        os.makedirs(folder, exist_ok=True)
    db = connect_db()
    db.executescript(SCHEMA)
    # Add any newer columns to an orders table made by an earlier version of the app.
    existing = {row["name"] for row in db.execute("PRAGMA table_info(orders)")}
    for name, definition in ORDER_COLUMNS_ADDED_LATER.items():
        if name not in existing:
            db.execute(f"ALTER TABLE orders ADD COLUMN {name} {definition}")
    db.close()


def get_db():
    if "db" not in g:
        g.db = connect_db()
    return g.db


@app.teardown_appcontext
def close_db(_error):
    db = g.pop("db", None)
    if db is not None:
        db.close()


init_db()


# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

def now_uk():
    return datetime.now(UK)


def current_week_start():
    """The Monday of the current week, UK time."""
    today = now_uk().date()
    return today - timedelta(days=today.weekday())


def orders_open():
    return FORCE_OPEN or ORDERS_OPEN_DAY <= now_uk().weekday() <= ORDERS_CLOSE_DAY


def ordering_week_start():
    """The Monday of the week that new orders belong to. Once this week's
    ordering has closed (Thursday onwards), that is next week."""
    week_start = current_week_start()
    if now_uk().weekday() > ORDERS_CLOSE_DAY:
        week_start += timedelta(days=7)
    return week_start


def collection_date(week_start):
    return week_start + timedelta(days=COLLECTION_DAY)


def boxes_sold(db, week_start):
    row = db.execute(
        "SELECT COALESCE(SUM(i.quantity), 0) FROM order_items i "
        "JOIN orders o ON o.id = i.order_id "
        "WHERE o.week_start = ? AND o.cancelled = 0",
        (week_start.isoformat(),),
    ).fetchone()
    return row[0]


def to_pence(pounds):
    return int(round(pounds * 100))


def reference(order_id):
    return f"{REFERENCE_PREFIX}-{order_id:04d}"


@app.template_filter("money")
def money(pence):
    return f"£{pence / 100:,.2f}"


@app.template_filter("nice_date")
def nice_date(d):
    if isinstance(d, str):
        d = date.fromisoformat(d)
    return f"{DAY_NAMES[d.weekday()]} {d.day} {d:%b}"


def full_address(order):
    return f"{order['address1']}, {order['town']}, {order['postcode']}"


def maps_link(order):
    return "https://www.google.com/maps/search/?api=1&query=" + quote_plus(full_address(order))


@app.context_processor
def shared_template_values():
    return {"reference": reference, "to_pence": to_pence, "full_address": full_address, "maps_link": maps_link}


def week_summary(db, week_start):
    """Everything about one week: its orders, the bake sheet and the money."""
    orders = db.execute(
        "SELECT * FROM orders WHERE week_start = ? ORDER BY id", (week_start.isoformat(),)
    ).fetchall()
    items = db.execute(
        "SELECT i.*, o.cancelled FROM order_items i JOIN orders o ON o.id = i.order_id "
        "WHERE o.week_start = ? ORDER BY i.id",
        (week_start.isoformat(),),
    ).fetchall()

    items_by_order = {}
    # Bake sheet: every product from the settings, plus any old product still on an order.
    bake = {
        p["id"]: {"name": p["name"], "kind": p["kind"], "boxes": {s: 0 for s in BOX_SIZES}, "pieces": 0}
        for p in PRODUCTS
    }
    for item in items:
        items_by_order.setdefault(item["order_id"], []).append(item)
        if item["cancelled"]:
            continue
        row = bake.setdefault(
            item["product_id"],
            {
                "name": item["product_name"],
                "kind": RETIRED_PRODUCT_KINDS.get(item["product_id"], ""),
                "boxes": {s: 0 for s in BOX_SIZES},
                "pieces": 0,
            },
        )
        row["boxes"][item["box_size"]] = row["boxes"].get(item["box_size"], 0) + item["quantity"]
        row["pieces"] += item["box_size"] * item["quantity"]

    active = [o for o in orders if not o["cancelled"]]
    deliveries = [o for o in active if o["method"] == "delivery"]
    fuel = [o["fuel_pence"] for o in deliveries]
    return {
        "orders": orders,
        "delivery_orders": [o for o in orders if o["method"] == "delivery"],
        "collection_orders": [o for o in orders if o["method"] != "delivery"],
        # Totals for the week's (not cancelled) deliveries, each counted as its own round trip.
        "delivery_miles": sum((o["distance_miles"] or 0) * 2 for o in deliveries),
        "fuel_pence": sum(fuel) if all(pence is not None for pence in fuel) else None,
        "items_by_order": items_by_order,
        "bake": list(bake.values()),
        "kind_totals": {
            label: sum(row["pieces"] for row in bake.values() if row["kind"] == kind)
            for kind, label in KIND_LABELS.items()
        },
        "boxes_sold": sum(sum(row["boxes"].values()) for row in bake.values()),
        "takings": sum(o["total_pence"] for o in active),
        "unpaid": sum(o["total_pence"] for o in active if not o["paid"]),
    }


# ----------------------------------------------------------------------------
# Delivery distance and fuel
# ----------------------------------------------------------------------------

class DeliveryProblem(Exception):
    """Delivery can't go ahead. The message is friendly and safe to show the customer."""


POSTCODE_PATTERN = re.compile(r"[A-Z]{1,2}\d[A-Z\d]? ?\d[A-Z]{2}")
LOOKUP_ERRORS = (requests.RequestException, ValueError, KeyError, TypeError)
WEB_HEADERS = {"User-Agent": "CynthiasHomemadeTeacakes-preorders"}
_bakery_location = None  # looked up once, then remembered while the app runs


def lookup_postcode(postcode):
    """Ask postcodes.io about a postcode. Returns (postcode, latitude, longitude),
    or None if it isn't a real postcode. Raises one of LOOKUP_ERRORS if the service is down."""
    response = requests.get(
        "https://api.postcodes.io/postcodes/" + quote(postcode), headers=WEB_HEADERS, timeout=8
    )
    if response.status_code == 404:
        return None
    response.raise_for_status()
    result = response.json()["result"]
    if result["latitude"] is None or result["longitude"] is None:
        return None
    return result["postcode"], result["latitude"], result["longitude"]


def straight_line_miles(start, end):
    """Distance as the crow flies between two (latitude, longitude) points."""
    lat1, lon1, lat2, lon2 = map(math.radians, (*start, *end))
    a = math.sin((lat2 - lat1) / 2) ** 2 + math.cos(lat1) * math.cos(lat2) * math.sin((lon2 - lon1) / 2) ** 2
    return 3958.8 * 2 * math.asin(math.sqrt(a))


def driving_miles(start, end):
    """One-way driving distance between two (latitude, longitude) points.
    Returns (miles, is_estimate). Falls back to straight line x 1.3 if OSRM can't answer."""
    try:
        response = requests.get(
            f"https://router.project-osrm.org/route/v1/driving/{start[1]},{start[0]};{end[1]},{end[0]}",
            params={"overview": "false"},
            headers=WEB_HEADERS,
            timeout=8,
        )
        data = response.json()
        if data["code"] == "Ok":
            return data["routes"][0]["distance"] / METRES_PER_MILE, False
    except (*LOOKUP_ERRORS, IndexError) as error:
        app.logger.warning("OSRM distance lookup failed (%s); using an estimate.", type(error).__name__)
    return straight_line_miles(start, end) * 1.3, True


def fuel_for(one_way_miles):
    """Round-trip (litres, cost in pence), or (None, None) if the car settings aren't filled in."""
    if CAR_MPG <= 0 or FUEL_PRICE_PER_LITRE <= 0:
        return None, None
    litres = one_way_miles * 2 / CAR_MPG * LITRES_PER_GALLON
    return litres, int(round(litres * FUEL_PRICE_PER_LITRE * 100))


def check_delivery(postcode):
    """Work out a delivery to this postcode, or raise DeliveryProblem."""
    global _bakery_location
    try:
        if _bakery_location is None:
            _bakery_location = lookup_postcode(BAKERY_POSTCODE)
            if _bakery_location is None:
                app.logger.error("BAKERY_POSTCODE isn't a postcode that postcodes.io recognises.")
                raise DeliveryProblem("Sorry, delivery isn't available right now. Collection is available.")
        customer = lookup_postcode(postcode)
    except LOOKUP_ERRORS as error:
        app.logger.warning("Postcode lookup failed (%s).", type(error).__name__)
        raise DeliveryProblem(
            "Sorry, we couldn't check your postcode just now. Please try again in a minute, or choose collection."
        ) from None
    if customer is None:
        raise DeliveryProblem("We couldn't find that postcode. Please check it and try again.")

    miles, estimated = driving_miles(_bakery_location[1:], customer[1:])
    if miles > MAX_DELIVERY_MILES:
        raise DeliveryProblem(
            f"Sorry, we don't deliver that far - you're about {miles:.0f} miles away and we deliver "
            f"up to {MAX_DELIVERY_MILES:g} miles. Collection is available, so please choose Collection instead."
        )
    litres, fuel_pence = fuel_for(miles)
    return {
        "postcode": customer[0],
        "miles": round(miles, 2),
        "estimated": int(estimated),
        "litres": litres,
        "fuel_pence": fuel_pence,
    }


# ----------------------------------------------------------------------------
# Telegram
# ----------------------------------------------------------------------------

def telegram_configured():
    return bool(TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID)


def split_message(text, limit=4000):
    """Telegram refuses messages over 4096 characters, so break long ones between lines."""
    chunks, current = [], ""
    for line in text.split("\n"):
        if current and len(current) + len(line) + 1 > limit:
            chunks.append(current)
            current = line
        else:
            current = f"{current}\n{line}" if current else line
    return chunks + [current]


def send_telegram(text):
    """Send a Telegram message. Returns (worked, detail) and never raises."""
    if not telegram_configured():
        return False, "Telegram isn't set up: TELEGRAM_BOT_TOKEN or TELEGRAM_CHAT_ID is blank."
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    for chunk in split_message(text):
        try:
            response = requests.post(url, json={"chat_id": TELEGRAM_CHAT_ID, "text": chunk}, timeout=10)
            body = response.json()
        except (requests.RequestException, ValueError) as error:
            # Only the error type is reported: the full error text includes the URL, which has the token in it.
            detail = f"Couldn't reach Telegram ({type(error).__name__})."
            app.logger.warning(detail)
            return False, detail
        if not body.get("ok"):
            detail = f"Telegram said: {body.get('description', response.status_code)}"
            app.logger.warning(detail)
            return False, detail
    return True, "Sent."


def order_alert_text(order, items):
    lines = [
        f"🧁 New order {reference(order['id'])}",
        f"{order['name']} · {order['phone']}",
    ]
    when = f"{nice_date(collection_date(date.fromisoformat(order['week_start'])))}, {order['slot']}"
    if order["method"] == "delivery":
        one_way = order["distance_miles"] or 0
        estimate = " (estimate)" if order["distance_estimated"] else ""
        lines += [
            f"🚗 DELIVERY: {when}",
            full_address(order),
            maps_link(order),
            f"Distance: {one_way:.1f} miles one way, {one_way * 2:.1f} miles round trip{estimate}",
        ]
        if order["fuel_pence"] is not None:
            lines.append(f"Fuel: {order['fuel_litres']:.2f} litres, {money(order['fuel_pence'])}")
    else:
        lines.append(f"Collection: {when}")
    lines.append("")
    for item in items:
        lines.append(
            f"{item['quantity']} × {item['product_name']} (box of {item['box_size']}) - {money(item['line_pence'])}"
        )
    if order["delivery_fee_pence"]:
        lines.append(f"Delivery fee - {money(order['delivery_fee_pence'])}")
    lines += ["", f"Total: {money(order['total_pence'])}"]
    if order["notes"]:
        lines.append(f"Notes: {order['notes']}")
    return "\n".join(lines)


def bake_sheet_text(db, week_start):
    summary = week_summary(db, week_start)
    lines = [f"📋 Bake sheet · collection {nice_date(collection_date(week_start))}", ""]

    active = [o for o in summary["orders"] if not o["cancelled"]]
    if not active:
        return "\n".join(lines + ["No orders this week."])

    lines.append("TO BAKE")
    for row in summary["bake"]:
        if row["pieces"]:
            boxes = ", ".join(f"{count} × box of {size}" for size, count in row["boxes"].items() if count)
            lines.append(f"{row['name']}: {row['pieces']} {KIND_LABELS.get(row['kind'], 'items')} ({boxes})")
    lines += [
        "Total: " + ", ".join(f"{pieces} {label}" for label, pieces in summary["kind_totals"].items()),
        "",
        f"Boxes: {summary['boxes_sold']} of {WEEKLY_BOX_CAP}",
        f"Money: {money(summary['takings'])} ({money(summary['unpaid'])} not yet paid)",
    ]

    def order_line(order):
        paid = "PAID" if order["paid"] else "NOT PAID"
        return f"{reference(order['id'])} · {order['name']} · {order['slot']} · {paid}"

    deliveries = [o for o in active if o["method"] == "delivery"]
    collections = [o for o in active if o["method"] != "delivery"]
    lines += ["", f"DELIVERIES ({len(deliveries)})"]
    for order in deliveries:
        lines.append(order_line(order))
        lines.append(f"   {full_address(order)} · {(order['distance_miles'] or 0) * 2:.1f} miles round trip")
    if deliveries:
        fuel = money(summary["fuel_pence"]) if summary["fuel_pence"] is not None else "not worked out"
        lines.append(f"Delivery total: {summary['delivery_miles']:.1f} miles, fuel {fuel}")
    lines += ["", f"COLLECTIONS ({len(collections)})"]
    lines += [order_line(order) for order in collections]
    return "\n".join(lines)


def scheduled_bake_sheet():
    """The automatic weekly send. Goes out at most once per week, even across restarts."""
    week_start = current_week_start()
    db = connect_db()
    try:
        # Claim this week in the database first; if the row is already there, it has been sent.
        claimed = db.execute(
            "INSERT OR IGNORE INTO bake_sheets_sent (week_start, sent_at) VALUES (?, ?)",
            (week_start.isoformat(), now_uk().isoformat(timespec="seconds")),
        ).rowcount
        if not claimed:
            return
        ok, _detail = send_telegram(bake_sheet_text(db, week_start))
        if not ok:
            db.execute("DELETE FROM bake_sheets_sent WHERE week_start = ?", (week_start.isoformat(),))
    finally:
        db.close()


# ----------------------------------------------------------------------------
# Customer pages
# ----------------------------------------------------------------------------

def render_order_page(errors=None, form=None):
    week_start = ordering_week_start()
    is_open = orders_open()
    # The next week customers can order for: the coming one if we're closed,
    # or the one after if this one is open but sold out.
    next_week = week_start + timedelta(days=7) if is_open else week_start
    # A photo is only used if the file is really there; otherwise the card shows a placeholder.
    images = {
        p["id"]: url_for("static", filename="images/" + p["image"])
        for p in PRODUCTS
        if p.get("image") and os.path.isfile(os.path.join(app.static_folder, "images", p["image"]))
    }
    return render_template(
        "index.html",
        images=images,
        is_open=is_open,
        boxes_left=max(WEEKLY_BOX_CAP - boxes_sold(get_db(), week_start), 0),
        products=PRODUCTS,
        box_sizes=BOX_SIZES,
        slots=COLLECTION_SLOTS,
        max_per_choice=MAX_BOXES_PER_CHOICE,
        allergen_note=ALLERGEN_NOTE,
        collection=collection_date(week_start),
        next_open=next_week + timedelta(days=ORDERS_OPEN_DAY),
        next_collection=collection_date(next_week),
        close_day=DAY_NAMES[ORDERS_CLOSE_DAY],
        delivery_available=bool(BAKERY_POSTCODE),
        delivery_fee_pence=DELIVERY_FEE_PENCE,
        max_delivery_miles=f"{MAX_DELIVERY_MILES:g}",
        errors=errors or [],
        form=form or {},
    )


@app.get("/")
def index():
    return render_order_page()


@app.post("/order")
def place_order():
    if not orders_open():
        return redirect(url_for("index"))

    form = request.form
    errors = []

    # What they want to order. Prices always come from the settings, never the browser.
    lines = []
    for product in PRODUCTS:
        for size in BOX_SIZES:
            raw = form.get(f"qty_{product['id']}_{size}", "").strip() or "0"
            try:
                quantity = int(raw)
            except ValueError:
                quantity = -1
            if not 0 <= quantity <= MAX_BOXES_PER_CHOICE:
                errors.append(f"Please choose between 0 and {MAX_BOXES_PER_CHOICE} boxes for each option.")
                break
            if quantity:
                lines.append({
                    "product_id": product["id"],
                    "product_name": product["name"],
                    "box_size": size,
                    "quantity": quantity,
                    "line_pence": to_pence(product["prices"][size]) * quantity,
                })
    total_boxes = sum(line["quantity"] for line in lines)
    if not errors and total_boxes == 0:
        errors.append("Please add at least one box to your order.")

    # Who they are.
    name = form.get("name", "").strip()
    phone = form.get("phone", "").strip()
    email = form.get("email", "").strip()
    slot = form.get("slot", "")
    notes = form.get("notes", "").strip()

    if not name or len(name) > 80:
        errors.append("Please enter your name.")
    if len(re.sub(r"\D", "", phone)) < 7 or len(phone) > 30 or not re.fullmatch(r"[\d\s()+-]+", phone):
        errors.append("Please enter a valid phone number.")
    if email and (len(email) > 120 or not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email)):
        errors.append("That email address doesn't look right. You can leave it blank.")
    if slot not in COLLECTION_SLOTS:
        errors.append("Please choose a collection slot.")
    if len(notes) > 500:
        errors.append("Please keep notes under 500 characters.")

    # Collection or delivery.
    method = form.get("method", "collection")
    address1 = form.get("address1", "").strip()
    town = form.get("town", "").strip()
    postcode = " ".join(form.get("postcode", "").upper().split())
    delivery = {"postcode": "", "miles": None, "estimated": 0, "litres": None, "fuel_pence": None}
    fee_pence = 0
    if method == "delivery" and BAKERY_POSTCODE:
        if not address1 or len(address1) > 100:
            errors.append("Please enter the first line of your delivery address.")
        if not town or len(town) > 60:
            errors.append("Please enter your town.")
        if not POSTCODE_PATTERN.fullmatch(postcode):
            errors.append("Please enter a valid UK postcode for delivery.")
        # Only look the postcode up once everything else on the form is right.
        if not errors:
            try:
                delivery = check_delivery(postcode)
                fee_pence = DELIVERY_FEE_PENCE
            except DeliveryProblem as problem:
                errors.append(str(problem))
    elif method != "collection":
        errors.append("Please choose collection or delivery.")
    else:
        address1 = town = ""

    if errors:
        return render_order_page(errors, form)

    # Check the cap and save in one locked step, so two people ordering at the
    # same moment can't both take the last box.
    db = get_db()
    week_start = ordering_week_start()
    db.execute("BEGIN IMMEDIATE")
    try:
        left = WEEKLY_BOX_CAP - boxes_sold(db, week_start)
        if total_boxes > left:
            db.execute("ROLLBACK")
            if left <= 0:
                return redirect(url_for("index"))
            plural = "box" if left == 1 else "boxes"
            return render_order_page(
                [f"Sorry, only {left} {plural} left this week. Please reduce your order."], form
            )
        token = secrets.token_urlsafe(16)
        cursor = db.execute(
            "INSERT INTO orders (token, week_start, created_at, name, phone, email, slot, notes, total_pence, "
            "method, address1, town, postcode, delivery_fee_pence, distance_miles, distance_estimated, "
            "fuel_litres, fuel_pence) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                token,
                week_start.isoformat(),
                now_uk().isoformat(timespec="seconds"),
                name,
                phone,
                email,
                slot,
                notes,
                sum(line["line_pence"] for line in lines) + fee_pence,
                method,
                address1,
                town,
                delivery["postcode"],
                fee_pence,
                delivery["miles"],
                delivery["estimated"],
                delivery["litres"],
                delivery["fuel_pence"],
            ),
        )
        db.executemany(
            "INSERT INTO order_items (order_id, product_id, product_name, box_size, quantity, line_pence) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            [
                (cursor.lastrowid, l["product_id"], l["product_name"], l["box_size"], l["quantity"], l["line_pence"])
                for l in lines
            ],
        )
        db.execute("COMMIT")
    except Exception:
        if db.in_transaction:
            db.execute("ROLLBACK")
        raise

    # Tell the baker. Sent in the background so the customer never waits on Telegram.
    if telegram_configured():
        order = db.execute("SELECT * FROM orders WHERE token = ?", (token,)).fetchone()
        items = db.execute("SELECT * FROM order_items WHERE order_id = ? ORDER BY id", (order["id"],)).fetchall()
        threading.Thread(target=send_telegram, args=(order_alert_text(order, items),), daemon=True).start()

    return redirect(url_for("thanks", token=token))


@app.get("/thanks/<token>")
def thanks(token):
    db = get_db()
    order = db.execute("SELECT * FROM orders WHERE token = ?", (token,)).fetchone()
    if order is None:
        abort(404)
    items = db.execute("SELECT * FROM order_items WHERE order_id = ? ORDER BY id", (order["id"],)).fetchall()
    return render_template(
        "thanks.html",
        order=order,
        items=items,
        collection=collection_date(date.fromisoformat(order["week_start"])),
        bank_name=BANK_NAME,
        sort_code=SORT_CODE,
        account_number=ACCOUNT_NUMBER,
    )


# ----------------------------------------------------------------------------
# Admin
# ----------------------------------------------------------------------------

def is_admin():
    return bool(ADMIN_KEY) and session.get("admin") is True


@app.get("/admin")
def admin():
    if not is_admin():
        return render_template("admin_login.html", configured=bool(ADMIN_KEY), wrong=False)

    this_week = current_week_start()
    try:
        week_start = date.fromisoformat(request.args.get("week", ""))
        week_start -= timedelta(days=week_start.weekday())
    except ValueError:
        week_start = this_week

    # From Thursday, new orders (only possible with FORCE_OPEN) go into next week.
    upcoming = ordering_week_start()
    upcoming_orders = 0
    if upcoming != this_week:
        upcoming_orders = get_db().execute(
            "SELECT COUNT(*) FROM orders WHERE week_start = ?", (upcoming.isoformat(),)
        ).fetchone()[0]

    return render_template(
        "admin.html",
        upcoming_orders=upcoming_orders,
        week_start=week_start,
        is_this_week=week_start == this_week,
        prev_week=week_start - timedelta(days=7),
        next_week=week_start + timedelta(days=7),
        collection=collection_date(week_start),
        box_sizes=BOX_SIZES,
        cap=WEEKLY_BOX_CAP,
        telegram_ready=telegram_configured(),
        **week_summary(get_db(), week_start),
    )


@app.post("/admin/bake-sheet/send")
def admin_send_bake_sheet():
    if not is_admin():
        abort(403)
    try:
        week_start = date.fromisoformat(request.form.get("week", ""))
    except ValueError:
        week_start = current_week_start()
    # A manual send never counts as the automatic weekly one.
    ok, detail = send_telegram(bake_sheet_text(get_db(), week_start))
    flash("Bake sheet sent to Telegram." if ok else f"Bake sheet not sent. {detail}")
    return redirect(url_for("admin", week=week_start.isoformat()))


@app.post("/admin/login")
def admin_login():
    key = request.form.get("key", "")
    if ADMIN_KEY and hmac.compare_digest(key.encode(), ADMIN_KEY.encode()):
        session["admin"] = True
        return redirect(url_for("admin"))
    return render_template("admin_login.html", configured=bool(ADMIN_KEY), wrong=True), 403


@app.post("/admin/logout")
def admin_logout():
    session.clear()
    return redirect(url_for("admin"))


@app.post("/admin/order/<int:order_id>/<action>")
def admin_update(order_id, action):
    if not is_admin():
        abort(403)
    if action not in ("paid", "collected", "cancelled"):
        abort(404)
    # Each button flips its flag, so a mis-tap can be undone by tapping again.
    get_db().execute(f"UPDATE orders SET {action} = 1 - {action} WHERE id = ?", (order_id,))
    return redirect(url_for("admin", week=request.form.get("week", "")) + f"#order-{order_id}")


# ----------------------------------------------------------------------------
# Weekly bake sheet timer
# ----------------------------------------------------------------------------

# This runs inside the app, so the app must run as ONE process (see Procfile).
if telegram_configured():
    scheduler = BackgroundScheduler(timezone=UK)
    scheduler.add_job(
        scheduled_bake_sheet,
        CronTrigger(day_of_week=BAKE_SHEET_DAY, hour=BAKE_SHEET_HOUR, minute=BAKE_SHEET_MINUTE, timezone=UK),
        misfire_grace_time=3600,
        coalesce=True,
    )
    scheduler.start()


if __name__ == "__main__":
    # For running on your own computer. Railway uses gunicorn (see Procfile).
    app.run(host="127.0.0.1", port=5000)
