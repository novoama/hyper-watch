#!/usr/bin/env python3
"""
Hyper Watch: on every run it prices EVERY day in a travel window (not a sample),
from all your home airports to all the destination airports at once, any airline,
and emails you when a fare is exceptionally cheap.

Settings live in hyperwatch.toml. GitHub Actions runs this on a schedule
(.github/workflows/hyperwatch.yml). What it has seen so far is saved on the
repo's "hyperwatch-data" branch: state.json (its memory) and latest.md (a
readable price table you can open on GitHub).

A day is a steal when ANY of these is true:
  1. the one-way out is at or under steal_one_way
  2. out + back (two one-ways) is at or under steal_round_trip
  3. it is under_60_day_low_percent below the lowest price Google has recorded
     for that exact day over the previous 60 days
  4. it drops sudden_drop_percent below what that same day cost over the last
     day or so, to a price lower than 3 out of 4 days in the past two months

  python hyperwatch.py             normal run
  python hyperwatch.py --dry-run   search and print only; no email, nothing saved
"""
from __future__ import annotations

import argparse
import base64
import json
import os
import random
import smtplib
import statistics
import sys
import time
import tomllib
import traceback
import urllib.error
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta, timezone
from email.message import EmailMessage
from email.utils import formataddr
from html import escape
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path(__file__).resolve().parent
CONFIG_PATH = ROOT / "hyperwatch.toml"
DATA_DIR = ROOT / "hyperwatch_data"  # lives on the hyperwatch-data branch, not on main
STATE_PATH = DATA_DIR / "state.json"
LATEST_PATH = DATA_DIR / "latest.md"
WORKFLOW_FILE = "hyperwatch.yml"
URL = "https://www.google.com/travel/flights"

SETTINGS_DEFAULTS = {
    "workers": 6,              # searches running at once
    "tries": 7,                # Google withholds results on about 4 in 10 loads; retrying fixes it
    "budget_seconds": 24,      # stop starting searches after this, so a run stays under a minute
    "out_every_minutes": 0,    # trips out are re-priced this often (0 = every run)
    "back_every_minutes": 90,  # trips home are re-priced this often
    "max_searches_per_run": 0, # at most this many searches per run, stalest first (0 = no limit)
    "monthly_run_cap": 0,      # pause after this many runs in a month (0 = no limit)
    "timezone": "America/New_York",
}
WATCH_DEFAULTS = {
    "nights": [2, 10],
    "max_stops": 1,
    "max_hours": 12,
    "steal_one_way": None,
    "steal_round_trip": None,
    "under_60_day_low_percent": 10,
    "sudden_drop_percent": 35,
    "depart_days": [],        # e.g. ["Thu", "Fri", "Sat"]; empty = any day
    "return_days": [],
    "active_from": None,      # this watch only runs from / until these dates (your local dates)
    "active_until": None,
    "summary_at": [],         # send a "where prices stand" email at these times, e.g. ["2026-11-19 18:00"]
    "note": "",               # a line of your own that goes at the top of its emails
}
WATCH_REQUIRED = ("name", "origins", "destinations", "depart_between", "return_between")
AIRPORT_NAMES = {
    "EWR": "Newark", "JFK": "JFK", "LGA": "LaGuardia", "HPN": "Westchester", "SWF": "Stewart",
    "ISP": "Islip", "TTN": "Trenton", "ACY": "Atlantic City", "PHL": "Philadelphia",
    "SJU": "San Juan", "BQN": "Aguadilla", "PSE": "Ponce",
}
WEEKDAYS = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
HISTORY_HOURS = 96      # hourly price memory per day, for the sudden-drop rule
DROP_WINDOW_HOURS = 36
DROP_MIN_POINTS = 4
DROP_MIN_DOLLARS = 25
FRESH_HOURS = 6         # only act on prices seen this recently
BASELINE_HOURS = 20     # how often each day's 60-day price history is re-read
MAX_CARDS = 6


# ───────────────────────────── config ─────────────────────────────

class ConfigError(Exception):
    """Something in hyperwatch.toml needs fixing (the message says what)."""


def _num(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool)


def _airports(value, where):
    if not (isinstance(value, list) and value):
        raise ConfigError(f'{where} should be a list like ["EWR", "JFK"]')
    out = []
    for a in value:
        code = str(a).strip().upper()
        if not (len(code) == 3 and code.isalpha()):
            raise ConfigError(f'{where}: "{a}" isn\'t a 3-letter airport code')
        out.append(code)
    if len(out) > 7:
        raise ConfigError(f"{where}: Google Flights takes at most 7 airports at once")
    return out


def _window(value, where):
    if not (isinstance(value, list) and len(value) == 2):
        raise ConfigError(f'{where} should look like ["2026-12-01", "2026-12-31"]')
    try:
        start, end = (v if isinstance(v, date) else date.fromisoformat(str(v).strip()) for v in value)
    except ValueError:
        raise ConfigError(f'{where}: dates should look like "2026-12-01"') from None
    if end < start:
        raise ConfigError(f"{where}: the end date is before the start date")
    return start, end


def _one_date(value, where):
    try:
        return value if isinstance(value, date) and not isinstance(value, datetime) else date.fromisoformat(str(value).strip())
    except ValueError:
        raise ConfigError(f'{where} should be a date like "2026-11-20"') from None


def _weekdays(value, where):
    if not isinstance(value, list):
        raise ConfigError(f'{where} should be a list like ["Thu", "Fri", "Sat"]')
    out = []
    for item in value:
        short = str(item).strip()[:3].title()
        if short not in WEEKDAYS:
            raise ConfigError(f'{where}: "{item}" isn\'t a weekday (use Mon, Tue ... Sun)')
        out.append(short)
    return out


def _moments(value, where, tz):
    if not isinstance(value, list):
        raise ConfigError(f'{where} should be a list like ["2026-11-19 18:00"]')
    out = []
    for item in value:
        try:
            out.append(datetime.strptime(str(item).strip(), "%Y-%m-%d %H:%M").replace(tzinfo=tz))
        except ValueError:
            raise ConfigError(f'{where}: "{item}" should look like "2026-11-19 18:00"') from None
    return out


def slug(text):
    return "-".join("".join(c if c.isalnum() else " " for c in text.lower()).split())


def load_config(path=None):
    path = path or CONFIG_PATH
    try:
        with open(path, "rb") as f:
            raw = tomllib.load(f)
    except FileNotFoundError:
        raise ConfigError(f"can't find {path.name}") from None
    except tomllib.TOMLDecodeError as e:
        raise ConfigError(f"typo in {path.name}: {e}. Check that line for a missing quote, "
                          f"bracket, or comma.") from None

    user = raw.get("settings", {})
    unknown = sorted(set(user) - set(SETTINGS_DEFAULTS))
    if unknown:
        raise ConfigError(f"[settings] has unknown option(s): {', '.join(unknown)} (typo?)")
    settings = {**SETTINGS_DEFAULTS, **user}
    for key in ("workers", "tries", "budget_seconds", "back_every_minutes"):
        if not (_num(settings[key]) and settings[key] >= 1):
            raise ConfigError(f"[settings] {key} should be a number, 1 or more")
    for key in ("out_every_minutes", "max_searches_per_run", "monthly_run_cap"):
        if not (_num(settings[key]) and settings[key] >= 0):
            raise ConfigError(f"[settings] {key} should be a number, 0 or more")
    try:
        settings["tz"] = ZoneInfo(str(settings["timezone"]))
    except Exception:
        raise ConfigError(f'[settings] timezone "{settings["timezone"]}" isn\'t one I know') from None

    watches = []
    for n, w in enumerate(raw.get("watch", []), 1):
        where = f"Watch #{n}" + (f' "{w["name"]}"' if w.get("name") else "")
        unknown = sorted(set(w) - set(WATCH_DEFAULTS) - set(WATCH_REQUIRED))
        if unknown:
            raise ConfigError(f"{where} has unknown option(s): {', '.join(unknown)} (typo?)")
        missing = [k for k in WATCH_REQUIRED if k not in w]
        if missing:
            raise ConfigError(f"{where} is missing: {', '.join(missing)}")
        watch = {**WATCH_DEFAULTS, **w}
        watch["id"] = slug(str(w["name"]))
        if not watch["id"]:
            raise ConfigError(f"{where} needs a name")
        watch["origins"] = _airports(w["origins"], f"{where} origins")
        watch["destinations"] = _airports(w["destinations"], f"{where} destinations")
        watch["depart"] = _window(w["depart_between"], f"{where} depart_between")
        watch["back"] = _window(w["return_between"], f"{where} return_between")
        nights = watch["nights"]
        if not (isinstance(nights, list) and len(nights) == 2 and all(_num(x) for x in nights)
                and 1 <= nights[0] <= nights[1]):
            raise ConfigError(f"{where} nights should look like [2, 10]")
        for key in ("steal_one_way", "steal_round_trip"):
            if watch[key] is not None and not (_num(watch[key]) and watch[key] > 0):
                raise ConfigError(f"{where} {key} should be a dollar amount like 75")
        for key in ("under_60_day_low_percent", "sudden_drop_percent"):
            if not (_num(watch[key]) and 0 < watch[key] < 100):
                raise ConfigError(f"{where} {key} should be between 1 and 99")
        if not (_num(watch["max_stops"]) and watch["max_stops"] in (0, 1, 2)):
            raise ConfigError(f"{where} max_stops should be 0 (nonstop only), 1, or 2")
        if not (_num(watch["max_hours"]) and watch["max_hours"] > 0):
            raise ConfigError(f"{where} max_hours should be a number of hours like 12")
        watch["depart_days"] = _weekdays(watch["depart_days"], f"{where} depart_days")
        watch["return_days"] = _weekdays(watch["return_days"], f"{where} return_days")
        for key in ("active_from", "active_until"):
            if watch[key] is not None:
                watch[key] = _one_date(watch[key], f"{where} {key}")
        if watch["active_from"] and watch["active_until"] and watch["active_until"] < watch["active_from"]:
            raise ConfigError(f"{where}: active_until is before active_from")
        watch["summary_at"] = _moments(watch["summary_at"], f"{where} summary_at", settings["tz"])
        watch["note"] = str(watch["note"]).strip()
        if watch["id"] in {x["id"] for x in watches}:
            raise ConfigError(f'two watches are named "{w["name"]}"')
        watches.append(watch)
    if not watches:
        raise ConfigError("no [[watch]] block yet")
    return settings, watches


# ─────────────────────── asking Google Flights ───────────────────────
# One search = one page load. The search itself travels in the "tfs" address
# parameter, a small protobuf message. Building it by hand lets one search cover
# several origin AND destination airports at once (the fast-flights library sends
# one of each), and reading the page ourselves picks up both of Google's result
# lists. Google's 60-day price history for a day only comes with a plain search of
# one airport pair, so that is read separately (see refresh_baselines).

def _varint(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        out.append(b | 0x80 if n else b)
        if not n:
            return bytes(out)


def _bytes_field(field, payload):
    return _varint((field << 3) | 2) + _varint(len(payload)) + payload


def _int_field(field, value):
    return _varint(field << 3) + _varint(value)


def one_way_tfs(day, origins, destinations, max_stops=None, hide_self_transfer=True):
    """The tfs value for: one adult, economy, one way on `day`."""
    leg = _bytes_field(2, day.isoformat().encode())
    if max_stops is not None:
        leg += _int_field(5, int(max_stops))
    leg += b"".join(_bytes_field(13, _bytes_field(2, a.encode())) for a in origins)
    leg += b"".join(_bytes_field(14, _bytes_field(2, a.encode())) for a in destinations)
    body = _bytes_field(3, leg)
    body += _bytes_field(8, bytes([1]))  # one adult
    body += _int_field(9, 1)             # economy
    if hide_self_transfer:
        body += _int_field(17, 1)        # hide separate-ticket / self-transfer trips
    body += _int_field(19, 2)            # one way
    return base64.b64encode(body).decode()


def search_url(day, origin, destination, max_stops=None):
    return f"{URL}/search?tfs={one_way_tfs(day, [origin], [destination], max_stops)}&hl=en&curr=USD"


class Withheld(Exception):
    """Google answered but left the results out (it does this to a share of automated loads)."""


def parse_page(html):
    from selectolax.lexbor import LexborHTMLParser

    node = LexborHTMLParser(html).css_first(r"script.ds\:1")
    if node is None:
        raise Withheld("the page had no results block")
    js = node.text()
    if "data:" not in js:
        raise Withheld("the results block was empty")
    data = js.split("data:", 1)[1].rsplit(",", 1)[0]
    if data.endswith("errorHasStatus: true"):
        raise Withheld("Google withheld the results")
    return json.loads(data)


def fetch_payload(tfs):
    from primp import Client

    client = Client(impersonate="chrome_145", impersonate_os="macos", referer=True, cookie_store=True)
    res = client.get(URL, params={"tfs": tfs, "hl": "en-US", "curr": "USD"})
    return parse_page(res.text)


def _hm(value):
    """Google drops zero parts of a time: [7] is 7:00, [None, 36] is 0:36."""
    padded = [*(value or []), None, None]
    return padded[0] or 0, padded[1] or 0


def options(payload):
    """Every priced itinerary on the page: Google's "best" list (2) and "other" list (3)."""
    found = []
    for idx in (2, 3):
        try:
            block = payload[idx][0] or []
        except (IndexError, TypeError):
            continue
        for item in block:
            try:
                flight, price = item[0], item[1][0][1]
                legs = flight[2]
                if not (isinstance(price, (int, float)) and 15 <= price < 20000 and legs):
                    continue
                minutes = flight[9] if isinstance(flight[9], int) else sum(l[11] for l in legs)
                found.append({
                    "price": int(round(price)),
                    "airlines": list(dict.fromkeys(flight[1] or [])),
                    "origin": legs[0][3],
                    "destination": legs[-1][6],
                    "via": [l[6] for l in legs[:-1]],
                    "stops": len(legs) - 1,
                    "minutes": minutes,
                    "leaves": list(_hm(legs[0][8])),
                    "lands": list(_hm(legs[-1][10])),
                    "next_day": tuple(legs[-1][21]) != tuple(legs[0][20]),
                })
            except Exception:  # one odd row shouldn't sink the page
                continue
    return found


def price_history(payload):
    """Google's own record of this search's lowest price on each of the previous 60 days.
    It only comes with a plain search of ONE airport pair, so it's read separately."""
    try:
        box = payload[5]
        series = box[10][0]
        prices = sorted(p for _, p in series[:-1] if isinstance(p, (int, float)) and p > 0)  # last point = today
        if len(prices) < 20:
            return None
        usual = box[2][1] if isinstance(box[2], list) and len(box[2]) > 1 else None
        return {"low": int(prices[0]), "p25": int(prices[len(prices) // 4]),
                "median": int(statistics.median(prices)), "days": len(prices),
                "usual": int(usual) if isinstance(usual, (int, float)) and usual > 0 else None}
    except Exception:
        return None


def summarize(payload, watch, direction):
    """The cheapest sensible itinerary, the cheapest nonstop, and the cheapest into the main airport."""
    allowed = [o for o in options(payload)
               if o["stops"] <= watch["max_stops"] and o["minutes"] <= watch["max_hours"] * 60]
    rank = lambda o: (o["price"], o["stops"], o["minutes"])  # noqa: E731
    best = min(allowed, key=rank, default=None)
    nonstop = min((o for o in allowed if o["stops"] == 0), key=rank, default=None)
    end = "destination" if direction == "out" else "origin"  # the far-away end of the trip
    main = min((o for o in allowed if o[end] == watch["destinations"][0]), key=rank, default=None)
    return {"best": best, "nonstop": nonstop["price"] if nonstop else None,
            "main": main["price"] if main else None}


def load_one(tfs, tries, fetch, deadline=None):
    """-> (payload or None, the problem if it never loaded)"""
    problem = None
    for attempt in range(1, int(tries) + 1):
        if deadline is not None and time.monotonic() > deadline:
            return None, problem or "ran out of time this run"
        try:
            return fetch(tfs), None
        except Withheld as e:
            problem = str(e)
        except Exception as e:  # network hiccup, layout change, ...
            problem = f"{type(e).__name__}: {str(e)[:120]}"
        time.sleep(random.uniform(0.15, 0.4) * attempt)
    return None, problem


def sweep(tasks, watch, settings, fetch, deadline):
    """Run every (direction, day) search, a few at a time. -> [(task, summary|None, problem|None)]"""

    def one(task):
        direction, day = task
        a, b = watch["origins"], watch["destinations"]
        pair = (a, b) if direction == "out" else (b, a)
        payload, problem = load_one(one_way_tfs(day, *pair, watch["max_stops"]),
                                    settings["tries"], fetch, deadline)
        if payload is None:
            return task, None, problem
        try:
            return task, summarize(payload, watch, direction), None
        except Exception as e:
            return task, None, f"couldn't read the page ({type(e).__name__}: {str(e)[:80]})"

    with ThreadPoolExecutor(max_workers=int(settings["workers"])) as pool:
        return list(pool.map(one, tasks))


# ───────────────────────── memory (state.json) ─────────────────────────

def utc_now():
    return datetime.now(timezone.utc).replace(microsecond=0)


def iso(dt):
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def parse_iso(stamp):
    try:
        return datetime.fromisoformat(str(stamp).replace("Z", "+00:00"))
    except ValueError:
        return None


def load_state():
    try:
        return json.loads(STATE_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}
    except json.JSONDecodeError:
        print("! state.json was unreadable; starting fresh")
        return {}


def save_state(state):
    DATA_DIR.mkdir(exist_ok=True)
    tmp = STATE_PATH.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    tmp.replace(STATE_PATH)


def days_between(start, end):
    return [start + timedelta(days=i) for i in range((end - start).days + 1)]


def on_days(day, allowed):
    return not allowed or WEEKDAYS[day.weekday()] in allowed


def phase(watch, today):
    """-> "early" (not started yet), "on", or "done" (its active dates have passed)"""
    if watch["active_from"] and today < watch["active_from"]:
        return "early"
    if watch["active_until"] and today > watch["active_until"]:
        return "done"
    return "on"


def window_days(watch, today):
    """-> (days out still ahead of us, days home), keeping only days that can pair up
    within the allowed trip lengths and weekdays"""
    lo, hi = (int(n) for n in watch["nights"])
    stays = range(lo, hi + 1)
    homes = {d for d in days_between(*watch["back"]) if on_days(d, watch["return_days"])}
    out_days = [d for d in days_between(*watch["depart"])
                if d > today and on_days(d, watch["depart_days"])
                and any(d + timedelta(days=n) in homes for n in stays)]
    reachable = {d + timedelta(days=n) for d in out_days for n in stays}
    return out_days, sorted(homes & reachable)


def plan(watch, memory, today, now, settings):
    """This run's searches, most overdue first. A run that's cut short, or capped by
    max_searches_per_run, picks up where it left off next time."""
    out_days, back_days = window_days(watch, today)
    seen = memory.get("days", {})
    every = {"out": settings["out_every_minutes"], "back": settings["back_every_minutes"]}
    due = []
    for direction, days in (("out", out_days), ("back", back_days)):
        for day in days:
            checked = parse_iso(seen.get(f"{direction}|{day.isoformat()}", {}).get("checked"))
            age = float("inf") if checked is None else (now - checked).total_seconds() / 60
            if age >= every[direction]:
                due.append((-age / max(every[direction], 5), direction == "back", day, direction))
    due.sort()
    tasks = [(direction, day) for _, _, day, direction in due]
    cap = int(settings["max_searches_per_run"])
    return (tasks[:cap] if cap else tasks), out_days, back_days


def remember(memory, results, now):
    """Fold this run's results into memory. -> how many searches came back."""
    days = memory.setdefault("days", {})
    hour = now.strftime("%Y-%m-%dT%H")
    cutoff = (now - timedelta(hours=HISTORY_HOURS)).strftime("%Y-%m-%dT%H")
    ok = 0
    for (direction, day), summary, _ in results:
        if summary is None:
            continue
        ok += 1
        rec = days.setdefault(f"{direction}|{day.isoformat()}", {})
        rec["checked"] = iso(now)
        rec["best"], rec["nonstop"], rec["main"] = summary["best"], summary["nonstop"], summary["main"]
        rec["new_low"] = False
        if summary["best"]:
            price = summary["best"]["price"]
            hourly = rec.setdefault("hourly", {})
            hourly[hour] = min(price, hourly.get(hour, price))
            rec["hourly"] = {h: p for h, p in hourly.items() if h >= cutoff}
            rec["new_low"] = "low" in rec and price < rec["low"]
            rec["low"] = min(price, rec.get("low", price))
    return ok


def forget_past(memory, today):
    stamp = today.isoformat()
    memory["days"] = {k: v for k, v in memory.get("days", {}).items() if k.split("|")[1] > stamp}
    memory["alerts"] = {k: v for k, v in memory.get("alerts", {}).items() if k > stamp}


def recent_usual(rec, now):
    """What this day has cost lately (median of earlier hourly checks), or None if too new."""
    this_hour = now.strftime("%Y-%m-%dT%H")
    since = (now - timedelta(hours=DROP_WINDOW_HOURS)).strftime("%Y-%m-%dT%H")
    earlier = [p for h, p in rec.get("hourly", {}).items() if since <= h < this_hour]
    return statistics.median(earlier) if len(earlier) >= DROP_MIN_POINTS else None


def fresh(rec, now, hours=FRESH_HOURS):
    checked = parse_iso(rec.get("checked")) if rec else None
    return bool(rec and rec.get("best")) and checked is not None and (now - checked) <= timedelta(hours=hours)


def coverage(memory, days_by_direction, now):
    """-> share of the window's days whose page has loaded recently (priced or confirmed empty)."""
    total = have = 0
    for direction, days in days_by_direction:
        for d in days:
            total += 1
            rec = memory.get("days", {}).get(f"{direction}|{d.isoformat()}")
            checked = parse_iso(rec.get("checked")) if rec else None
            have += bool(checked and (now - checked) <= timedelta(hours=FRESH_HOURS))
    return have / total if total else 0.0


def pair_of(option):
    return f"{option['origin']}-{option['destination']}"


def baseline(rec):
    """The 60-day history for the airport pair of this day's current best fare, if we have it."""
    if not rec or not rec.get("best"):
        return {}
    return (rec.get("bases") or {}).get(pair_of(rec["best"])) or {}


def refresh_baselines(watch, memory, out_days, now, settings, fetch, deadline):
    """About once a day per travel day, read Google's 60-day price history for that day's
    cheapest airport pair. -> (how many were read, how many were due)"""
    stale = now - timedelta(hours=BASELINE_HOURS)
    todo = []
    for d in out_days:
        rec = memory.get("days", {}).get(f"out|{d.isoformat()}")
        if not fresh(rec, now):
            continue
        bases = rec.setdefault("bases", {})
        for pair in [k for k, b in bases.items() if (parse_iso(b.get("at")) or now) < now - timedelta(hours=48)]:
            del bases[pair]
        at = parse_iso(bases.get(pair_of(rec["best"]), {}).get("at"))
        if at is None or at < stale:
            todo.append((d, rec))

    def one(item):
        d, rec = item
        o = rec["best"]
        tfs = one_way_tfs(d, [o["origin"]], [o["destination"]], watch["max_stops"], hide_self_transfer=False)
        return item, load_one(tfs, settings["tries"], fetch, deadline)[0]

    read = 0
    with ThreadPoolExecutor(max_workers=int(settings["workers"])) as pool:
        for (d, rec), payload in pool.map(one, todo):
            if payload is not None:  # "no history offered" is an answer too: don't ask again until tomorrow
                rec["bases"][pair_of(rec["best"])] = {"at": iso(now), **(price_history(payload) or {})}
                read += 1
    return read, len(todo)


# ───────────────────────────── judging ─────────────────────────────

def money(p):
    return f"${p:,.0f}"


def ways_home(watch, memory, out_day, now):
    """Recent one-way prices home within the allowed trip lengths, cheapest first."""
    lo, hi = watch["nights"]
    first, last = watch["back"]
    found = []
    for n in range(int(lo), int(hi) + 1):
        day = out_day + timedelta(days=n)
        rec = memory.get("days", {}).get(f"back|{day.isoformat()}")
        if first <= day <= last and on_days(day, watch["return_days"]) and fresh(rec, now):
            found.append((rec["best"]["price"], day, rec["best"]))
    return sorted(found, key=lambda x: (x[0], x[1]))


def find_steals(watch, memory, out_days, now, just_checked):
    """Every outbound day that is a steal right now. Only days priced in THIS run can trigger."""
    steals = []
    for day in out_days:
        key = f"out|{day.isoformat()}"
        rec = memory.get("days", {}).get(key)
        if key not in just_checked or not rec or not rec.get("best"):
            continue
        best, price, base, reasons = rec["best"], rec["best"]["price"], baseline(rec), []
        if watch["steal_one_way"] and price <= watch["steal_one_way"]:
            reasons.append(f"at or under your {money(watch['steal_one_way'])} one-way steal price")
        low = base.get("low")
        if low and price <= low * (1 - watch["under_60_day_low_percent"] / 100):
            reasons.append(f"{round((1 - price / low) * 100)}% under the lowest price Google recorded for this "
                           f"day in the previous {base['days']} days ({money(low)})")
        usual = recent_usual(rec, now)
        if (usual and rec.get("new_low") and usual - price >= DROP_MIN_DOLLARS
                and price <= usual * (1 - watch["sudden_drop_percent"] / 100)
                and (not base.get("p25") or price <= base["p25"])):
            reasons.append(f"dropped {round((1 - price / usual) * 100)}% in the last day or so (it had been about "
                           f"{money(usual)})" + (", and it's now cheaper than on 3 of every 4 days in the past "
                                                 "two months" if base.get("p25") else ""))
        home = ways_home(watch, memory, day, now)
        total = price + home[0][0] if home else None
        if total and watch["steal_round_trip"] and total <= watch["steal_round_trip"]:
            reasons.append(f"round trip for {money(total)}, at or under your "
                           f"{money(watch['steal_round_trip'])} round-trip steal price")
        if reasons:
            steals.append({"day": day, "price": price, "best": best, "nonstop": rec.get("nonstop"),
                           "main": rec.get("main"), "base": base, "reasons": reasons,
                           "home": home[:3], "total": total})
    return sorted(steals, key=lambda s: (s["price"], s["day"]))


def is_news(memory, steal):
    """Alert once per day of travel, then again only if it gets meaningfully cheaper."""
    prev = memory.get("alerts", {}).get(steal["day"].isoformat())
    if not prev:
        return True
    if steal["price"] <= prev["price"] - max(10, 0.1 * prev["price"]):
        return True
    return bool(steal["total"] and prev.get("total")
                and steal["total"] <= prev["total"] - max(15, 0.1 * prev["total"]))


def still_there(steal, watch, settings, fetch):
    """Load that exact airport pair once more before emailing, so a one-off glitch can't
    set off an alert. -> True (seen again), False (gone), None (couldn't load the page)."""
    o = steal["best"]
    tfs = one_way_tfs(steal["day"], [o["origin"]], [o["destination"]], watch["max_stops"])
    payload, _ = load_one(tfs, settings["tries"], fetch)
    if payload is None:
        return None
    again = summarize(payload, watch, "out")["best"]
    return bool(again and again["price"] <= steal["price"] * 1.05 + 2)


# ───────────────────────────── wording ─────────────────────────────

def day_str(d):
    return f"{d:%a}, {d:%b} {d.day}"


def clock(hm):
    h, m = hm
    return f"{h % 12 or 12}:{m:02d} {'AM' if h < 12 else 'PM'}"


def length(minutes):
    return f"{minutes // 60}h {minutes % 60:02d}m"


def place(code):
    name = AIRPORT_NAMES.get(code)
    return f"{name} ({code})" if name and name != code else code


def stops_word(o):
    return "nonstop" if o["stops"] == 0 else f"{o['stops']} stop{'s' if o['stops'] > 1 else ''}"


def stops_str(o):
    return stops_word(o) if o["stops"] == 0 else f"{stops_word(o)} ({', '.join(o['via'])})"


def airline(o):
    return ", ".join(o["airlines"]) or "airline not listed"


def flight_line(o):
    lands = clock(o["lands"]) + (" next day" if o["next_day"] else "")
    return (f"{o['origin']} → {o['destination']} · {airline(o)} · {stops_str(o)} · "
            f"{clock(o['leaves'])} → {lands} ({length(o['minutes'])})")


def local_str(dt, tz):
    t = dt.astimezone(tz)
    return f"{t:%a}, {t:%b} {t.day} at {t.strftime('%I:%M %p').lstrip('0')} {t.tzname()}"


def rules_text(watch):
    lines = []
    if watch["steal_one_way"]:
        lines.append(f"a one-way out at {money(watch['steal_one_way'])} or less")
    if watch["steal_round_trip"]:
        lo, hi = watch["nights"]
        lines.append(f"a round trip (two one-ways, {lo:g} to {hi:g} nights) at "
                     f"{money(watch['steal_round_trip'])} or less")
    lines.append(f"any day priced {watch['under_60_day_low_percent']:g}% or more under its own lowest price "
                 f"of the past 60 days")
    lines.append(f"any day that suddenly drops {watch['sudden_drop_percent']:g}% or more to an unusually low price")
    return lines


def cheapest_days(memory, direction, days, now, count=None):
    rows = []
    for d in days:
        rec = memory.get("days", {}).get(f"{direction}|{d.isoformat()}")
        if fresh(rec, now):
            rows.append((rec["best"]["price"], d, rec))
    rows.sort(key=lambda r: (r[0], r[1]))
    return rows[:count] if count else rows


def best_round_trips(watch, memory, out_days, now, count=3):
    combos = []
    for d in out_days:
        rec = memory.get("days", {}).get(f"out|{d.isoformat()}")
        if not fresh(rec, now):
            continue
        home = ways_home(watch, memory, d, now)
        if home:
            combos.append((rec["best"]["price"] + home[0][0], d, home[0][1], rec["best"], home[0][2]))
    combos.sort(key=lambda c: (c[0], c[1]))
    return combos[:count]


FONT = ("font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,Helvetica,Arial,"
        "sans-serif;max-width:560px;color:#1a1a1a;line-height:1.45")
CARD = "border:1px solid #e2e2e2;border-radius:10px;padding:14px 16px;margin:0 0 12px"
MUTED = "color:#666;font-size:13px"
GOOD = "color:#0b7a34"
BUTTON = ("display:inline-block;background:#1a73e8;color:#fff;text-decoration:none;"
          "padding:8px 14px;border-radius:6px;font-weight:600")
FINE_PRINT = ("The lowest fares are usually basic economy, so a carry-on or checked bag can cost "
              "extra. Fares move fast: confirm the price before you book.")


def steal_email(watch, steals, now, tz):
    """-> (subject, text, html) for one email covering every new steal."""
    top = steals[0]
    o = top["best"]
    if len(steals) == 1:
        subject = (f"🚨 Flight steal: {money(top['price'])} one-way {o['origin']}→{o['destination']} "
                   f"{day_str(top['day'])} ({airline(o)}, {stops_word(o)})")
    else:
        subject = f"🚨 {len(steals)} flight steals from {money(top['price'])} one-way: {watch['name']}"
    main_airport = watch["destinations"][0]
    text = [watch["name"], ""]
    html = [f'<div style="{FONT}"><p style="margin:0 0 12px"><b>{escape(watch["name"])}</b></p>']
    for s in steals[:MAX_CARDS]:
        o = s["best"]
        link = search_url(s["day"], o["origin"], o["destination"], watch["max_stops"])
        extra = []
        if s["base"].get("low"):
            extra.append(f"This day over the past {s['base']['days']} days ({o['origin']}→{o['destination']}): "
                         f"lowest {money(s['base']['low'])}, typically {money(s['base']['median'])}.")
        if s["nonstop"] and o["stops"]:
            extra.append(f"Nonstop that day from {money(s['nonstop'])}.")
        if o["destination"] != main_airport and s["main"]:
            extra.append(f"Into {place(main_airport)} that day from {money(s['main'])}.")
        home = [f"{day_str(d)} {money(p)} ({b['origin']}→{b['destination']}, {airline(b)}, {stops_word(b)})"
                for p, d, b in s["home"]]
        if home:
            extra.append("Cheapest ways home: " + "; ".join(home) + ".")
            extra.append(f"Round trip from {money(s['total'])} as two one-ways.")
        headline = f"{day_str(s['day'])}: {money(s['price'])} one way to {place(o['destination'])}"
        text += [headline, flight_line(o), *("Why: " + r for r in s["reasons"]), *extra,
                 f"Google Flights: {link}", ""]
        html.append(
            f'<div style="{CARD}">'
            f'<div style="font-size:15px;font-weight:600">{escape(day_str(s["day"]))} '
            f'to {escape(place(o["destination"]))}</div>'
            f'<div style="font-size:30px;font-weight:700;margin:2px 0">{money(s["price"])} '
            f'<span style="font-size:14px;font-weight:400;color:#666">one way</span></div>'
            f'<div>{escape(flight_line(o))}</div>'
            f'<div style="{GOOD};margin-top:6px">{"<br>".join("✔ " + escape(r) for r in s["reasons"])}</div>'
            + "".join(f'<div style="margin-top:6px">{escape(x)}</div>' for x in extra)
            + f'<div style="margin-top:12px"><a href="{escape(link)}" style="{BUTTON}">'
              f"Open in Google Flights</a></div></div>")
    rest = steals[MAX_CARDS:]
    if rest:
        line = "Also at steal prices: " + "; ".join(
            f"{day_str(s['day'])} {money(s['price'])} ({s['best']['origin']}→{s['best']['destination']})"
            for s in rest) + "."
        text += [line, ""]
        html.append(f"<p>{escape(line)}</p>")
    foot = f"Checked {local_str(now, tz)}. {FINE_PRINT}"
    text.append(foot)
    html.append(f'<p style="{MUTED}">{escape(foot)}</p></div>')
    return subject, "\n".join(text), "".join(html)


def table_url(repo):
    return f"https://github.com/{repo}/blob/hyperwatch-data/latest.md" if repo else ""


def scope_text(watch, out_days, back_days):
    which = "every day" if not watch["depart_days"] else "every " + "/".join(watch["depart_days"])
    home = f" on {'/'.join(watch['return_days'])}" if watch["return_days"] else ""
    lo, hi = watch["nights"]
    places = f"{'/'.join(watch['origins'])} to {'/'.join(watch['destinations'])}"
    return (f"It prices {which} from {day_str(out_days[0])} to {day_str(out_days[-1])} ({places}, any airline), "
            f"plus trips home{home} through {day_str(back_days[-1])}, for trips of {lo:g} to {hi:g} nights.")


def overview_email(kind, watch, memory, out_days, back_days, now, tz, repo):
    """kind "launch": the hello when a watch starts. kind "summary": where prices stand."""
    if kind == "launch":
        subject = f"✈️ Now watching: {watch['name']}"
        intro = (scope_text(watch, out_days, back_days)
                 + " You'll hear from it only when something is exceptionally cheap.")
    else:
        subject = f"✈️ Price check: {watch['name']}"
        intro = "Here's where prices stand right now. " + scope_text(watch, out_days, back_days)
    cheap = cheapest_days(memory, "out", out_days, now, count=5)
    trips = best_round_trips(watch, memory, out_days, now, count=3 if kind == "launch" else 6)
    text, html = [], [f'<div style="{FONT}">']
    if watch["note"]:
        text += [watch["note"], ""]
        html.append(f'<p style="background:#fff4d6;padding:10px 12px;border-radius:8px">{escape(watch["note"])}</p>')
    text += [intro, "", "Cheapest one-ways out right now:"]
    html += [f"<p>{escape(intro)}</p>",
             f'<div style="{CARD}"><div style="font-weight:600;margin-bottom:6px">'
             f"Cheapest one-ways out right now</div>"]
    for price, d, rec in cheap:
        base = baseline(rec)
        past = ""
        if base.get("low") and price < base["low"]:
            past = f" (its lowest in {base['days']} days; the previous low was {money(base['low'])})"
        elif base.get("low") and price == base["low"]:
            past = f" (ties its lowest of the past {base['days']} days)"
        elif base.get("low"):
            past = f" (lowest in the past {base['days']} days: {money(base['low'])})"
        text.append(f"  {day_str(d)}: {money(price)}{past} · {flight_line(rec['best'])}")
        html.append(f'<div style="margin:4px 0"><b>{escape(day_str(d))}: {money(price)}</b>{escape(past)}<br>'
                    f'<span style="{MUTED}">{escape(flight_line(rec["best"]))}</span></div>')
    html.append("</div>")
    if trips:
        text += ["", "Cheapest round trips right now (two one-ways):"]
        html.append(f'<div style="{CARD}"><div style="font-weight:600;margin-bottom:6px">'
                    f"Cheapest round trips right now (two one-ways)</div>")
        for total, d_out, d_back, a, b in trips:
            nights = (d_back - d_out).days
            line = f"{day_str(d_out)} → {day_str(d_back)} ({nights} nights): {money(total)}"
            legs = (f"Out {money(a['price'])} {a['origin']}→{a['destination']} {airline(a)}, {stops_word(a)} · "
                    f"Back {money(b['price'])} {b['origin']}→{b['destination']} {airline(b)}, {stops_word(b)}")
            text += ["  " + line, "    " + legs]
            html.append(f'<div style="margin:4px 0"><b>{escape(line)}</b><br>'
                        f'<span style="{MUTED}">{escape(legs)}</span></div>')
        html.append("</div>")
    text += ["", "You'll get an alert for:"] + ["  - " + r for r in rules_text(watch)]
    html.append(f'<div style="{CARD}"><div style="font-weight:600;margin-bottom:6px">'
                f"You'll get an alert for</div>"
                + "".join(f'<div style="margin:4px 0">• {escape(r)}</div>' for r in rules_text(watch))
                + "</div>")
    foot = f"Sent {local_str(now, tz)}. {FINE_PRINT}"
    text += ["", foot]
    html.append(f'<p style="{MUTED}">{escape(foot)}')
    if repo:
        text.append(f"Every day's current price: {table_url(repo)}")
        html.append(f' <a href="{escape(table_url(repo))}">See every day\'s current price</a>.')
    html.append("</p></div>")
    return subject, "\n".join(text), "".join(html)


def plain_email(subject, paragraphs):
    html = f'<div style="{FONT}">' + "".join(f"<p>{escape(p)}</p>" for p in paragraphs) + "</div>"
    return subject, "\n\n".join(paragraphs), html


def latest_markdown(watches, state, now, tz):
    out = ["# Hyper Watch: latest prices", "", f"Updated {local_str(now, tz)}. Prices are one way, per person.", ""]
    today = now.astimezone(tz).date()
    for watch in watches:
        stage = phase(watch, today)
        if stage == "done":
            continue
        if stage == "early":
            out += [f"## {watch['name']}", "", f"Starts {day_str(watch['active_from'])}.", ""]
            continue
        memory = state.get("watches", {}).get(watch["id"], {})
        out_days, back_days = window_days(watch, today)
        out += [f"## {watch['name']}", ""]
        trips = best_round_trips(watch, memory, out_days, now, count=5)
        if trips:
            out += ["### Cheapest round trips (two one-ways)", "",
                    "| Out | Back | Total | Out flight | Back flight |", "|---|---|---|---|---|"]
            for total, d_out, d_back, a, b in trips:
                out.append(f"| {day_str(d_out)} | {day_str(d_back)} | **{money(total)}** | "
                           f"{money(a['price'])} {flight_line(a)} | {money(b['price'])} {flight_line(b)} |")
            out.append("")
        for direction, days, title in (("out", out_days, "One-way out, by day"),
                                       ("back", back_days, "One-way home, by day")):
            history = direction == "out"
            out += [f"### {title}", "",
                    "| Day | Lowest | Flight | Nonstop from |"
                    + (" Past 60 days: lowest | Past 60 days: typical |" if history else "") + " Checked |",
                    "|---|---|---|---|" + ("---|---|" if history else "") + "---|"]
            for d in days:
                rec = memory.get("days", {}).get(f"{direction}|{d.isoformat()}")
                blank = " | |" if history else ""
                if not rec or not rec.get("best"):
                    out.append(f"| {day_str(d)} | no price yet | | |{blank} |")
                    continue
                base = baseline(rec)
                past = (f" {money(base['low'])} | {money(base['median'])} |" if base.get("low") else blank) if history else ""
                checked = parse_iso(rec.get("checked"))
                when = checked.astimezone(tz).strftime("%b %d, %I:%M %p") if checked else ""
                nonstop = money(rec["nonstop"]) if rec.get("nonstop") else "–"
                out.append(f"| {day_str(d)} | **{money(rec['best']['price'])}** | {flight_line(rec['best'])} | "
                           f"{nonstop} |{past} {when} |")
            out.append("")
    return "\n".join(out) + "\n"


# ───────────────────────────── telling you ─────────────────────────────

def github_api(method, path, body=None):
    """Call this repo's GitHub API with the run's own token. -> the reply (parsed), or None"""
    token, repo = os.environ.get("GITHUB_TOKEN", ""), os.environ.get("GITHUB_REPOSITORY", "")
    if not (token and repo):
        raise RuntimeError("not running on GitHub")
    req = urllib.request.Request(
        f"https://api.github.com/repos/{repo}" + (f"/{path}" if path else ""), method=method,
        data=json.dumps(body).encode() if body is not None else None,
        headers={"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
                 "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "hyperwatch"})
    with urllib.request.urlopen(req, timeout=20) as res:
        raw = res.read()
    return json.loads(raw) if raw.strip() else None


def smtp_settings():
    """-> (sender, password, recipients) when the email secrets are set, else None"""
    sender = os.environ.get("EMAIL_FROM", "").strip()
    password = "".join(os.environ.get("EMAIL_APP_PASSWORD", "").split())  # app passwords show with spaces
    to = [a.strip() for a in os.environ.get("EMAIL_TO", "").split(",") if a.strip()]
    return (sender, password, to) if sender and password and to else None


def send_email(subject, text, html):
    sender, password, to = smtp_settings()
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = formataddr(("Flight Watch", sender))
    msg["To"] = ", ".join(to)
    msg.set_content(text)
    msg.add_alternative(html, subtype="html")
    host = os.environ.get("SMTP_HOST", "").strip() or "smtp.gmail.com"
    chosen = os.environ.get("SMTP_PORT", "").strip()
    problem = None
    for port in ([int(chosen)] if chosen.isdigit() else [465, 587]):
        try:
            # 465 is encrypted from the first byte; 587 starts plain and upgrades (STARTTLS)
            server = smtplib.SMTP_SSL(host, port, timeout=30) if port == 465 else smtplib.SMTP(host, port, timeout=30)
            with server:
                if port != 465:
                    server.starttls()
                server.login(sender, password)
                server.send_message(msg)
            return
        except smtplib.SMTPAuthenticationError:
            raise  # a wrong password won't get better on another port
        except (smtplib.SMTPException, OSError) as e:
            problem = e
    raise problem


def to_markdown(text):
    """The plain-text version of an email, tidied for a GitHub issue."""
    lines = []
    for line in text.split("\n"):
        label, _, link = line.partition(": http")
        if link and label in ("Google Flights", "Every day's current price"):
            words = "Open in Google Flights" if label == "Google Flights" else "See every day's current price"
            lines.append(f"[{words}](http{link})")
        else:
            lines.append(line.replace("$", "\\$"))  # GitHub would read $...$ as math
    return "\n".join(lines)


def open_issue(subject, body):
    """GitHub emails new issues to the repo's owner; assigning it to them makes sure of it."""
    owner = os.environ.get("GITHUB_REPOSITORY_OWNER", "").strip()
    try:
        github_api("POST", "issues", {"title": subject, "body": body, "assignees": [owner] if owner else []})
    except urllib.error.HTTPError as e:
        if e.code != 422:
            raise
        github_api("POST", "issues", {"title": subject, "body": body})


def tell(subject, text, html):
    """Reach you: by email when the email secrets are set, otherwise (or if email fails)
    by opening a GitHub issue, which GitHub emails to you."""
    if smtp_settings():
        try:
            send_email(subject, text, html)
            print(f"📧 Sent: {subject}")
            return True
        except Exception as e:
            print(f"✗ Email failed ({type(e).__name__}: {str(e)[:200]}). Opening a GitHub issue instead.")
    try:
        open_issue(subject, to_markdown(text))
        print(f"📝 Opened a GitHub issue (GitHub emails it to you): {subject}")
        return True
    except Exception as e:
        print(f"✗ Couldn't open a GitHub issue: {e}")
        return False


def switch_off():
    try:
        github_api("PUT", f"actions/workflows/{WORKFLOW_FILE}/disable")
        print("Schedule switched off.")
    except Exception as e:
        print(f"! Couldn't switch the schedule off ({e}).")


PAUSE_ENVIRONMENT = "pause"  # the GitHub environment whose wait timer spaces the checks out


def pause_problem():
    """Why this repo can't pause between checks, "" when it can, or None when GitHub wouldn't say.
    The pause is the wait timer on the job's GitHub environment. Free accounts only get wait
    timers on public repositories, and without one the loop would run back to back."""
    try:
        if github_api("GET", "")["private"]:
            return "this repository is private, so GitHub ignores the wait timer"
        rules = github_api("GET", f"environments/{PAUSE_ENVIRONMENT}").get("protection_rules") or []
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return f'there is no "{PAUSE_ENVIRONMENT}" environment in this repository\'s settings'
        return None
    except Exception:
        return None
    minutes = max((r.get("wait_timer") or 0 for r in rules if r.get("type") == "wait_timer"), default=0)
    return "" if minutes >= 1 else f'the "{PAUSE_ENVIRONMENT}" environment has no wait timer'


def start_next():
    """Line up the next check. Used where the workflow pauses between checks by itself (see
    the workflow file): each run starts its successor, so the pace doesn't depend on GitHub's
    scheduler. The newest unfinished run always carries the loop on, so this run only starts
    a successor when nothing newer is already waiting."""
    mode = os.environ.get("HYPERWATCH_CHAIN", "").strip().lower()
    if mode not in ("once", "forever"):
        print("Not lining up another check (chain is off).")
        return 0
    state = load_state()
    now = utc_now()
    if state.get("finished") or state.get("capped") == now.strftime("%Y-%m"):
        print("The watch is over or paused, so no further check is lined up.")
        return 0
    me = int(os.environ.get("GITHUB_RUN_ID", "0") or 0)
    try:
        runs = github_api("GET", f"actions/workflows/{WORKFLOW_FILE}/runs?per_page=30")["workflow_runs"]
    except Exception as e:
        print(f"! Couldn't list runs ({e}); lining up the next check anyway.")
        runs = []
    newer = sorted(r["id"] for r in runs if r["status"] != "completed" and r["id"] > me)
    if newer:
        print(f"A newer check is already lined up (run {newer[-1]}); it carries on from here.")
        return 0
    if mode == "forever":
        # Never loop without a real pause: that would run checks back to back.
        why = pause_problem()
        if why:
            print(f"✗ Not lining up another check: {why}.")
            return 0
        recent = [r for r in runs if (parse_iso(r.get("run_started_at")) or now) > now - timedelta(minutes=10)]
        if len(recent) >= 6:
            print(f"✗ Not lining up another check: {len(recent)} checks started in the last 10 minutes, "
                  f"so the pause between them isn't working.")
            return 0
    body = {"ref": os.environ.get("GITHUB_REF_NAME", "") or "main",
            "inputs": {"chain": "forever" if mode == "forever" else "off"}}
    for attempt in range(1, 6):
        try:
            github_api("POST", f"actions/workflows/{WORKFLOW_FILE}/dispatches", body)
            print("Next check lined up.")
            return 0
        except Exception as e:
            print(f"! Couldn't line up the next check (try {attempt} of 5): {e}")
            time.sleep(3 * attempt)
    print("✗ Gave up. The backup schedule will restart the loop.")
    return 0


# ───────────────────────────── main ─────────────────────────────

def print_table(watch, memory, out_days, back_days, now):
    for direction, days in (("out", out_days), ("back", back_days)):
        print(f"  --- one-way {'out' if direction == 'out' else 'home'} ---")
        for d in days:
            rec = memory.get("days", {}).get(f"{direction}|{d.isoformat()}")
            if not rec:
                print(f"    {day_str(d)}: not loaded")
            elif not rec.get("best"):
                print(f"    {day_str(d)}: no flights listed")
            else:
                base = baseline(rec)
                past = (f"60d low {money(base['low'])} p25 {money(base['p25'])} med {money(base['median'])} "
                        f"usual {base['usual']}" if base.get("low") else "no history")
                nonstop = f"nonstop {money(rec['nonstop'])}" if rec.get("nonstop") else "no nonstop listed"
                print(f"    {day_str(d)}: {money(rec['best']['price'])} · {flight_line(rec['best'])} | "
                      f"{nonstop}" + (f" | {past}" if direction == "out" else ""))


def run_watch(watch, settings, state, now, dry_run, fetch=fetch_payload, summary_now=False):
    """-> (searches that came back, searches tried, whether this watch is over)"""
    tz = settings["tz"]
    today = now.astimezone(tz).date()
    stage = phase(watch, today)
    if stage != "on":
        print(f"\n{watch['name']}: " + (f"starts {day_str(watch['active_from'])}" if stage == "early"
                                        else f"ended {day_str(watch['active_until'])}"))
        return 0, 0, stage == "done"
    memory = state.setdefault("watches", {}).setdefault(watch["id"], {})
    forget_past(memory, today)
    tasks, out_days, back_days = plan(watch, memory, today, now, settings)
    print(f"\n{watch['name']}: {len(out_days)} days out, {len(back_days)} days home; "
          f"{len(tasks)} searches this run")
    if not out_days:
        print("  Every travel day in this watch has passed.")
        if not memory.get("ended") and not dry_run and tell(*plain_email(
                f"✈️ Finished watching: {watch['name']}",
                [f'Every travel day in "{watch["name"]}" has now passed, so this watch has stopped.'])):
            memory["ended"] = iso(now)
        return 0, 0, True

    started = time.monotonic()
    deadline = started + settings["budget_seconds"]
    results = sweep(tasks, watch, settings, fetch, deadline)
    ok = remember(memory, results, now)
    read, due = refresh_baselines(watch, memory, out_days, now, settings, fetch, deadline)
    just_checked = {f"{d}|{day.isoformat()}" for (d, day), summary, _ in results if summary is not None}
    problems = {}
    for _, summary, problem in results:
        if summary is None:
            problems[problem] = problems.get(problem, 0) + 1
    print(f"  {ok} of {len(tasks)} searches came back"
          + (f", plus {read} of {due} price histories" if due else "") + f", in {time.monotonic() - started:.0f}s"
          + ("" if not problems else " | missed: " + "; ".join(f"{n}× {p}" for p, n in problems.items())))

    if dry_run:
        print_table(watch, memory, out_days, back_days, now)
    for price, d, rec in cheapest_days(memory, "out", out_days, now, count=5):
        print(f"    {day_str(d)}: {money(price)} · {flight_line(rec['best'])}")
    for total, d_out, d_back, _, _ in best_round_trips(watch, memory, out_days, now):
        print(f"    round trip {day_str(d_out)} → {day_str(d_back)}: {money(total)}")

    steals = find_steals(watch, memory, out_days, now, just_checked)
    news = [s for s in steals if is_news(memory, s)]
    for s in steals:
        tag = "NEW" if s in news else "already alerted"
        print(f"  ★ {day_str(s['day'])} {money(s['price'])} ({tag}): {'; '.join(s['reasons'])}")
    if dry_run:
        return ok, len(tasks), False

    covered = coverage(memory, (("out", out_days), ("back", back_days)), now)
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    if not memory.get("launched") and covered >= 0.85 and read >= 0.8 * due:
        if tell(*overview_email("launch", watch, memory, out_days, back_days, now, tz, repo)):
            memory["launched"] = iso(now)
    sent = memory.setdefault("summaries", [])
    wanted = [m.strftime("%Y-%m-%d %H:%M") for m in watch["summary_at"] if m <= now < m + timedelta(hours=12)]
    wanted = [stamp for stamp in wanted if stamp not in sent]
    if (wanted or summary_now) and covered >= 0.85:
        if tell(*overview_email("summary", watch, memory, out_days, back_days, now, tz, repo)):
            sent.extend(wanted)

    confirmed = []
    for s in news[:MAX_CARDS + 4]:
        seen_again = still_there(s, watch, settings, fetch)
        if seen_again is False:
            print(f"  ✗ {day_str(s['day'])} {money(s['price'])} was gone on a second look; not alerting")
        else:
            confirmed.append(s)
    if confirmed and tell(*steal_email(watch, confirmed, now, tz)):
        for s in confirmed:
            memory.setdefault("alerts", {})[s["day"].isoformat()] = {
                "price": s["price"], "total": s["total"], "at": iso(now)}
    return ok, len(tasks), False


def check_health(state, ok, tried, now, tz):
    """One heads-up if searches keep failing, one all-clear when they recover."""
    health = state.setdefault("health", {})
    if tried and ok < 0.5 * tried:
        health["bad_runs"] = health.get("bad_runs", 0) + 1
        health.setdefault("bad_since", iso(now))
        if health["bad_runs"] >= 3 and not health.get("told"):
            since = parse_iso(health["bad_since"]) or now
            if tell(*plain_email(
                    "⚠️ Hyper Watch is having trouble reaching Google Flights",
                    [f"The last {health['bad_runs']} checks got few or no prices back (since "
                     f"{local_str(since, tz)}). Google may be turning away GitHub's servers for now. "
                     f"The watch keeps trying on every run, and you'll get one more note when prices "
                     f"are coming through again.",
                     "If this goes on for a day, ask Claude to take a look."])):
                health["told"] = True
    elif tried:
        if health.get("told"):
            tell(*plain_email("✅ Hyper Watch is getting prices again",
                              ["Searches are coming back normally again. Nothing for you to do."]))
        state["health"] = {}


def over_monthly_cap(state, settings, now):
    """Count this month's runs; past the cap, pause the schedule so the other watchers that
    share your free GitHub minutes keep running."""
    month = now.strftime("%Y-%m")
    count = state.get("runs", {}).get(month, 0) + 1
    state["runs"] = {month: count}
    if not settings["monthly_run_cap"] or count <= settings["monthly_run_cap"]:
        return False
    print(f"Run {count} this month is over the cap of {settings['monthly_run_cap']:g}; pausing the schedule.")
    if state.get("capped") != month and tell(*plain_email(
            "⏸️ Hyper Watch paused itself for the rest of the month",
            [f"It has run {count - 1} times this month, which is the limit set to protect your free "
             f"GitHub minutes (your other watchers share them).",
             "To start it again: open the repo on GitHub, click Actions, click Hyper Watch on the left, "
             "then click Enable workflow. Or ask Claude."])):
        state["capped"] = month
    return True


def report_problem(text, dry_run):
    """Email a problem once (not on every run). -> exit code"""
    print(f"✗ {text}")
    if dry_run:
        return 1
    state = load_state()
    if state.get("problem") != text:
        if not tell(*plain_email("⚠️ Hyper Watch hit a problem and needs a look",
                                 [text, "It can't check prices until this is fixed. Ask Claude to take a look."])):
            return 1
        state["problem"] = text
        save_state(state)
    return 0


def run(args, fetch, now):
    try:
        settings, watches = load_config()
    except ConfigError as e:
        return report_problem(f"hyperwatch.toml problem: {e}", args.dry_run)

    now = now or utc_now()
    state = load_state()
    state.pop("problem", None)
    print(f"Hyper Watch ({local_str(now, settings['tz'])})")
    if not args.dry_run and over_monthly_cap(state, settings, now):
        save_state(state)
        switch_off()
        return 0

    ok = tried = 0
    all_over = True
    for watch in watches:
        w_ok, w_tried, over = run_watch(watch, settings, state, now, args.dry_run, fetch, args.summary_now)
        ok, tried, all_over = ok + w_ok, tried + w_tried, all_over and over
    if args.dry_run:
        print("\n(dry run: no email sent, nothing saved)")
        return 0

    check_health(state, ok, tried, now, settings["tz"])
    state["last_run"] = iso(now)
    state["finished"] = all_over
    save_state(state)
    LATEST_PATH.write_text(latest_markdown(watches, state, now, settings["tz"]), encoding="utf-8")
    if all_over:
        switch_off()
    return 0


def main(argv=None, fetch=fetch_payload, now=None):
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(errors="replace")
    ap = argparse.ArgumentParser(description="Price every day in a travel window; email the steals.")
    ap.add_argument("--dry-run", action="store_true", help="search and print only")
    ap.add_argument("--summary-now", action="store_true", help="also send the 'where prices stand' email")
    ap.add_argument("--test-notification", action="store_true",
                    help="send a test message the way alerts are sent, then stop")
    ap.add_argument("--next", action="store_true", help="line up the next check (the workflow calls this)")
    args = ap.parse_args(argv)
    try:
        if args.next:
            return start_next()
        if args.test_notification:
            return 0 if tell(*plain_email(
                "[TEST] Hyper Watch can reach you",
                ["This is a test from Hyper Watch. If you're reading it, real alerts will reach you "
                 "the same way."])) else 1
        return run(args, fetch, now)
    except Exception as e:
        traceback.print_exc()
        return report_problem(f"Unexpected error: {type(e).__name__}: {str(e)[:200]}", args.dry_run)


if __name__ == "__main__":
    sys.exit(main())
