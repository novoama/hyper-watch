#!/usr/bin/env python3
"""
Offline checks for hyperwatch.py: no internet, no email. It replaces Google
Flights with made-up pages and the email step with a recorder, then walks the
watch through its whole life.

  python hyperwatch_selftest.py
"""
import base64
import contextlib
import io
import os
import re
import sys
import tempfile
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

import hyperwatch as hw

PROBLEMS = []
NYC = {"EWR", "JFK", "LGA"}
REAL_TELL = hw.tell
EMAIL_KEYS = ("EMAIL_FROM", "EMAIL_APP_PASSWORD", "EMAIL_TO", "GITHUB_REPOSITORY_OWNER", "GITHUB_RUN_ID",
              "HYPERWATCH_CHAIN", "GITHUB_REF_NAME")


def check(name, condition, detail=""):
    print(f"  {'✓' if condition else '✗'} {name}" + (f" ({str(detail)[:400]})" if detail and not condition else ""))
    if not condition:
        PROBLEMS.append(name)


# ─────────────── made-up Google Flights pages ───────────────

def fake_option(price, origin="EWR", dest="SJU", via=(), carrier="United", minutes=235,
                leaves=(7, 0), lands=(11, 55), lands_next_day=False):
    airports = [origin, *via, dest]
    legs = []
    for a, b in zip(airports, airports[1:]):
        leg = [None] * 23
        leg[3], leg[6] = a, b
        leg[8] = list(leaves) if leaves[1] else [leaves[0]]  # Google drops a zero minute
        leg[10] = list(lands)
        leg[11] = minutes // (len(airports) - 1)
        leg[20] = [2026, 12, 9]
        leg[21] = [2026, 12, 10] if lands_next_day else [2026, 12, 9]
        leg[22] = ["UA", "123", None, carrier]
        legs.append(leg)
    flight = [None] * 24
    flight[0], flight[1], flight[2], flight[9] = "UA", [carrier], legs, minutes
    return [flight, [[None, price], "token"]]


def fake_page(best=(), other=(), history=None, today=None):
    """`history` = (low, high): 60 past days spread evenly between them, then today's price."""
    page = [None] * 32
    page[2] = [list(best) or None, None, 0, 0, [1]]
    page[3] = [list(other) or None, 116, 0, 0, [1]]
    if history:
        low, high = history
        past = [[1789617600000 + i * 86400000, round(low + (high - low) * i / 59)] for i in range(60)]
        series = past + [[1789617600000 + 60 * 86400000, today]]
        page[5] = [2, [None, today], [None, 175], [None, 175 - today], [None, 105], [None, 280], 1,
                   None, None, None, [series]]
    return page


class FakeGoogle:
    """Prices by (direction, day). Anything not listed costs the default.
    It tells the three kinds of search apart the way the real one differs:
      sweep    several airports at once
      confirm  one airport pair, self-transfer trips hidden
      history  one airport pair, plain (the only kind that comes with the 60-day history)"""

    def __init__(self, default_out=140, default_back=170, history=(120, 200)):
        self.default_out, self.default_back, self.history = default_out, default_back, history
        self.out, self.back, self.confirm_price = {}, {}, {}
        self.calls, self.fail_all, self.fail_first = [], False, set()

    def __call__(self, tfs):
        raw = base64.b64decode(tfs)
        day = date.fromisoformat(re.search(rb"\d{4}-\d{2}-\d{2}", raw).group().decode())
        codes = [c.decode() for c in re.findall(rb"\x12\x03([A-Z]{3})", raw)]
        direction = "out" if codes[0] in NYC else "back"
        hidden = raw.endswith(b"\x88\x01\x01\x98\x01\x02")
        kind = "sweep" if len(codes) > 2 else ("confirm" if hidden else "history")
        self.calls.append((direction, day, kind))
        if self.fail_all:
            raise hw.Withheld("Google withheld the results")
        if (direction, day) in self.fail_first:
            self.fail_first.discard((direction, day))
            raise hw.Withheld("Google withheld the results")
        if direction == "out":
            price = self.out.get(day, self.default_out)
            if kind == "confirm" and day in self.confirm_price:
                price = self.confirm_price[day]
            return fake_page(
                best=[fake_option(price + 30, "EWR", "SJU")],
                other=[fake_option(price, "JFK", "SJU", via=("MCO",), carrier="JetBlue", minutes=461,
                                   leaves=(16, 53), lands=(1, 34), lands_next_day=True),
                       fake_option(price - 20, "LGA", "SJU", via=("ORD", "IAD"), minutes=600),      # 2 stops
                       fake_option(price - 30, "EWR", "PSE", via=("MCO",), carrier="Frontier", minutes=1540),  # 25 h
                       fake_option(price + 90, "EWR", "BQN")],
                history=self.history if kind == "history" else None, today=price)
        price = self.back.get(day, self.default_back)
        return fake_page(other=[fake_option(price, "SJU", "EWR"), fake_option(price + 40, "BQN", "EWR")])


# ─────────────── a sandboxed watch ───────────────

CONFIG = """
[settings]
budget_seconds = 60
[[watch]]
name = "NYC → Puerto Rico, December"
origins = ["EWR", "JFK", "LGA"]
destinations = ["SJU", "BQN", "PSE"]
depart_between = ["2026-12-01", "2026-12-31"]
return_between = ["2026-12-03", "2027-01-10"]
steal_one_way = 75
steal_round_trip = 180
"""


class Sandbox:
    def __init__(self, config=CONFIG):
        self.dir = Path(tempfile.mkdtemp(prefix="hyperwatch-test-"))
        (self.dir / "hyperwatch.toml").write_text(config, encoding="utf-8")
        hw.CONFIG_PATH = self.dir / "hyperwatch.toml"
        hw.DATA_DIR = self.dir / "data"
        hw.STATE_PATH = hw.DATA_DIR / "state.json"
        hw.LATEST_PATH = hw.DATA_DIR / "latest.md"
        self.sent, self.switched_off = [], 0
        hw.tell = lambda subject, text, html: (self.sent.append((subject, text, html)), True)[1]
        hw.switch_off = lambda: setattr(self, "switched_off", self.switched_off + 1)
        hw.time.sleep = lambda seconds: None
        self.google = FakeGoogle()

    def run(self, now, *args):
        before = len(self.sent)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            code = hw.main(list(args), fetch=self.google, now=now)
        self.log = buf.getvalue()
        return code, self.sent[before:]


def at(month, day, hour, minute=4):
    """A UTC time in 2026; an hour past 23 rolls into the next day."""
    return datetime(2026, month, day, 0, minute, tzinfo=timezone.utc) + timedelta(hours=hour)


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(errors="replace")
    print("Hyper Watch self-test")

    # 1. Reading a page
    watch = {"max_stops": 1, "max_hours": 12, "destinations": ["SJU", "BQN", "PSE"]}
    page = FakeGoogle()(hw.one_way_tfs(date(2026, 12, 9), ["EWR", "JFK", "LGA"], ["SJU", "BQN", "PSE"], 1))
    s = hw.summarize(page, watch, "out")
    check("picks the cheapest sensible flight, skipping 2-stop and 25-hour trips",
          s["best"]["price"] == 140 and s["best"]["origin"] == "JFK" and s["best"]["via"] == ["MCO"], str(s["best"]))
    check("finds the cheapest nonstop and the cheapest into San Juan", s["nonstop"] == 170 and s["main"] == 140, str(s))
    page = FakeGoogle()(hw.one_way_tfs(date(2026, 12, 9), ["JFK"], ["SJU"], 1, hide_self_transfer=False))
    past = hw.price_history(page)
    check("reads Google's 60-day history for a day, leaving out today",
          past == {"low": 120, "p25": 140, "median": 160, "days": 60, "usual": 175}, str(past))
    check("no history on the page is fine", hw.price_history(fake_page()) is None)
    line = hw.flight_line(s["best"])
    check("describes a flight in plain words",
          line == "JFK → SJU · JetBlue · 1 stop (MCO) · 4:53 PM → 1:34 AM next day (7h 41m)", line)
    check("an empty page means no flights, not a crash", hw.summarize(fake_page(), watch, "out")["best"] is None)

    # 2. First run: prices everything, sends the hello email, no steals at normal prices
    box = Sandbox()
    code, sent = box.run(at(11, 16, 21))
    outs = {d for direction, d, kind in box.google.calls if direction == "out" and kind == "sweep"}
    backs = {d for direction, d, kind in box.google.calls if direction == "back"}
    pasts = [d for direction, d, kind in box.google.calls if kind == "history"]
    check("first run prices all 31 December days out", len(outs) == 31 and min(outs) == date(2026, 12, 1), str(len(outs)))
    check("and every day home through Jan 10", len(backs) == 39 and max(backs) == date(2027, 1, 10), str(len(backs)))
    check("and reads each day's 60-day history once", len(pasts) == 31 and len(set(pasts)) == 31, str(len(pasts)))
    check("sends one 'Now watching' email and no steal alert",
          code == 0 and len(sent) == 1 and sent[0][0].startswith("✈️ Now watching"), str([s[0] for s in sent]))
    check("that email lists today's lows and the alert rules",
          "Tue, Dec 1: $140 (lowest in the past 60 days: $120)" in sent[0][1] and "$75 or less" in sent[0][1]
          and "$310" in sent[0][1] and "under its own lowest price of the past 60 days" in sent[0][1], sent[0][1][:300])
    table = hw.LATEST_PATH.read_text(encoding="utf-8")
    check("writes the readable price table", "| Tue, Dec 1 | **$140** |" in table and "| $120 | $160 |" in table, table[:600])

    # 3. 45 minutes later: trips out are re-priced, trips home are not due yet
    box.google.calls.clear()
    code, sent = box.run(at(11, 16, 21, 49))
    check("next run re-prices every day out but skips trips home (not due for 90 min)",
          [c[2] for c in box.google.calls if c[0] == "out"] == ["sweep"] * 31
          and not any(c[0] == "back" for c in box.google.calls) and not sent, box.log[:200])

    # 4. A fare falls under the one-way steal price
    box.google.out[date(2026, 12, 8)] = 69
    code, sent = box.run(at(11, 16, 22, 34))
    check("a $69 one-way sets off exactly one alert",
          len(sent) == 1 and sent[0][0] == "🚨 Flight steal: $69 one-way JFK→SJU Tue, Dec 8 (JetBlue, 1 stop)",
          str([s[0] for s in sent]))
    body = sent[0][1] if sent else ""
    check("the alert explains why, shows the way home, and links to Google Flights",
          "at or under your $75 one-way steal price" in body and "Cheapest ways home" in body
          and "43% under the lowest price Google recorded for this day in the previous 60 days ($120)" in body
          and "This day over the past 60 days (JFK→SJU): lowest $120, typically $160." in body
          and "Round trip from $239" in body and "Nonstop that day from $99" in body
          and "https://www.google.com/travel/flights/search?tfs=" in body, body)
    check("it looked at that exact airport pair again before emailing",
          ("out", date(2026, 12, 8), "confirm") in box.google.calls)
    code, sent = box.run(at(11, 16, 23, 19))
    check("the same fare doesn't alert twice", not sent, str([s[0] for s in sent]))
    box.google.out[date(2026, 12, 8)] = 66
    code, sent = box.run(at(11, 17, 0, 4))
    check("a $3 dip doesn't re-alert", not sent)
    box.google.out[date(2026, 12, 8)] = 58
    code, sent = box.run(at(11, 17, 0, 49))
    check("a real further drop does", len(sent) == 1 and "$58" in sent[0][0], str([s[0] for s in sent]))

    # 5. A glitch: cheap in the sweep, gone on the second look
    box.google.out[date(2026, 12, 15)] = 60
    box.google.confirm_price[date(2026, 12, 15)] = 140
    code, sent = box.run(at(11, 17, 1, 34))
    check("a price that's gone on the second look doesn't alert",
          not sent and "was gone on a second look" in box.log, box.log[-300:])
    del box.google.out[date(2026, 12, 15)], box.google.confirm_price[date(2026, 12, 15)]

    # 6. Round-trip rule
    box.google.out[date(2026, 12, 10)] = 95
    box.google.back[date(2026, 12, 14)] = 80
    code, sent = box.run(at(11, 17, 3, 4))
    check("out + back under the round-trip price alerts",
          len(sent) == 1 and "round trip for $175, at or under your $180" in sent[0][1], str([s[1][:200] for s in sent]))

    # 7. Under that day's own 60-day low (a pricey holiday day, nowhere near the $75 mark)
    box2 = Sandbox()
    box2.google.default_out, box2.google.history = 420, (380, 700)
    box2.run(at(11, 16, 21))
    box2.google.out[date(2026, 12, 23)] = 345
    code, sent = box2.run(at(11, 16, 21, 49))
    check("a holiday fare only 9% under its 60-day low stays quiet", not sent, str([s[0] for s in sent]))
    box2.google.out[date(2026, 12, 23)] = 330
    code, sent = box2.run(at(11, 16, 22, 34))
    check("13% under its 60-day low alerts, even at $330",
          len(sent) == 1 and "13% under the lowest price Google recorded for this day in the previous 60 days ($380)"
          in sent[0][1], str([s[1][:300] for s in sent]))

    # 8. Sudden drop
    def drop_case(history):
        box = Sandbox()
        box.google.history, box.google.default_out = history, 300
        for hour in range(6):
            box.run(at(11, 16, 12 + hour))
        box.google.out[date(2026, 12, 20)] = 185
        return box, box.run(at(11, 16, 19))[1]

    box3, sent = drop_case(None)
    check("a 38% overnight drop alerts when Google offers no history for that day",
          len(sent) == 1 and "dropped 38% in the last day or so (it had been about $300)" in sent[0][1],
          str([s[1][:300] for s in sent]))
    _, sent = drop_case((170, 420))
    check("the same drop alerts when it's also cheaper than 3 of every 4 days in the past two months",
          len(sent) == 1 and "cheaper than on 3 of every 4 days in the past two months" in sent[0][1],
          str([s[1][:300] for s in sent]))
    _, sent = drop_case((170, 190))
    check("but not when that day was usually this cheap anyway", not sent, str([s[0] for s in sent]))
    box3.google.out[date(2026, 12, 21)] = 500
    for hour in range(5):
        box3.run(at(11, 16, 20) + timedelta(hours=hour))
    del box3.google.out[date(2026, 12, 21)]
    code, sent = box3.run(at(11, 17, 2))
    check("a fare bouncing back to its old price is not a steal", not sent, str([s[0] for s in sent]))

    # 9. Google trouble: one heads-up after 3 bad runs, one all-clear after
    box4 = Sandbox()
    box4.run(at(11, 16, 21))
    box4.google.fail_all = True
    notes = []
    for i in range(5):
        notes += box4.run(at(11, 16, 22 + i))[1]
    check("five failed runs in a row send one heads-up, and the run still exits cleanly",
          len(notes) == 1 and "having trouble" in notes[0][0], str([n[0] for n in notes]))
    box4.google.fail_all = False
    code, sent = box4.run(at(11, 17, 4))
    check("recovery sends one all-clear", len(sent) == 1 and "getting prices again" in sent[0][0])
    box4.google.fail_first = {("out", date(2026, 12, 5)), ("back", date(2026, 12, 9))}
    box4.google.calls.clear()
    code, sent = box4.run(at(11, 17, 6))
    tried_twice = box4.google.calls.count(("out", date(2026, 12, 5), "sweep")) == 2
    check("a withheld page is retried within the same run, and nothing is missed",
          tried_twice and "missed" not in box4.log and not sent, box4.log[:300])

    # 10. Safety net for the free minutes
    box5 = Sandbox(CONFIG.replace("budget_seconds = 60", "budget_seconds = 60\nmonthly_run_cap = 3"))
    for i in range(3):
        box5.run(at(11, 16, 10 + i))
    box5.google.calls.clear()
    code, sent = box5.run(at(11, 16, 14))
    code2, sent2 = box5.run(at(11, 16, 15))
    check("past the monthly cap it pauses the schedule, says so once, and searches nothing",
          box5.switched_off == 2 and len(sent) == 1 and "paused itself" in sent[0][0] and not sent2
          and not box5.google.calls, f"{box5.switched_off} {[s[0] for s in sent]}")
    code, sent = box5.run(at(12, 1, 0))
    check("a new month starts the count over", box5.switched_off == 2 and len(box5.google.calls) > 0)

    # 11. Settings typo: one email, then quiet
    box6 = Sandbox(CONFIG.replace("steal_one_way = 75", "steal_one_wya = 75"))
    code, sent = box6.run(at(11, 16, 21))
    code2, sent2 = box6.run(at(11, 16, 22))
    check("a typo in the settings is reported once, in plain words",
          len(sent) == 1 and "unknown option(s): steal_one_wya" in sent[0][1] and not sent2, str(sent))

    # 12. December rolls by, then the watch ends itself
    box7 = Sandbox()
    box7.run(at(11, 16, 21))
    box7.google.calls.clear()
    box7.run(at(12, 20, 15))
    outs = {d for direction, d, kind in box7.google.calls if direction == "out"}
    check("on Dec 20 it only prices Dec 21 onward", min(outs) == date(2026, 12, 21) and len(outs) == 11, str(sorted(outs)[:2]))
    code, sent = box7.run(datetime(2027, 1, 1, 6, 0, tzinfo=timezone.utc))
    code2, sent2 = box7.run(datetime(2027, 1, 1, 7, 0, tzinfo=timezone.utc))
    check("after Dec 31 it says goodbye once and switches its schedule off",
          len(sent) == 1 and sent[0][0].startswith("✈️ Finished watching") and not sent2 and box7.switched_off == 2,
          f"{[s[0] for s in sent]} {box7.switched_off}")

    # 13. Dry run touches nothing
    box8 = Sandbox()
    box8.google.out[date(2026, 12, 8)] = 50
    code, sent = box8.run(at(11, 16, 21), "--dry-run")
    check("--dry-run prints the steal but sends and saves nothing",
          code == 0 and not sent and not hw.STATE_PATH.exists() and "★ Tue, Dec 8 $50 (NEW)" in box8.log, box8.log[-400:])

    # 14. Weekend trips only: Thu/Fri/Sat out, Sun/Mon/Tue home, 2 to 4 nights
    weekend = CONFIG + 'depart_days = ["Thu", "Fri", "Sat"]\nreturn_days = ["Sun", "Mon", "Tue"]\nnights = [2, 4]\n'
    box9 = Sandbox(weekend)
    code, sent = box9.run(at(11, 21, 15))
    outs = sorted({d for direction, d, kind in box9.google.calls if direction == "out"})
    backs = sorted({d for direction, d, kind in box9.google.calls if direction == "back"})
    check("a weekend watch only prices Thu/Fri/Sat out and Sun/Mon/Tue home",
          len(outs) == 13 and {d.strftime("%a") for d in outs} == {"Thu", "Fri", "Sat"}
          and len(backs) == 14 and {d.strftime("%a") for d in backs} == {"Sun", "Mon", "Tue"}
          and backs[0] == date(2026, 12, 6) and backs[-1] == date(2027, 1, 4), f"{len(outs)} {len(backs)} {backs[:1]} {backs[-1:]}")
    check("its hello email says so", len(sent) == 1 and "It prices every Thu/Fri/Sat from Thu, Dec 3 to Thu, Dec 31"
          in sent[0][1] and "plus trips home on Sun/Mon/Tue through Mon, Jan 4, for trips of 2 to 4 nights" in sent[0][1],
          sent[0][1][:300] if sent else "nothing sent")
    box9.google.out[date(2026, 12, 12)] = 95      # Sat
    box9.google.back[date(2026, 12, 16)] = 20     # Wed: cheap, but not a day he can come home
    box9.google.back[date(2026, 12, 15)] = 80     # Tue
    code, sent = box9.run(at(11, 21, 17))
    body = sent[0][1] if sent else ""
    check("a weekend round trip pairs Sat with Tue, never with a cheaper Wednesday",
          len(sent) == 1 and "round trip for $175" in body and "Tue, Dec 15 $80" in body and "Dec 16" not in body, body[:500])

    # 15. One watch until a decision date, another from the day after
    two = (CONFIG + 'active_until = "2026-11-20"\n' + CONFIG.split("[[watch]]")[1].replace(
        'name = "NYC → Puerto Rico, December"', 'name = "December weekends"').join(["\n[[watch]]", ""])
        + 'active_from = "2026-11-21"\ndepart_days = ["Fri"]\nreturn_days = ["Mon"]\nnights = [3, 3]\n')
    box10 = Sandbox(two)
    code, sent = box10.run(at(11, 20, 15))
    check("before the decision date only the first watch runs",
          len(sent) == 1 and sent[0][0] == "✈️ Now watching: NYC → Puerto Rico, December"
          and "December weekends: starts Sat, Nov 21" in box10.log, f"{[s[0] for s in sent]} {box10.log[:200]}")
    box10.google.calls.clear()
    code, sent = box10.run(at(11, 21, 15))
    fridays = {d for direction, d, kind in box10.google.calls if direction == "out"}
    check("the day after, the second takes over by itself and nothing switches off",
          len(sent) == 1 and sent[0][0] == "✈️ Now watching: December weekends" and box10.switched_off == 0
          and all(d.strftime("%a") == "Fri" for d in fridays) and len(fridays) == 4
          and "NYC → Puerto Rico, December: ended Fri, Nov 20" in box10.log, f"{[s[0] for s in sent]} {sorted(fridays)}")
    table = hw.LATEST_PATH.read_text(encoding="utf-8")
    check("the price table shows only the watch that's running", "## December weekends" in table
          and "## NYC → Puerto Rico, December\n" not in table, table[:200])

    # 16. "Where prices stand" email at a set time
    box11 = Sandbox(CONFIG + 'summary_at = ["2026-11-19 18:00"]\nnote = "Decide on the longer trip by Nov 20."\n')
    box11.run(at(11, 19, 21))                       # 4 PM Eastern: hello email only
    code, sent = box11.run(at(11, 19, 23, 30))      # 6:30 PM Eastern
    check("it sends one price-check email once that time arrives, with your note on top",
          len(sent) == 1 and sent[0][0] == "✈️ Price check: NYC → Puerto Rico, December"
          and sent[0][1].startswith("Decide on the longer trip by Nov 20.") and "(2 nights): $310" in sent[0][1]
          and "Out $140 JFK→SJU JetBlue, 1 stop · Back $170 SJU→EWR United, nonstop" in sent[0][1], str(sent)[:500])
    code, sent = box11.run(at(11, 19, 24))
    check("and doesn't repeat it", not sent, str([s[0] for s in sent]))
    code, sent = box11.run(at(11, 19, 25), "--summary-now")
    check("--summary-now sends one on demand", len(sent) == 1 and sent[0][0].startswith("✈️ Price check"))

    # 17. A cap on searches per run spreads the work fairly
    box12 = Sandbox(CONFIG.replace("budget_seconds = 60", "budget_seconds = 60\nmax_searches_per_run = 16"))
    seen_out, seen_back, hello_at = set(), set(), None
    for i in range(8):
        box12.google.calls.clear()
        code, sent = box12.run(at(11, 16, 21) + timedelta(minutes=5 * i))
        sweeps = [c for c in box12.google.calls if c[2] == "sweep"]
        if len(sweeps) != 16:
            check("a capped run does exactly 16 searches", False, f"run {i}: {len(sweeps)}")
        seen_out |= {c[1] for c in sweeps if c[0] == "out"}
        seen_back |= {c[1] for c in sweeps if c[0] == "back"}
        if sent and hello_at is None:
            hello_at = i
    check("with 16 searches per run, every day out and home still gets priced within 40 minutes",
          len(seen_out) == 31 and len(seen_back) == 39, f"{len(seen_out)} {len(seen_back)}")
    check("and the hello email waits until nearly everything has been priced once (the 4th run)", hello_at == 3, str(hello_at))
    box12.google.calls.clear()
    box12.run(at(11, 16, 21, 45))
    kinds = [c[0] for c in box12.google.calls if c[2] == "sweep"]
    check("after that, each run goes to the days waiting longest (trips out, re-priced every run)",
          kinds.count("out") == 16, str(kinds))

    # 18. Reaching you: email when the secrets are set, otherwise a GitHub issue
    saved = {k: os.environ.pop(k, None) for k in EMAIL_KEYS}
    calls = []
    hw.github_api = lambda method, path, body=None: calls.append((method, path, body))
    hw.tell = REAL_TELL
    os.environ["GITHUB_REPOSITORY_OWNER"] = "someone"
    with contextlib.redirect_stdout(io.StringIO()):
        ok = hw.tell("🚨 Flight steal: $69", "Tue, Dec 8: $69 one way\nGoogle Flights: https://www.google.com/x?tfs=1", "<p>x</p>")
    check("with no email secrets, an alert becomes a GitHub issue assigned to the owner",
          ok and calls == [("POST", "issues", {"title": "🚨 Flight steal: $69", "assignees": ["someone"],
                                               "body": "Tue, Dec 8: \\$69 one way\n[Open in Google Flights](https://www.google.com/x?tfs=1)"})],
          str(calls))
    os.environ.update(EMAIL_FROM="a@example.com", EMAIL_APP_PASSWORD="abcd efgh", EMAIL_TO="b@example.com")
    emails = []
    hw.send_email = lambda subject, text, html: emails.append(subject)
    calls.clear()
    with contextlib.redirect_stdout(io.StringIO()):
        ok = hw.tell("subject", "text", "<p>x</p>")
    check("with email secrets it emails and opens no issue", ok and emails == ["subject"] and not calls)

    def broken(subject, text, html):
        raise OSError("connection refused")
    hw.send_email = broken
    with contextlib.redirect_stdout(io.StringIO()):
        ok = hw.tell("subject", "text", "<p>x</p>")
    check("if email fails, the alert still goes out as an issue", ok and len(calls) == 1 and calls[0][1] == "issues")

    # 19. Lining up the next check
    def chain(mode, runs, state=None, run_id="100", private=False, timer=4):
        for k in ("EMAIL_FROM", "EMAIL_APP_PASSWORD", "EMAIL_TO"):
            os.environ.pop(k, None)
        box = Sandbox()
        if state is not None:
            hw.save_state(state)
        os.environ.update(HYPERWATCH_CHAIN=mode, GITHUB_RUN_ID=run_id, GITHUB_REF_NAME="main")
        posted = []

        def api(method, path, body=None):
            if method == "GET" and path == "":
                return {"private": private}
            if method == "GET" and path.startswith("environments/"):
                if timer is None:
                    raise hw.urllib.error.HTTPError("url", 404, "Not Found", None, None)
                return {"protection_rules": [{"type": "wait_timer", "wait_timer": timer}] if timer else []}
            if method == "GET":
                return {"workflow_runs": runs}
            posted.append((path, body))
        hw.github_api = api
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            hw.main(["--next"])
        chain.log = buf.getvalue()
        return posted

    dispatch = "actions/workflows/hyperwatch.yml/dispatches"
    me = {"id": 100, "status": "in_progress"}
    check("when nothing else is waiting, a run starts its successor",
          chain("forever", [me, {"id": 99, "status": "completed"}]) == [(dispatch, {"ref": "main", "inputs": {"chain": "forever"}})])
    check("an older unfinished run doesn't count: the newest run carries the loop",
          len(chain("forever", [me, {"id": 98, "status": "in_progress"}])) == 1)
    check("when a newer check is already waiting, it starts nothing",
          chain("forever", [me, {"id": 101, "status": "waiting"}]) == [])
    check("'once' starts one more run that then stops",
          chain("once", [me]) == [(dispatch, {"ref": "main", "inputs": {"chain": "off"}})])
    check("chain off starts nothing", chain("off", [me]) == [] and chain("", [me]) == [])
    check("a finished watch stops the loop", chain("forever", [me], state={"finished": True}) == [])
    check("it won't loop in a private repo, where GitHub ignores the wait timer",
          chain("forever", [me], private=True) == [] and "this repository is private" in chain.log, chain.log)
    check("or when the pause environment has no wait timer, or doesn't exist",
          chain("forever", [me], timer=0) == [] and "has no wait timer" in chain.log
          and chain("forever", [me], timer=None) == [] and 'there is no "pause" environment' in chain.log, chain.log)
    just_now = hw.iso(hw.utc_now())
    burst = [me] + [{"id": 90 + i, "status": "completed", "run_started_at": just_now} for i in range(6)]
    check("and it stops if checks ever start running back to back",
          chain("forever", burst) == [] and "started in the last 10 minutes" in chain.log, chain.log)
    check("'once' needs no pause (it can't loop)", len(chain("once", [me], private=True, timer=None)) == 1)

    # 20. The test message
    box13 = Sandbox()
    code, sent = box13.run(at(11, 16, 21), "--test-notification")
    check("--test-notification sends one test message and prices nothing",
          code == 0 and len(sent) == 1 and sent[0][0] == "[TEST] Hyper Watch can reach you" and not box13.google.calls)
    for k, v in saved.items():
        os.environ.pop(k, None)
        if v is not None:
            os.environ[k] = v

    if PROBLEMS:
        print(f"\nSelf-test FAILED ({len(PROBLEMS)}): " + "; ".join(PROBLEMS))
        return 1
    print("\nSelf-test passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
