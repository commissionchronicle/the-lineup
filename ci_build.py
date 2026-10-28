#!/usr/bin/env python3
"""
ci_build.py - CI generator for The Lineup (GTA RP Event Magazine).

Runs inside GitHub Actions on the commissionchronicle/the-lineup repo:
fetches the public "GTA RP Notice Board" Google Calendar through its
public iCal feed (the runner has no local calendar CLI), expands
recurrences with a stdlib-only engine, renders the same magazine as the
local build-lineup-site.py (host pages, marquee, countdowns, Times
toggle, date dividers), substitutes the artwork data URIs from the text
file assets-inline.json (the repo cannot hold binary assets), and writes
a single self-contained index.html next to this file. The workflow
commits index.html back to main only when it changed.

Rendering, template surgery and page features are shared verbatim with
build-lineup-site.py; only the data source and the asset-inlining step
differ. Window: today (America/Los_Angeles) through +45 days.

Standing desk rule: nothing about the user's own family/crew ever appears
in a desk product - any calendar item mentioning it is excluded here (the
exclusion term is assembled in code so it never sits in this file).

Usage:  python3 ci_build.py     (LINEUP_ICS_FILE / LINEUP_ICS_URL override
                                 the feed source, for local parity tests)
"""

import html
import json
import re
import os
import urllib.request
import sys
import time
from collections import Counter
from datetime import datetime, time as dt_time, timedelta, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

PT = ZoneInfo("America/Los_Angeles")
CAL_ID = "39853696cb7137bfff96f73bdf86e3328b0584f91e28e3428d536f8523fa24d5@group.calendar.google.com"
WINDOW_DAYS = 45

HERE = Path(__file__).resolve().parent
TEMPLATE = HERE / "template.html"
ASSETS_JSON = HERE / "assets-inline.json"
OUT_HTML = HERE / "index.html"

DOW3 = ["MON", "TUE", "WED", "THU", "FRI", "SAT", "SUN"]
MON3 = ["JAN", "FEB", "MAR", "APR", "MAY", "JUN",
        "JUL", "AUG", "SEP", "OCT", "NOV", "DEC"]

LAUNCH_WORDS = ("launch", "opening", "inauguration", "inauguração", "grand opening",
                "estreia", "abertura", "server opens", "city opens")
CONTEST_WORDS = ("contest", "race", "tournament", "best build", "corrida", "competition")
PLACE_HINTS = ("benny", "los santos", "yankton", "lsia", "banco", "bank of",
               "jet street", "airport", "runway")


def esc(s):
    """HTML-escape a text value that will be injected via innerHTML."""
    return html.escape(str(s), quote=False)


def fmt_clock(dt):
    """datetime -> '3:00 PM'"""
    return dt.strftime("%I:%M %p").lstrip("0")


def fmt_range(start, end, zoned):
    """PT start/end -> '6:00–7:00 PM PT' / '8:00 PM' (bare when zone unlisted)."""
    suffix = " PT" if zoned else ""
    if end is None or end <= start or (end - start) >= timedelta(hours=20):
        return fmt_clock(start) + suffix
    s, e = fmt_clock(start), fmt_clock(end)
    if s[-2:] == e[-2:]:  # same meridiem: '6:00–7:00 PM'
        return s[:-2] + "–" + e + suffix
    return s + "–" + e + suffix


# --- Public ICS feed (CI data source) -------------------------------------
# The GitHub Actions runner has no hatch_gws_cli, so the CI build reads the
# calendar's public iCal feed (no key needed) and expands recurrences with
# a small stdlib-only engine, producing the same item dicts the Google API
# list call returns (summary / description / start / end / recurringEventId).
ICS_URL = ("https://calendar.google.com/calendar/ical/"
           "39853696cb7137bfff96f73bdf86e3328b0584f91e28e3428d536f8523fa24d5"
           "%40group.calendar.google.com/public/basic.ics")

_WEEKDAYS = {"MO": 0, "TU": 1, "WE": 2, "TH": 3, "FR": 4, "SA": 5, "SU": 6}


def _ics_unfold(text):
    lines = []
    for raw in text.replace("\r\n", "\n").replace("\r", "\n").split("\n"):
        if raw[:1] in (" ", "\t") and lines:
            lines[-1] += raw[1:]
        elif raw:
            lines.append(raw)
    return lines


def _ics_unescape(val):
    out, i = [], 0
    while i < len(val):
        if val[i] == "\\" and i + 1 < len(val):
            n = val[i + 1]
            out.append("\n" if n in "nN" else n)
            i += 2
        else:
            out.append(val[i])
            i += 1
    return "".join(out)


def _ics_prop(line):
    """'DTSTART;TZID=America/Sao_Paulo:20261010T200000' -> (name, params, value)."""
    head, _, value = line.partition(":")
    parts = head.split(";")
    params = {}
    for p in parts[1:]:
        k, _, v = p.partition("=")
        params[k.upper()] = v.strip('"')
    return parts[0].upper(), params, value


def _ics_components(text):
    """-> (calendar-level props dict, [vevent prop lists])."""
    cal_props, events, stack, cur = {}, [], [], None
    for line in _ics_unfold(text):
        name, params, value = _ics_prop(line)
        if name == "BEGIN":
            stack.append(value.upper())
            if value.upper() == "VEVENT":
                cur = []
            continue
        if name == "END":
            if value.upper() == "VEVENT" and cur is not None:
                events.append(cur)
                cur = None
            if stack:
                stack.pop()
            continue
        if cur is not None and stack and stack[-1] == "VEVENT":
            cur.append((name, params, value))
        elif stack == ["VCALENDAR"]:
            cal_props[name] = value
    return cal_props, events


def _ics_dt(params, value, cal_tz):
    """-> ('date', date) or ('dt', aware datetime)."""
    v = value.strip()
    if params.get("VALUE", "").upper() == "DATE" or re.fullmatch(r"\d{8}", v):
        return "date", datetime.strptime(v, "%Y%m%d").date()
    if v.endswith("Z"):
        return "dt", datetime.strptime(v, "%Y%m%dT%H%M%SZ").replace(
            tzinfo=timezone.utc)
    naive = datetime.strptime(v, "%Y%m%dT%H%M%S")
    tz = None
    tzid = params.get("TZID")
    if tzid:
        try:
            tz = ZoneInfo(tzid)
        except Exception:
            print(f"WARNING: unknown TZID {tzid!r} - using calendar zone",
                  file=sys.stderr)
    return "dt", naive.replace(tzinfo=tz or cal_tz)


def _rrule_until(raw, tz_hint):
    raw = raw.strip()
    if re.fullmatch(r"\d{8}", raw):
        return "date", datetime.strptime(raw, "%Y%m%d").date()
    if raw.endswith("Z"):
        return "dt", datetime.strptime(raw, "%Y%m%dT%H%M%SZ").replace(
            tzinfo=timezone.utc)
    return "dt", datetime.strptime(raw, "%Y%m%dT%H%M%S").replace(
        tzinfo=tz_hint or PT)


def _month_days(year, month, start_day, byday, bymonthday):
    import calendar as _cal
    ndays = _cal.monthrange(year, month)[1]
    days = set()
    if bymonthday:
        for md in bymonthday:
            dd = md if md > 0 else ndays + md + 1
            if 1 <= dd <= ndays:
                days.add(dd)
    elif byday:
        for ordinal, wd in byday:
            matches = [dd for dd in range(1, ndays + 1)
                       if datetime(year, month, dd).weekday() == wd]
            if ordinal is None:
                days.update(matches)
            elif 0 < ordinal <= len(matches):
                days.add(matches[ordinal - 1])
            elif ordinal < 0 and -ordinal <= len(matches):
                days.add(matches[ordinal])
    elif start_day <= ndays:
        days.add(start_day)
    return sorted(days)


def _expand_rrule(rrule_raw, kind, dtstart, gen_lo, gen_hi):
    """Instance starts (same kind/payload as dtstart) with instants in
    [gen_lo, gen_hi] (aware datetimes; for all-day series, their dates).
    Local wall-clock arithmetic, so a weekly 7 PM stays 7 PM across DST.
    Supports FREQ=DAILY/WEEKLY/MONTHLY/YEARLY with INTERVAL, COUNT, UNTIL,
    BYDAY, BYMONTH, BYMONTHDAY. The calendar's own series are WEEKLY."""
    rp = {}
    for kv in rrule_raw.split(";"):
        k, _, v = kv.partition("=")
        rp[k.upper()] = v
    freq = rp.get("FREQ", "").upper()
    interval = max(1, int(rp.get("INTERVAL", "1")))
    count_max = int(rp["COUNT"]) if "COUNT" in rp else None
    until = (_rrule_until(rp["UNTIL"], dtstart.tzinfo if kind == "dt" else None)
             if "UNTIL" in rp else None)
    byday = []
    for tok in rp.get("BYDAY", "").split(","):
        tok = tok.strip()
        if not tok:
            continue
        m = re.fullmatch(r"([+-]?\d{1,2})?([A-Z]{2})", tok)
        if m:
            byday.append((int(m.group(1)) if m.group(1) else None,
                          _WEEKDAYS[m.group(2)]))
    bymonth = sorted({int(x) for x in rp.get("BYMONTH", "").split(",") if x.strip()})
    bymonthday = {int(x) for x in rp.get("BYMONTHDAY", "").split(",") if x.strip()}
    wkst = _WEEKDAYS.get(rp.get("WKST", "MO").upper(), 0)

    if kind == "date":
        start_d = dtstart
        lo_d, hi_d = gen_lo.date(), gen_hi.date()

        def combine(d):
            return d

        def naive_of(p):
            return p

        def past_until(p):
            if until is None:
                return False
            uk, uv = until
            return p > uv if uk == "date" else p > uv.date()
    else:
        start_d = dtstart.date()
        tod = dtstart.timetz().replace(tzinfo=None)
        tz = dtstart.tzinfo
        lo_d, hi_d = gen_lo.date(), gen_hi.date()

        def combine(d):
            return datetime.combine(d, tod).replace(tzinfo=tz)

        def naive_of(p):
            return p.replace(tzinfo=None)

        def past_until(p):
            if until is None:
                return False
            uk, uv = until
            return naive_of(p).date() > uv if uk == "date" else p > uv

    start_naive = datetime.combine(start_d, tod) if kind == "dt" else None
    results, produced = [], 0

    def accept(cand):
        """cand: date (all-day) or aware datetime. -> False when done."""
        nonlocal produced
        nv = cand if kind == "date" else naive_of(cand)
        if kind == "dt" and nv < start_naive:
            return True
        if kind == "date" and cand < start_d:
            return True
        if past_until(cand):
            return False
        produced += 1
        if count_max is not None and produced > count_max:
            return False
        cd = cand if kind == "date" else cand.date()
        if lo_d <= cd <= hi_d:
            if kind == "date" or (gen_lo <= cand <= gen_hi):
                results.append(cand)
        return True

    import calendar as _cal  # noqa: F401  (used by _month_days already)
    if freq == "WEEKLY":
        days = sorted({wd for _, wd in byday}) or [start_d.weekday()]
        first_ws = start_d - timedelta(days=(start_d.weekday() - wkst) % 7)
        w = 0
        while True:
            ws = first_ws + timedelta(weeks=w * interval)
            if ws > hi_d:
                break
            for wd in days:
                cd = ws + timedelta(days=(wd - wkst) % 7)
                if not accept(combine(cd)):
                    return results
            w += 1
            if w > 5200:
                break
    elif freq == "DAILY":
        want = {wd for _, wd in byday}
        d, steps = start_d, 0
        while d <= hi_d and steps < 20000:
            if not want or d.weekday() in want:
                if not accept(combine(d)):
                    return results
            d += timedelta(days=interval)
            steps += 1
    elif freq in ("MONTHLY", "YEARLY"):
        months = []
        if freq == "MONTHLY":
            y, m = start_d.year, start_d.month
            while (y, m) <= (hi_d.year, hi_d.month):
                months.append((y, m))
                m += interval
                y, m = y + (m - 1) // 12, (m - 1) % 12 + 1
        else:
            for y in range(start_d.year, hi_d.year + 1, interval):
                for m in (bymonth or [start_d.month]):
                    months.append((y, m))
            months.sort()
        for (y, m) in months:
            for dd in _month_days(y, m, start_d.day, byday, bymonthday):
                cd = datetime(y, m, dd).date()
                if freq == "YEARLY" and not bymonth and cd < start_d and (y, m) == (start_d.year, start_d.month):
                    continue
                if not accept(combine(cd)):
                    return results
    else:
        print(f"WARNING: unsupported RRULE FREQ {freq!r} - single instance only",
              file=sys.stderr)
        accept(combine(start_d))
    return results


def pull_calendar(today):
    """Public-ICS equivalent of the old API pull: item dicts covering
    [today 00:00 PT, today+WINDOW_DAYS 23:59:59 PT] after parse filtering."""
    src = os.environ.get("LINEUP_ICS_FILE")
    if src:
        text = Path(src).read_text(encoding="utf-8")
    else:
        url = os.environ.get("LINEUP_ICS_URL", ICS_URL)
        req = urllib.request.Request(url, headers={"User-Agent": "lineup-ci/1.0"})
        with urllib.request.urlopen(req, timeout=60) as fh:
            text = fh.read().decode("utf-8")
    cal_props, vevents = _ics_components(text)
    try:
        cal_tz = ZoneInfo(cal_props.get("X-WR-TIMEZONE", "America/Los_Angeles"))
    except Exception:
        cal_tz = PT
    win_lo = datetime.combine(today - timedelta(days=10), dt_time.min, PT)
    win_hi = datetime.combine(today + timedelta(days=WINDOW_DAYS + 15),
                              dt_time.max, PT)

    def key_of(kind, payload):
        return payload.isoformat() if kind == "date" else int(payload.timestamp())

    by_uid = {}
    for props in vevents:
        d = {}
        for name, params, value in props:
            d.setdefault(name, []).append((params, value))
        uid = d.get("UID", [(None, "")])[0][1]
        by_uid.setdefault(uid, []).append(d)

    items = []
    for uid, group in by_uid.items():
        masters = [d for d in group if "RRULE" in d]
        others = [d for d in group if "RRULE" not in d]
        excl = set()
        for d in group:
            for params, value in d.get("EXDATE", []):
                for piece in value.split(","):
                    if piece.strip():
                        k, p = _ics_dt(params, piece.strip(), cal_tz)
                        excl.add(key_of(k, p))
        for d in others:
            if "RECURRENCE-ID" in d:
                params, value = d["RECURRENCE-ID"][0]
                k, p = _ics_dt(params, value, cal_tz)
                excl.add(key_of(k, p))

        def emit(d, kind, s, e, recurring):
            if (d.get("STATUS", [(None, "")])[0][1] or "").upper() == "CANCELLED":
                return
            item = {
                "summary": _ics_unescape(d.get("SUMMARY", [(None, "")])[0][1]).strip(),
                "description": _ics_unescape(d.get("DESCRIPTION", [(None, "")])[0][1]),
            }
            if kind == "date":
                item["start"] = {"date": s.isoformat()}
                item["end"] = {"date": e.isoformat()}
            else:
                item["start"] = {"dateTime": s.isoformat()}
                item["end"] = {"dateTime": e.isoformat()}
            if recurring:
                item["recurringEventId"] = uid
            items.append(item)

        for d in others:
            params, value = d["DTSTART"][0]
            kind, s = _ics_dt(params, value, cal_tz)
            if "DTEND" in d:
                _, e = _ics_dt(d["DTEND"][0][0], d["DTEND"][0][1], cal_tz)
            else:
                e = s
            emit(d, kind, s, e, recurring=("RECURRENCE-ID" in d))
        for d in masters:
            params, value = d["DTSTART"][0]
            kind, s = _ics_dt(params, value, cal_tz)
            if "DTEND" in d:
                _, e0 = _ics_dt(d["DTEND"][0][0], d["DTEND"][0][1], cal_tz)
                dur = e0 - s
            else:
                dur = timedelta(0)
            for inst in _expand_rrule(d["RRULE"][0][1], kind, s, win_lo, win_hi):
                if key_of(kind, inst) in excl:
                    continue
                emit(d, kind, inst, inst + dur, recurring=True)
            for params2, value2 in d.get("RDATE", []):
                for piece in value2.split(","):
                    if piece.strip():
                        k2, p2 = _ics_dt(params2, piece.strip(), cal_tz)
                        if k2 == kind and key_of(k2, p2) not in excl:
                            emit(d, kind, p2, p2 + dur, recurring=True)
    return items


def parse_event(item, today):
    """One calendar item -> magazine record (or None to skip)."""
    summary = item.get("summary", "").strip()
    desc = item.get("description", "") or ""
    blob = (summary + "\n" + desc).lower()
    if "tej" + "ada" in blob:  # standing rule: never in a desk product
        return None

    # Title: "<Event name> — @<handle>" (the name itself may contain dashes)
    m = re.match(r"^(?P<name>.*?)\s+—\s+(?P<handle>@\S+)\s*$", summary)
    if m:
        name, title_handle = m.group("name").strip(), m.group("handle")
    else:
        name, title_handle = summary, None

    lines = [ln.strip() for ln in desc.split("\n")]
    first = lines[0] if lines else ""
    segs = [s.strip() for s in first.split("·")]
    host_raw = ""
    if segs and segs[0].lower().startswith("host:"):
        host_raw = segs[0][5:].strip()
    hm = re.search(r"@\S+", host_raw)
    host = hm.group(0) if hm else (host_raw or title_handle or "")
    if not host.startswith("@") and title_handle:
        host = title_handle

    platform = segs[1] if len(segs) > 1 else ""
    if "platform not listed" in platform.lower():
        platform = "See flyer"
    if "every " in platform.lower() or "didn't list" in platform.lower():
        platform = "Weekly meetup" if item.get("recurringEventId") else "See flyer"

    as_posted = segs[2] if len(segs) > 2 else ""
    extras = [s for s in segs[3:] if s]
    for ln in lines[1:]:
        low = ln.lower()
        if not ln or "didn't list time zone" in low or "instagram.com" in low:
            continue
        if low.startswith("source:"):
            continue
        extras.append(ln)
    extras = [e for e in extras if "time tba" not in e.lower()]

    no_tz = "didn't list time zone" in desc.lower()
    url_m = re.search(r"https://www\.instagram\.com/(?:p|reel)/[^\s\"']+", desc)
    post_url = url_m.group(0) if url_m else ""

    start, end = item.get("start", {}), item.get("end", {})
    if "dateTime" in start:
        sdt = datetime.fromisoformat(start["dateTime"]).astimezone(PT)
        edt = (datetime.fromisoformat(end["dateTime"]).astimezone(PT)
               if "dateTime" in end else None)
        day = sdt.date()
        time_disp = fmt_range(sdt, edt, zoned=not no_tz)
        sort_key = (0, sdt)
    else:
        day = datetime.fromisoformat(start["date"]).date()
        sdt = edt = None
        time_disp = "TIME TBA"
        sort_key = (1, datetime.combine(day, datetime.min.time(), PT))
    if day < today or day > today + timedelta(days=WINDOW_DAYS):
        return None

    # Exact start/end instants for the live countdown + .ics export. The
    # calendar record already embodies the zone rule (no-zone events were
    # stored on PT by the watch; explicit-zone events keep their offset),
    # so the epoch of the stored dateTime is the true instant either way.
    start_ts = int(sdt.timestamp()) if sdt is not None else None
    end_ts = int(edt.timestamp()) if edt is not None else None

    # Categories for the filters / card stripe
    text = (name + " " + platform).lower()
    cats = set()
    if "halloween" in text or "spooky" in text:
        cats.add("halloween")
    if any(w in text for w in LAUNCH_WORDS):
        cats.add("launch")
    if any(w in text for w in CONTEST_WORDS):
        cats.add("contest")
    if "fivem" in platform.lower():
        cats.add("fivem")
    if any(w in platform.lower() for w in ("playstation", "ps5", "ps4", "psn", "xbox")):
        cats.add("console")
    if "meet" in text or "carmeet" in text or "encontro" in text:
        cats.add("meet")
    if "launch" in cats:
        order = ["launch", "halloween", "contest", "fivem", "console", "meet"]
    else:
        order = ["meet", "halloween", "contest", "fivem", "console"]
    cats = [c for c in order if c in cats] or ["meet"]
    primary = cats[0]

    # Where line: the as-posted time for timed events; a place hint if one is
    # in the record for all-day events; otherwise the flyer holds it.
    place = next((e for e in extras if any(h in e.lower() for h in PLACE_HINTS)), "")
    if sdt is not None:
        where = as_posted[:44] if as_posted and "time tba" not in as_posted.lower() \
            else "Location on flyer"
    else:
        where = place[:44] if place else "Location on flyer"

    # One-line description, assembled only from facts in the record
    if primary == "launch":
        body = "A new city/server opens its gates — launch listing from the Notice Board calendar."
    elif primary == "contest":
        body = "Contest / race listing from the Notice Board calendar — see the flyer post for the rules."
    elif primary == "meet":
        body = "On the Notice Board calendar — see the flyer post for the meet point."
    else:
        body = "Listed on the Notice Board calendar — full details on the flyer post."
    if extras:
        extra_txt = " · ".join(extras)
        body += " " + extra_txt[0].upper() + extra_txt[1:] + "."
    if no_tz:
        body += " Organizer didn't list a time zone."
    if sdt is None:
        body += " Time TBA — watch the host for the hour."
    if item.get("recurringEventId"):
        body += " Weekly regular."

    return {
        "day": day, "date_key": f"{DOW3[day.weekday()]} {MON3[day.month - 1]} {day.day}",
        "time": time_disp, "title": name, "host": host, "where": where,
        "platform": platform, "desc": body, "cats": cats, "post": post_url,
        "as_posted": as_posted, "extras": extras, "sort": sort_key,
        "recurring": bool(item.get("recurringEventId")),
        "start_ts": start_ts, "end_ts": end_ts, "day_iso": day.isoformat(),
        "no_tz": no_tz, "summary": summary,
    }


def ics_time_note(e):
    """Time-as-posted line for the .ics description (raw text, not HTML)."""
    if e["start_ts"] is not None:
        note = "Time as posted: " + (e["as_posted"] or e["time"])
    else:
        note = "Time TBA — see the flyer post for the hour"
    if e["no_tz"]:
        note += " (organizer didn't list time zone)"
    return note


def day_label(day):
    """'Fri Oct 23' style short label."""
    return f"{DOW3[day.weekday()].title()} {MON3[day.month - 1].title()} {day.day}"


def day_full(day):
    return day.strftime("%A, %B ") + str(day.day)


def replace_block(text, start_marker, end_marker, new_block):
    i = text.index(start_marker)
    j = text.index(end_marker, i) + len(end_marker)
    return text[:i] + new_block + text[j:]


def event_order_key(e):
    """Epoch key for front-of-magazine ordering: the event's start instant;
    all-day / time-TBA events sort at the end of their day (23:59 PT)."""
    if e["start_ts"] is not None:
        return e["start_ts"]
    return int(datetime.combine(e["day"], dt_time(23, 59), PT).timestamp())


# --- Cover overlay (2026-10-28) -------------------------------------------
# Page 1 is a swappable PHOTO (assets-inline key "cover") with the
# Newsstand cover's words as a live HTML overlay: the words below are
# computed from the same event data as the rest of the magazine, so they
# refresh every build while the photo only changes when the asset does.
# Layout/type replicate the approved mock (newsstand-cover-mock-v5.png):
# heavy condensed sans heads, monospace dates, Pitch Black / Cyber
# Magenta / Toxic Green / Neon Cyan (CSS lives with .cover-overlay in
# template.html). COVER_EDITION is the chip that belongs to the PHOTO,
# not the week — swap it when the cover asset changes.
COVER_EDITION = "HALLOWEEN EDITION"
COVER_WEEK_DAYS = 7        # cover week = today PT through today + 6
COVER_OPENINGS_DAYS = 30   # Server Watch horizon past the cover week

_OPENING_TAILS = ("grand opening", "server opening", "server inauguration",
                  "inauguration", "reopening", "reabertura", "abertura",
                  "opening", "launch", "estreia")
_BRAND_TAILS = ("car meet", "carmeet", "meetup", "meet")


def _strip_tails(name, tails):
    """Repeatedly strip trailing phrases ('Paradise RP Launch' -> 'Paradise RP')."""
    changed = True
    while changed:
        changed = False
        low = name.lower()
        for tail in tails:
            if low.endswith(tail) and len(name) > len(tail):
                name = name[: -len(tail)].strip(" -–—·,")
                changed = True
                break
    return name


def _cover_opening(e):
    """True when the event reads as a server/city opening or reopening."""
    if "launch" in e["cats"]:
        return True
    t = e["title"].lower()
    return any(w in t for w in LAUNCH_WORDS) or "reopen" in t


def _opening_name(title):
    """Short server name for the Server Watch sub-line."""
    name = _strip_tails(title.split(" — ")[0].strip(), _OPENING_TAILS)
    return name or title


def _host_brand(host_events, handle):
    """Cover display name for a host: their most-listed event title with
    the generic meet suffixes stripped ('Clean Culture Meet' -> 'Clean
    Culture'); falls back to a prettified handle."""
    title = Counter(e["title"] for e in host_events).most_common(1)[0][0]
    name = _strip_tails(title.split(" — ")[0].strip(), _BRAND_TAILS)
    if not name or len(name) < 3:
        name = re.sub(r"[._]+", " ", handle.lstrip("@")).strip().title()
    return name


def cover_values(events, today):
    """The words on this build's cover, computed from the event data."""
    wk_end = today + timedelta(days=COVER_WEEK_DAYS - 1)
    week = [e for e in events if today <= e["day"] <= wk_end]
    vals = {"dates": (f"{MON3[today.month - 1]} {today.day} – "
                      f"{MON3[wk_end.month - 1]} {wk_end.day}, {wk_end.year}"),
            "edition": COVER_EDITION, "week": week, "openings": []}
    if not week:
        return vals
    vals["count"] = len(week)
    by_day = Counter(e["day"] for e in week)
    big_day, big_n = None, -1
    for d in sorted(by_day):
        if by_day[d] > big_n:
            big_day, big_n = d, by_day[d]
    vals["big_day"], vals["big_n"] = big_day, big_n
    horizon = wk_end + timedelta(days=COVER_OPENINGS_DAYS)
    ops = [e for e in events
           if wk_end < e["day"] <= horizon and _cover_opening(e)]
    ops.sort(key=lambda e: (e["day"], event_order_key(e), e["title"]))
    vals["openings"] = ops
    by_host = {}
    for e in week:
        by_host.setdefault(e["host"], []).append(e)
    best = None
    for handle, hev in by_host.items():
        key = (-len(hev), min(event_order_key(e) for e in hev),
               handle.lower())
        if best is None or key < best[0]:
            best = (key, handle, hev)
    _, vals["host_handle"], vals["host_events"] = best
    vals["host_days"] = sorted({e["day"] for e in vals["host_events"]})
    vals["host_brand"] = _host_brand(vals["host_events"], vals["host_handle"])
    return vals


def cover_overlay_html(v):
    """Inner HTML for .cover-overlay (the template's __COVER_OVERLAY__)."""
    parts = ['<div class="cov-scrims" aria-hidden="true"></div>']
    parts.append(
        f'<div class="cov-strip"><span>{esc(v["dates"])}</span></div>'
        '<div class="cov-tags"><span class="cov-chip">GTA RP EVENT MAGAZINE</span>'
        f'<span class="cov-chip">{esc(v["edition"])}</span>'
        '<span class="cov-loc">LOS SANTOS</span></div>'
        '<div class="cov-mast">THE LINEUP</div><div class="cov-rule"></div>')
    if v.get("count"):
        parts.append(
            '<div class="cov-line cov-a"><p class="cov-kick cov-cyan">'
            'THIS WEEK’S FULL BOARD</p>'
            f'<p class="cov-head"><span class="cov-mag">{v["count"]}</span> '
            'MEETS<br>INSIDE!</p>'
            '<p class="cov-sub">Every meet, opening &amp; launch, listed</p></div>')
        d = v["big_day"]
        kick = f'{DOW3[d.weekday()]} · {MON3[d.month - 1]} {d.day}'
        if (d.month, d.day) == (10, 31):
            h1, h1c = "HALLOWEEN", "cov-mag"
        else:
            h1, h1c = d.strftime("%A").upper(), "cov-wht"
        n = v["big_n"]
        parts.append(
            f'<div class="cov-line cov-b"><p class="cov-kick cov-mag">{esc(kick)}</p>'
            f'<p class="cov-head"><span class="{h1c}">{esc(h1)}</span><br>NIGHT</p>'
            f'<p class="cov-sub">{n} event{"s" if n != 1 else ""} — '
            'the week’s biggest night</p></div>')
    ops = v.get("openings") or []
    if ops:
        month = ops[0]["day"].strftime("%B").upper()
        names = " · ".join(esc(_opening_name(e["title"])) for e in ops[:3])
        if len(ops) > 3:
            names += " + more"
        parts.append(
            '<div class="cov-line cov-c"><p class="cov-kick cov-toxic">'
            'PLUS — SERVER WATCH</p>'
            f'<p class="cov-head">EVERY <span class="cov-toxic">{month}</span>'
            '<br>SERVER OPENING</p>'
            f'<p class="cov-sub">{names}</p></div>')
    if v.get("count"):
        pat = " + ".join(DOW3[d.weekday()].title() for d in v["host_days"])
        word = "DOUBLEHEADER" if len(v["host_days"]) == 2 else "WEEK"
        parts.append(
            '<div class="cov-line cov-d"><p class="cov-kick cov-cyan">'
            'HOST SPOTLIGHT</p>'
            f'<p class="cov-head">{esc(v["host_brand"].upper())}’S<br>'
            f'<span class="cov-mag">{word}</span></p>'
            f'<p class="cov-sub cov-mono">{esc(pat)} meets · '
            f'{esc(v["host_handle"])}</p></div>')
    parts.append(
        '<div class="cov-foot"><div class="cov-barcode" aria-hidden="true">'
        '<i></i></div><p class="cov-free">FREE · OUT EVERY THURSDAY</p>'
        '<p class="cov-handle">@gtarpnoticeboard</p></div>')
    return "".join(parts)


# --- Organizer flyers: REMOVED 2026-10-25 at Kani's direction --------------
# The fetched-flyer figures never sat right in the card box, so the
# magazine is back to link-only cards (the "Flyer post" chip). The build
# still leaves a flyers/ folder in the repo holding only a .gitkeep
# placeholder: the Actions commit step runs `git add index.html flyers`,
# which fails if the folder disappears. Any *.jpg sitting in the checkout
# is deleted here so the removal lands in the bot's commit.
FLYERS_DIR = HERE / "flyers"


def clear_flyers():
    """Leave flyers/ containing only .gitkeep (see note above)."""
    try:
        FLYERS_DIR.mkdir(exist_ok=True)
        n_removed = 0
        for f in FLYERS_DIR.glob("*.jpg"):
            f.unlink()
            n_removed += 1
        keep = FLYERS_DIR / ".gitkeep"
        if not keep.exists():
            keep.write_text("", encoding="utf-8")
        if n_removed:
            print(f"flyers : removed {n_removed} stale flyer image(s) - "
                  "flyers/ now holds only .gitkeep")
        else:
            print("flyers : link-only edition - flyers/ holds only .gitkeep")
    except Exception as exc:
        print(f"flyers : cleanup failed ({exc!r}) - continuing link-only")


# --- Live countdown + Add to Calendar (injected into the template) -------
# The countdown chip and the .ics button ride in each card's .meta row, in
# the same pill language as the host / flyer chips. Countdown state is
# computed in the visitor's browser from the baked epoch start; time-TBA
# (all-day) events get no countdown and an all-day DATE-form .ics.
CD_CSS = """
/* Countdown + add-to-calendar chips (generator-injected) */
.meta .cd{color:var(--amber-hi);border-color:rgba(251,191,36,.55);background:rgba(251,191,36,.07)}
.meta .cd.soon{color:var(--rose-hi);border-color:rgba(251,113,133,.6);background:rgba(251,113,133,.1);box-shadow:0 0 10px rgba(251,113,133,.35)}
.meta .cd.live{color:#14092e;background:var(--cyan);border-color:var(--cyan);box-shadow:0 0 12px rgba(34,211,238,.55);font-weight:700}
.meta button.cal-btn{font-family:var(--mono);font-size:11px;letter-spacing:.04em;text-transform:uppercase;border:1px solid rgba(167,139,250,.55);border-radius:999px;padding:4px 9px;color:var(--violet-hi);background:rgba(167,139,250,.08);cursor:pointer}
.meta button.cal-btn:hover{border-color:var(--violet);color:#ede9fe;box-shadow:0 0 10px rgba(167,139,250,.45)}
.feat-meta{margin-top:12px}"""

CD_JS = r"""/* Live countdown + Add to Calendar — injected by build-lineup-site.py */
function cdState(e){
  if(!e.start) return null;
  var now=Date.now()/1000, d=e.start-now;
  if(d>86400) return {t:'in '+Math.floor(d/86400)+'d '+Math.floor((d%86400)/3600)+'h', c:''};
  if(d>=3600) return {t:'in '+Math.floor(d/3600)+'h '+Math.floor((d%3600)/60)+'m', c:''};
  if(d>0) return {t:'STARTING SOON \u00b7 '+Math.max(1,Math.round(d/60))+'m', c:' soon'};
  if(now<=e.start+10800) return {t:'LIVE NOW', c:' live'};
  return {t:'', c:''};
}
function cdChip(e){
  var s=cdState(e); if(!s) return '';
  return '<span class="cd'+s.c+'" data-ei="'+EVENTS.indexOf(e)+'"'+(s.t?'':' style="display:none"')+'>'+s.t+'</span>';
}
function calBtn(e){
  return '<button type="button" class="cal-btn" data-ei="'+EVENTS.indexOf(e)+'" aria-label="Add this event to your calendar">+ Calendar</button>';
}
function tickCD(){
  document.querySelectorAll('.cd').forEach(function(el){
    var e=EVENTS[+el.getAttribute('data-ei')]; if(!e) return;
    var s=cdState(e); if(!s) return;
    el.textContent=s.t;
    el.className='cd'+s.c;
    el.style.display=s.t?'':'none';
  });
}
function icsEsc(s){return String(s==null?'':s).replace(/\\/g,'\\\\').replace(/;/g,'\\;').replace(/,/g,'\\,').replace(/\r?\n/g,'\\n')}
function icsFold(line){var o='';while(line.length>73){o+=line.slice(0,73)+'\r\n ';line=line.slice(73)}return o+line}
function icsPad(n){return (n<10?'0':'')+n}
function icsUTC(ts){var d=new Date(ts*1000);return d.getUTCFullYear()+icsPad(d.getUTCMonth()+1)+icsPad(d.getUTCDate())+'T'+icsPad(d.getUTCHours())+icsPad(d.getUTCMinutes())+icsPad(d.getUTCSeconds())+'Z'}
function icsDay(dayiso,plus){var p=dayiso.split('-');var d=new Date(Date.UTC(+p[0],+p[1]-1,+p[2]+(plus||0)));return d.getUTCFullYear()+icsPad(d.getUTCMonth()+1)+icsPad(d.getUTCDate())}
function dlICS(e){
  var ic=e.ics||{};
  var lines=['BEGIN:VCALENDAR','VERSION:2.0','PRODID:-//The Lineup//GTA RP Events//EN','CALSCALE:GREGORIAN','METHOD:PUBLISH','BEGIN:VEVENT'];
  lines.push('UID:lineup-'+(e.start||e.dayiso)+'-'+String(ic.t||e.title).replace(/[^A-Za-z0-9]+/g,'').slice(0,24)+'@commissionchronicle.github.io');
  lines.push('DTSTAMP:'+icsUTC(Math.floor(Date.now()/1000)));
  if(e.start){lines.push('DTSTART:'+icsUTC(e.start));lines.push('DTEND:'+icsUTC((e.end&&e.end>e.start)?e.end:e.start+3600));}
  else{lines.push('DTSTART;VALUE=DATE:'+icsDay(e.dayiso,0));lines.push('DTEND;VALUE=DATE:'+icsDay(e.dayiso,1));}
  lines.push('SUMMARY:'+icsEsc(ic.t||e.title));
  var dl=[];
  if(ic.h)dl.push('Host: '+ic.h);
  if(ic.p)dl.push('Platform: '+ic.p);
  if(ic.ap)dl.push(ic.ap);
  if(ic.u)dl.push('Flyer post: '+ic.u);
  if(dl.length)lines.push('DESCRIPTION:'+icsEsc(dl.join('\n')));
  if(ic.u)lines.push('URL:'+ic.u);
  lines.push('END:VEVENT','END:VCALENDAR');
  var text=lines.map(icsFold).join('\r\n')+'\r\n';
  var blob=new Blob([text],{type:'text/calendar;charset=utf-8'});
  var a=document.createElement('a');
  a.href=URL.createObjectURL(blob);
  a.download=(String(ic.t||'event').replace(/[^A-Za-z0-9]+/g,'-').replace(/^-+|-+$/g,'').slice(0,48)||'event')+'.ics';
  document.body.appendChild(a);a.click();
  setTimeout(function(){URL.revokeObjectURL(a.href);if(a.parentNode)a.parentNode.removeChild(a)},400);
}
document.addEventListener('click',function(ev){
  var b=ev.target&&ev.target.closest?ev.target.closest('.cal-btn'):null;
  if(!b)return;
  var e=EVENTS[+b.getAttribute('data-ei')];if(e)dlICS(e);
});
var _renderAllLU=renderAll;
renderAll=function(){_renderAllLU();tickCD();};
tickCD();
setInterval(tickCD,45000);"""

# --- Time-zone toggle (injected into the template) ------------------------
# One segmented control in the Filter panel: Posted / My time / PT / ET / CT.
# Posted (the default) renders the calendar's time string untouched; the
# other modes re-render every .tz-time element from the event's baked epoch
# start/end via Intl.DateTimeFormat. The choice persists in localStorage.
TZ_CSS = """
/* Time-zone toggle (generator-injected) */
.tz-bar{display:flex;align-items:center;gap:8px;flex:1 1 100%;padding:4px 0 3px}
.tz-label{font-family:var(--mono);font-size:10.5px;letter-spacing:.14em;text-transform:uppercase;color:var(--ink3)}
.tz-seg{display:flex;border:1px solid var(--line);border-radius:999px;overflow:hidden;background:rgba(21,12,42,.7)}
.tz-seg button{appearance:none;border:0;background:transparent;color:var(--ink2);font-family:var(--mono);font-size:10.5px;letter-spacing:.08em;text-transform:uppercase;padding:5px 11px;cursor:pointer;white-space:nowrap}
.tz-seg button+button{border-left:1px solid var(--line)}
.tz-seg button:hover{color:var(--cyan-hi)}
.tz-seg button.on{background:rgba(34,211,238,.16);color:#a5f3fc;box-shadow:inset 0 0 10px rgba(34,211,238,.3)}"""

TZ_HTML = ('  <div class="tz-bar"><span class="tz-label" id="tzLabel">Times:</span>'
           '<div class="tz-seg" id="tzSeg" role="group" aria-labelledby="tzLabel">'
           '<button type="button" data-tz="posted" class="on" aria-pressed="true">Posted</button>'
           '<button type="button" data-tz="mine" aria-pressed="false">My time</button>'
           '<button type="button" data-tz="PT" aria-pressed="false">PT</button>'
           '<button type="button" data-tz="ET" aria-pressed="false">ET</button>'
           '<button type="button" data-tz="CT" aria-pressed="false">CT</button>'
           '</div></div>\n')

TZ_JS = r"""/* Time-zone toggle — injected by build-lineup-site.py */
var TZMODE='posted';
try{var _tzSaved=localStorage.getItem('lineup-tz');if(_tzSaved&&['posted','mine','PT','ET','CT'].indexOf(_tzSaved)>-1)TZMODE=_tzSaved;}catch(_e){}
var TZONES={PT:'America/Los_Angeles',ET:'America/New_York',CT:'America/Chicago'};
function tzParts(ts,tz){
  var o={hour:'numeric',minute:'2-digit',hour12:true,timeZoneName:'short',weekday:'short',year:'numeric',month:'2-digit',day:'2-digit'};
  if(tz)o.timeZone=tz;
  var f=new Intl.DateTimeFormat('en-US',o),m={};
  f.formatToParts(new Date(ts*1000)).forEach(function(p){m[p.type]=p.value});
  return m;
}
function tzClock(p){return p.hour+':'+p.minute+' '+p.dayPeriod}
function tzFmt(e){
  if(TZMODE==='posted'||!e.start)return e.time;
  var tz=TZMODE==='mine'?null:TZONES[TZMODE];
  var sp=tzParts(e.start,tz),out;
  if(e.end&&e.end>e.start&&(e.end-e.start)<72000){
    var ep=tzParts(e.end,tz);
    if(ep.dayPeriod===sp.dayPeriod&&ep.timeZoneName===sp.timeZoneName){
      out=sp.hour+':'+sp.minute+'\u2013'+tzClock(ep)+' '+sp.timeZoneName;
    }else{
      out=tzClock(sp)+' '+sp.timeZoneName+' \u2013 '+tzClock(ep)+' '+ep.timeZoneName;
    }
  }else{
    out=tzClock(sp)+' '+sp.timeZoneName;
  }
  var iso=sp.year+'-'+sp.month+'-'+sp.day;
  if(iso!==e.dayiso)out=sp.weekday+' '+out;
  return out;
}
function applyTZ(){
  document.querySelectorAll('.tz-time').forEach(function(el){
    var e=EVENTS[+el.getAttribute('data-ei')];if(!e)return;
    el.textContent=tzFmt(e);
  });
  document.querySelectorAll('#tzSeg button').forEach(function(b){
    var on=b.getAttribute('data-tz')===TZMODE;
    b.classList.toggle('on',on);
    b.setAttribute('aria-pressed',on?'true':'false');
  });
}
var tzSegEl=document.getElementById('tzSeg');
if(tzSegEl){tzSegEl.addEventListener('click',function(ev){
  var b=ev.target&&ev.target.closest?ev.target.closest('button[data-tz]'):null;
  if(!b)return;
  TZMODE=b.getAttribute('data-tz');
  try{localStorage.setItem('lineup-tz',TZMODE);}catch(_e){}
  applyTZ();
});}
var _renderAllTZ=renderAll;
renderAll=function(){_renderAllTZ();applyTZ();};
applyTZ();"""

# --- Share preview meta (injected into <head>) -----------------------------
# Open Graph + Twitter card. No og:image: the GitHub push flow accepts
# UTF-8 text only, so a binary share image cannot be published to the repo
# (verified 2026-10-24 — push-files rejects non-UTF-8 snapshot files).
META_HTML = (
    '\n<meta property="og:title" content="The Lineup — GTA RP Event Magazine"/>'
    '\n<meta property="og:description" content="Every GTA RP event, car meet and city opening in one magazine — with live countdowns."/>'
    '\n<meta property="og:type" content="website"/>'
    '\n<meta property="og:url" content="https://commissionchronicle.github.io/the-lineup/"/>'
    '\n<meta name="twitter:card" content="summary_large_image"/>'
    '\n<meta name="twitter:title" content="The Lineup — GTA RP Event Magazine"/>'
    '\n<meta name="twitter:description" content="Every GTA RP event, car meet and city opening in one magazine — with live countdowns."/>')

# --- Name search (injected into the Filter panel) --------------------------
# A search row at the top of the filter panel; matches() (in the core
# script below) also checks SEARCHQ against event title + host handle,
# composing with the category filters. Re-renders go through renderAll,
# so the countdown + zone-toggle wrappers re-apply after every keystroke.
SEARCH_CSS = """
/* Name search — top of the filter panel (generator-injected) */
.fb-search{flex:1 1 100%;display:flex;align-items:center;gap:7px;padding:2px 0 4px}
.fb-search input{flex:1;min-width:0;background:rgba(13,7,22,.8);border:1px solid var(--line);border-radius:999px;color:var(--ink);font-family:var(--sans);font-size:13.5px;padding:8px 14px}
.fb-search input::placeholder{color:var(--ink3)}
.fb-search input:focus{outline:none;border-color:var(--cyan);box-shadow:0 0 10px rgba(34,211,238,.35)}
.fb-search button{appearance:none;border:1px solid var(--line);background:rgba(21,12,42,.7);color:var(--ink2);width:30px;height:30px;border-radius:50%;font-size:16px;line-height:1;cursor:pointer;flex:none}
.fb-search button:hover{border-color:var(--rose);color:var(--rose-hi)}"""

SEARCH_HTML = ('    <div class="fb-search">'
               '<input id="searchInput" type="search" placeholder="Search events or hosts…" '
               'aria-label="Search events or hosts" autocomplete="off"/>'
               '<button id="searchClear" type="button" aria-label="Clear search" hidden>×</button>'
               '</div>')

SEARCH_JS = r"""/* Name search — injected by build-lineup-site.py */
var searchInputEl=document.getElementById('searchInput');
var searchClearEl=document.getElementById('searchClear');
function applySearch(){
  SEARCHQ=searchInputEl?searchInputEl.value.trim():'';
  if(searchClearEl)searchClearEl.hidden=!SEARCHQ;
  renderAll();
  if(!inPlay(current))goTo(0,false);
}
if(searchInputEl){searchInputEl.addEventListener('input',applySearch);}
if(searchClearEl){searchClearEl.addEventListener('click',function(){
  if(searchInputEl)searchInputEl.value='';
  applySearch();
  if(searchInputEl)searchInputEl.focus();
});}"""

# --- Host pages + marquee (generator-injected) ------------------------------
HOST_CSS = """
/* Host pages + back page (generator-injected) */
.host-head{display:flex;align-items:flex-end;gap:18px;margin:30px 0 6px;flex-wrap:wrap}
.host-head-main{min-width:0}
.host-kicker{font-family:var(--mono);font-size:12px;letter-spacing:.22em;text-transform:uppercase;color:var(--amber-hi);text-shadow:0 0 9px rgba(251,191,36,.5);margin:0 0 6px}
.host-name{font-family:var(--disp);font-weight:700;font-size:clamp(38px,7vw,72px);line-height:.95;margin:0;letter-spacing:.02em;color:#f7f4ff;text-shadow:0 0 16px rgba(34,211,238,.45),0 0 44px rgba(232,121,249,.25);overflow-wrap:anywhere}
.host-name a{color:inherit;text-decoration:none}
.host-name a:hover{color:var(--pink-hi);text-decoration:none;text-shadow:0 0 16px rgba(244,113,182,.6)}
.host-next{margin:10px 0 0;font-size:16px;color:var(--ink)}
.host-next b{color:var(--amber-hi);font-weight:600}
.host-meta{margin:4px 0 0;font-family:var(--mono);font-size:11.5px;letter-spacing:.1em;text-transform:uppercase;color:var(--cyan-hi)}
.host-flyer{margin:0 0 22px;border:1px solid var(--cyan-soft);border-radius:12px;box-shadow:0 0 18px rgba(34,211,238,.12)}
.back-page{margin:30px 0 10px}
.credits-line{text-align:center;font-family:var(--mono);font-size:11px;letter-spacing:.06em;text-transform:uppercase;color:var(--ink3);line-height:1.8;padding:8px 0 0}
.end-mark{text-align:center;font-family:var(--mono);letter-spacing:.3em;color:var(--pink-hi);font-size:13px;padding:12px 0 34px;text-shadow:0 0 10px rgba(244,113,182,.5)}
.fb-days button.host-chip{display:flex;flex-direction:column;align-items:flex-start;gap:1px;padding:6px 10px;text-align:left}
.fb-days button.host-chip b{font-family:var(--disp);font-size:13.5px;letter-spacing:.03em;color:var(--pink-hi);font-weight:700;text-transform:none}
.fb-days button.host-chip span{font-size:9.5px;color:var(--ink3);letter-spacing:.05em}
.fb-days button.host-chip.on b{color:#fbcfe8}
.date-divider{font-family:var(--mono);font-size:12px;letter-spacing:.18em;text-transform:uppercase;color:var(--cyan-hi);text-shadow:0 0 8px rgba(34,211,238,.35);margin:24px 0 10px;padding-bottom:6px;border-bottom:1px solid var(--cyan-soft)}
.date-divider:first-child{margin-top:4px}"""

MQ_CSS = """
/* Marquee — live ticker items (generator-injected). The scroll is driven
   by a JS requestAnimationFrame loop (see the marquee block in CORE_JS),
   NOT by the template's CSS keyframes: Android's "Remove animations"
   setting makes prefers-reduced-motion match, and the template's
   reduced-motion block freezes .ticker-track with animation:none, which
   killed the ticker outright on phones. The rule below therefore retires
   the CSS animation for good (!important beats both the base keyframe
   rule and the reduced-motion freeze), and the JS transform is exempt
   from the freeze — the ticker's motion IS its content. Pausing is also
   JS-driven (pointer / touch / focus), not animation-play-state. */
.ticker-track{animation:none!important;will-change:transform}
.ticker .mq-item{font:inherit;letter-spacing:inherit;text-transform:inherit;color:var(--ink2);background:none;border:0;padding:0;cursor:pointer;white-space:nowrap}
.ticker .mq-item:hover{color:var(--cyan-hi);text-decoration:underline;text-underline-offset:3px}"""


# --- Core page script (replaces the template's day-spread script) ---------
# Data tokens (__EVENTS_JSON__ etc.) are filled in by main(). The script
# ends with the renderAll(); / goTo(0,false); pair the tail injection
# anchors on, so the countdown / zone-toggle / search blocks appended
# there keep working unchanged (their function declarations — cdChip,
# calBtn, tickCD, applyTZ — are hoisted across the whole script element).
CORE_JS = r"""/* The Lineup — host-page edition. Data + page machinery injected by build-lineup-site.py */
var EVENTS=__EVENTS_JSON__;
var POSTS=__POSTS_JSON__;
var HOSTS=__HOSTS_JSON__;
var CLOSING=__CLOSING_JSON__;

function igLink(handle,label){
  return '<a class="ig" href="https://www.instagram.com/'+handle.slice(1)+'/" target="_blank" rel="noopener">'+(label||handle)+'</a>';
}
function hostChip(h){
  if(h.charAt(0)==='@'){
    return '<a href="https://www.instagram.com/'+h.slice(1)+'/" target="_blank" rel="noopener" aria-label="Open '+h+' on Instagram">'+h+' ↗</a>';
  }
  return '<span>'+h+'</span>';
}
var SEARCHQ='';
function qEsc(s){return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')}
function matches(e,f){
  if(f!=='all'&&e.cats.indexOf(f)===-1)return false;
  if(!SEARCHQ)return true;
  return (e.title+' '+e.host).toLowerCase().indexOf(SEARCHQ.toLowerCase())>-1;
}
function cardHTML(e,solo){
  var ei=EVENTS.indexOf(e);
  var post=POSTS[e.title+'|'+e.date];
  var flyer=post?'<a class="flyer-link" href="'+post+'" target="_blank" rel="noopener" aria-label="Open the original flyer post for '+e.title+' on Instagram">Flyer post ↗</a>':'';
  return '<article class="event s-'+e.cats[0]+(solo?' solo':'')+'"><div class="date"><span class="tz-time" data-ei="'+ei+'">'+e.time+'</span></div><h3>'+e.title+'</h3><p>'+e.desc+'</p><div class="meta">'+hostChip(e.host)+flyer+cdChip(e)+calBtn(e)+'<span>'+e.where+'</span><span>'+e.platform+'</span></div></article>';
}

/* Build one page per host, in the baked soonest-first order */
var stage=document.getElementById('stage');
HOSTS.forEach(function(h,hi){
  h.eis.forEach(function(ei){EVENTS[ei]._hp=hi+1;});
  var sec=document.createElement('section');
  sec.className='page'; sec.setAttribute('data-title',h.handle); sec.setAttribute('aria-label','Host: '+h.handle);
  var first=EVENTS[h.eis[0]], last=EVENTS[h.eis[h.eis.length-1]];
  var handleHTML=h.handle.charAt(0)==='@'
    ? '<a href="https://www.instagram.com/'+h.handle.slice(1)+'/" target="_blank" rel="noopener" aria-label="Open '+h.handle+' on Instagram">'+h.handle+' ↗</a>'
    : h.handle;
  var flyer='';
  if(h.flyer){
    flyer='<figure class="flyer-fig host-flyer"><img src="'+h.flyer.img+'" alt="'+h.flyer.alt+'"/><figcaption>The official flyer, as posted by '+(h.handle.charAt(0)==='@'?igLink(h.handle):h.handle)+(h.flyer.post?' · <a class="ig" href="'+h.flyer.post+'" target="_blank" rel="noopener">Original flyer post ↗</a>':'')+'</figcaption></figure>';
  }
  sec.innerHTML='<div class="host-head"><div class="host-head-main"><p class="host-kicker">Host · '+(hi+1)+' of '+HOSTS.length+'</p><h2 class="host-name" tabindex="-1">'+handleHTML+'</h2>'
    +'<p class="host-next">Next up — <b>'+first.title+'</b> · <span class="tz-time" data-ei="'+h.eis[0]+'">'+first.time+'</span></p>'
    +'<p class="host-meta">'+h.eis.length+(h.eis.length===1?' event':' events')+' in this issue · '+first.date+' – '+last.date+'</p></div>'
    +'<div class="day-count" data-count></div></div><div class="day-rule"></div>'+flyer+'<div data-body></div>';
  sec._events=h.eis.map(function(ei){return EVENTS[ei];});
  sec._host=h;
  stage.appendChild(sec);
});

/* Back page — closing note, credits and the end mark */
var backSec=document.createElement('section');
backSec.className='page'; backSec.setAttribute('data-title','Back page'); backSec.setAttribute('aria-label','Back page');
backSec.innerHTML='<div class="back-page">'+CLOSING+'</div>';
backSec._shown=1;
stage.appendChild(backSec);

var pages=Array.prototype.slice.call(document.querySelectorAll('.page'));
var hostChips=document.getElementById('dayChips');
var chipEls=[];
var flipbarEl=document.querySelector('.flipbar');
var daysToggle=document.getElementById('daysToggle'), filterToggle=document.getElementById('filterToggle');
function setPanel(cls,btn,open){
  flipbarEl.classList.toggle(cls,open);
  btn.setAttribute('aria-expanded',open?'true':'false');
}
daysToggle.addEventListener('click',function(){
  setPanel('open-days',daysToggle,!flipbarEl.classList.contains('open-days'));
  setPanel('open-filters',filterToggle,false);
});
filterToggle.addEventListener('click',function(){
  setPanel('open-filters',filterToggle,!flipbarEl.classList.contains('open-filters'));
  setPanel('open-days',daysToggle,false);
});
function makeChip(label,pageIdx,cls){
  var b=document.createElement('button'); b.type='button';
  if(cls)b.className=cls;
  b.innerHTML=label;
  b.addEventListener('click',function(){goTo(pageIdx, pageIdx<current); setPanel('open-days',daysToggle,false)});
  hostChips.appendChild(b); chipEls[pageIdx]=b; return b;
}
makeChip('Cover',0);
HOSTS.forEach(function(h,hi){
  var ne=EVENTS[h.eis[0]];
  makeChip('<b>'+h.handle+'</b><span>'+ne.date+' · '+ne.time+'</span>', hi+1, 'host-chip');
});
makeChip('Back page',pages.length-1);

var current=0, filter='all';
var prevBtn=document.getElementById('prevBtn'), nextBtn=document.getElementById('nextBtn');
var fbTitle=document.getElementById('fbTitle'), fbCount=document.getElementById('fbCount');

/* Group a host's (chronological) events under one slim divider per
   distinct day, so the date is stated once instead of on every card. */
function dayLabel(e){
  var d=new Date(e.dayiso+'T12:00:00');
  return d.toLocaleDateString('en-US',{weekday:'long',month:'long',day:'numeric'});
}
function groupByDay(list){
  var groups=[],cur=null;
  list.forEach(function(e){
    if(!cur||cur.dayiso!==e.dayiso){cur={dayiso:e.dayiso,label:dayLabel(e),events:[]};groups.push(cur);}
    cur.events.push(e);
  });
  return groups;
}
function renderHost(sec){
  if(!sec._events) return;
  var shown=sec._events.filter(function(e){return matches(e,filter)});
  var body=sec.querySelector('[data-body]');
  if(shown.length){
    body.innerHTML=groupByDay(shown).map(function(g){
      return '<div class="date-divider" role="separator">'+g.label+'</div>'
        +'<div class="day-grid">'+g.events.map(function(e){return cardHTML(e, shown.length===1)}).join('')+'</div>';
    }).join('');
  }else{
    body.innerHTML='<div class="day-empty">'+(SEARCHQ?'No events match &ldquo;'+qEsc(SEARCHQ)+'&rdquo; for this host — clear the search in Filter, or flip on.':'Nothing in this lane for this host — flip on, or switch the filter back to All Events.')+'</div>';
  }
  var c=sec.querySelector('[data-count]');
  if(c)c.textContent=shown.length+(shown.length===1?' event':' events')+(filter!=='all'||SEARCHQ?' · filtered':'');
  sec._shown=shown.length;
}
function renderAll(){pages.forEach(renderHost)}

/* A page stays in the flip order if it has anything showing; cover and back page always stay */
function inPlay(i){return i===0||i===pages.length-1||pages[i]._shown>0}
function playList(){var r=[];for(var i=0;i<pages.length;i++){if(inPlay(i))r.push(i)}return r}

function goTo(idx,back){
  var list=playList();
  if(list.indexOf(idx)===-1){idx=list[0]}
  pages.forEach(function(p,i){p.classList.toggle('active',i===idx); p.classList.toggle('back',!!back&&i===idx)});
  current=idx;
  var pos=list.indexOf(idx);
  if(idx===0){fbTitle.textContent='Cover';}
  else if(idx===pages.length-1){fbTitle.textContent='Back page';}
  else{fbTitle.textContent='Host '+idx+' of '+HOSTS.length+' — '+HOSTS[idx-1].handle;}
  fbCount.textContent='Page '+(pos+1)+' of '+list.length;
  prevBtn.disabled=pos<=0; nextBtn.disabled=pos>=list.length-1;
  chipEls.forEach(function(c,i){if(c){c.classList.toggle('on',i===idx); c.disabled=!inPlay(i)}});
  window.scrollTo(0,0);
  var h=pages[idx].querySelector('.host-name'); if(h){h.focus({preventScroll:true})}
}
function step(dir){
  var list=playList(); var pos=list.indexOf(current);
  var n=list[pos+dir]; if(n===undefined)return;
  goTo(n, dir<0);
}
prevBtn.addEventListener('click',function(){step(-1)});
nextBtn.addEventListener('click',function(){step(1)});
document.addEventListener('keydown',function(ev){
  if(ev.target.tagName==='INPUT'||ev.target.tagName==='TEXTAREA')return;
  if(ev.key==='ArrowRight'){step(1)}
  else if(ev.key==='ArrowLeft'){step(-1)}
});
var tx=null,ty=null;
stage.addEventListener('touchstart',function(ev){var t=ev.changedTouches[0]; tx=t.clientX; ty=t.clientY},{passive:true});
stage.addEventListener('touchend',function(ev){
  if(tx===null)return;
  var t=ev.changedTouches[0], dx=t.clientX-tx, dy=t.clientY-ty; tx=null;
  if(Math.abs(dx)>70&&Math.abs(dx)>Math.abs(dy)*1.6){step(dx<0?1:-1)}
},{passive:true});

document.querySelectorAll('.fb-filters button[data-filter]').forEach(function(b){
  b.addEventListener('click',function(){
    document.querySelectorAll('.fb-filters button[data-filter]').forEach(function(x){x.classList.remove('active')});
    b.classList.add('active');
    filter=b.getAttribute('data-filter');
    filterToggle.textContent=filter==='all'?'Filter ▾':'Filter: '+b.textContent+' ▾';
    filterToggle.style.borderColor=filter==='all'?'':'var(--cyan)';
    filterToggle.style.color=filter==='all'?'':'var(--cyan-hi)';
    renderAll();
    goTo(inPlay(current)?current:0, false);
  });
});

/* Marquee — the live wire at the very top. Events starting within the
   next 30 minutes lead; otherwise the next upcoming timed events (up
   to 5, soonest first) ride with live countdowns. Every item jumps to
   its host's page. Refreshed on the countdown tick and on zone changes. */
function mqCountdown(e,now){
  var d=e.start-now;
  if(d>86400)return 'in '+Math.floor(d/86400)+'d '+Math.floor((d%86400)/3600)+'h';
  if(d>=3600)return 'in '+Math.floor(d/3600)+'h '+Math.floor((d%3600)/60)+'m';
  return 'in '+Math.max(1,Math.round(d/60))+'m';
}
function mqPicks(now){
  var soon=[],up=[];
  EVENTS.forEach(function(e){
    if(!e.start)return;
    if(e.start>now&&e.start<=now+1800)soon.push(e);
    else if(e.start>now)up.push(e);
  });
  var byStart=function(a,b){return a.start-b.start};
  soon.sort(byStart); up.sort(byStart);
  if(soon.length)return soon.map(function(e){return{e:e,soon:true}});
  return up.slice(0,5).map(function(e){return{e:e,soon:false}});
}
/* JS scroll driver — the track's CSS animation is disabled (see MQ_CSS:
   the template's reduced-motion rule froze it on Android). A rAF loop
   advances the track ~36px/s (0.6px per 60fps frame) and wraps at half
   the track width, where the duplicated content takes over seamlessly.
   Pauses while the ticker is touched / hovered / focused. */
var mqState={off:0,last:0,paused:false,run:false};
function mqApply(){
  var t=document.getElementById('tickerTrack');
  if(t)t.style.transform='translateX('+(-mqState.off)+'px)';
}
function mqFrame(ts){
  if(!mqState.run)return;
  if(mqState.last&&!mqState.paused){
    var t=document.getElementById('tickerTrack');
    var half=t?t.scrollWidth/2:0;
    if(half>0){mqState.off=(mqState.off+(ts-mqState.last)*0.036)%half;mqApply();}
  }
  mqState.last=ts;
  requestAnimationFrame(mqFrame);
}
function mqStart(){if(mqState.run)return;mqState.run=true;mqState.last=0;requestAnimationFrame(mqFrame);}
function renderMarquee(){
  var track=document.getElementById('tickerTrack');
  if(!track)return;
  var now=Date.now()/1000;
  var picks=mqPicks(now);
  var items;
  if(picks.length){
    items=picks.map(function(pk){
      var e=pk.e;
      var tail=pk.soon?('<b>'+tzFmt(e)+'</b>'):('<b>'+mqCountdown(e,now)+'</b>');
      return '<button type="button" class="mq-item" data-hp="'+(e._hp||0)+'">'+(pk.soon?'STARTING SOON · ':'')+e.title+' — '+e.host+' · '+tail+'</button>';
    });
  }else{
    items=['<span class="mq-static">THE LINEUP — EVERY GTA RP EVENT, ONE PAGE PER HOST</span>'];
  }
  var reps=Math.max(1,Math.ceil(6/items.length));
  var half='';
  for(var r=0;r<reps;r++){half+=items.join(' <i>◆</i> ')+' <i>◆</i> ';}
  track.innerHTML='<span class="mq-set">'+half+'</span><span class="mq-set">'+half+'</span>';
  mqState.off=0;mqApply();
}
var tickerEl=document.getElementById('tickerTrack');
if(tickerEl){tickerEl.addEventListener('click',function(ev){
  var b=ev.target&&ev.target.closest?ev.target.closest('.mq-item'):null;
  if(!b)return;
  var p=+b.getAttribute('data-hp');
  if(p>0)goTo(p,false);
});}
var _tickCDHost=tickCD;
tickCD=function(){_tickCDHost();renderMarquee();};
var _applyTZHost=applyTZ;
applyTZ=function(){_applyTZHost();renderMarquee();};
var tickerBox=document.querySelector('.ticker');
if(tickerBox){
  ['pointerdown','touchstart','mouseenter','focusin'].forEach(function(n){
    tickerBox.addEventListener(n,function(){mqState.paused=true;},{passive:true});
  });
  ['pointerup','pointercancel','touchend','mouseleave','focusout'].forEach(function(n){
    tickerBox.addEventListener(n,function(){mqState.paused=false;},{passive:true});
  });
}
renderMarquee();
mqStart();

renderAll();
goTo(0,false);
"""


def main():
    today = datetime.now(PT).date()
    raw = pull_calendar(today)
    events, skipped = [], 0
    for item in raw:
        rec = parse_event(item, today)
        if rec is None:
            skipped += 1
        else:
            events.append(rec)
    events.sort(key=lambda e: (e["day"], e["sort"], e["title"]))
    if not events:
        sys.exit("no events in window — refusing to build an empty magazine")
    clear_flyers()
    total = len(events)
    last_day = max(e["day"] for e in events)

    # JS data blocks ------------------------------------------------------
    js_events = [{
        "date": e["date_key"], "time": e["time"], "title": esc(e["title"]),
        "host": esc(e["host"]), "where": esc(e["where"]),
        "platform": esc(e["platform"]), "desc": esc(e["desc"]),
        "cats": e["cats"],
        # Countdown instants (epoch seconds; null for time-TBA / all-day)
        "start": e["start_ts"], "end": e["end_ts"], "dayiso": e["day_iso"],
        # Raw (unescaped) fields used only to build the .ics download
        "ics": {
            "t": e["summary"], "h": e["host"], "p": e["platform"],
            "ap": ics_time_note(e), "u": e["post"],
        },
    } for e in events]
    posts = {f"{esc(e['title'])}|{e['date_key']}": e["post"]
             for e in events if e["post"]}

    # Host grouping + ordering ---------------------------------------------
    # Group the globally chronological event list by host (each host's
    # slice stays chronological), then order hosts by their next event's
    # order key — timed starts at their instant, all-day / time-TBA at
    # the end of their day — soonest first, ties broken by handle.
    by_host = {}
    for idx, e in enumerate(events):
        by_host.setdefault(e["host"], []).append(idx)
    host_list = []
    for handle, eis in by_host.items():
        key = min(event_order_key(events[i]) for i in eis)
        host_list.append({"handle": handle, "eis": eis, "key": key})
    host_list.sort(key=lambda h: (h["key"], h["handle"].lower()))
    n_hosts = len(host_list)

    js_hosts = []
    for h in host_list:
        flyer = None
        if h["handle"] == "@wsp_city_roleplay":
            post = ""
            for i in h["eis"]:
                if events[i]["post"] and "wsp city" in events[i]["title"].lower():
                    post = events[i]["post"]
                    break
            if not post:
                post = next((events[i]["post"] for i in h["eis"]
                             if events[i]["post"]), "")
            flyer = {"img": "assets/wsp-flyer.jpg",
                     "alt": "WSP City Roleplay official flyer: inauguration artwork with blue neon city styling",
                     "post": post}
        js_hosts.append({"handle": esc(h["handle"]), "eis": h["eis"],
                         "flyer": flyer})

    # Closing / back page ---------------------------------------------------
    reg_hosts = Counter(e["host"] for e in events if e["recurring"])
    reg_bits = []
    for h, c in reg_hosts.most_common():
        series = Counter(e["title"] for e in events
                         if e["host"] == h).most_common(1)[0][0]
        reg_bits.append(
            f"<b>{esc(series)}</b> ({c} listings · "
            f"<a class=\"ig\" href=\"https://www.instagram.com/{h[1:]}/\" "
            f"target=\"_blank\" rel=\"noopener\">{esc(h)}</a>)")
    regulars_txt = (" Weekly regulars riding along in this issue: "
                    + " and ".join(reg_bits) + ".") if reg_bits else ""
    credits = ("Cover: The lineup forms up — customs, classics &amp; bikes under the neon"
               "<br>Photos: Lineup studio illustrations"
               + (" · WSP City flyer: @wsp_city_roleplay"
                  if "@wsp_city_roleplay" in by_host else ""))
    closing_html = (
        '<div class="closing"><h3>Get listed in the next issue</h3><p>Hosting a meet, '
        'launch or contest? The Lineup is built from the same watch as the GTA RP Event '
        'Calendar — dated flyers with a time, place and platform get picked up on the '
        f'12 AM / 12 PM runs.{regulars_txt}</p>'
        '<a class="btn" href="https://tinyurl.com/GTA-RP-EVENT-Calendar" target="_blank" '
        'rel="noopener">Open the Full Calendar →</a></div>'
        f'<div class="colophon"><b>The Lineup</b> — GTA RP Event Magazine · '
        f'{day_full(today)}<br>From the @gtarpnoticeboard desk · Events as listed by '
        'their organizers · In-game RP events only</div>'
        f'<p class="credits-line">{credits}</p>'
        '<p class="end-mark">◆ END OF ISSUE ◆</p>')

    # Core script assembly --------------------------------------------------
    def js_json(obj):
        return json.dumps(obj, ensure_ascii=False, indent=1).replace("</", "<\\/")

    script = (CORE_JS
              .replace("__EVENTS_JSON__", js_json(js_events))
              .replace("__POSTS_JSON__", js_json(posts))
              .replace("__HOSTS_JSON__", js_json(js_hosts))
              .replace("__CLOSING_JSON__", js_json(closing_html)))

    # Template surgery ------------------------------------------------------
    tpl = TEMPLATE.read_text(encoding="utf-8")
    out = tpl
    # The whole day-spread script (ticker fill, day data, features, page
    # building, spotlight, navigation) is replaced by the host-page core.
    assert out.count("</script>") == 1, "script anchor"
    out = replace_block(out, "var TICKER=", "</script>", script + "</script>")

    # Share-preview meta in the head.
    title_anchor = "<title>The Lineup — GTA RP Event Magazine</title>"
    assert out.count(title_anchor) == 1, "title anchor"
    out = out.replace(title_anchor, title_anchor + META_HTML)

    # Injected CSS: countdown chips, zone toggle, search, host pages, marquee.
    assert out.count("</style>") == 1, "style anchor"
    out = out.replace("</style>",
                      CD_CSS + TZ_CSS + SEARCH_CSS + HOST_CSS + MQ_CSS + "\n</style>")

    # Filter panel: name search at the top, zone toggle at the bottom.
    # (The flip bar itself keeps only Prev / label / Next + Hosts + Filter.)
    filter_open = '  <div class="fb-filters" id="filterRow" role="group" aria-label="Filter events">'
    assert out.count(filter_open) == 1, "filter panel anchor"
    out = out.replace(filter_open, filter_open + "\n" + SEARCH_HTML)
    filter_close = '    <button data-filter="console" type="button">PS / Xbox</button>\n  </div>'
    assert out.count(filter_close) == 1, "filter panel close anchor"
    out = out.replace(filter_close,
                      '    <button data-filter="console" type="button">PS / Xbox</button>\n'
                      + TZ_HTML + '  </div>')

    # Countdown / zone-toggle / search behaviour at the end of the script.
    tail_anchor = "renderAll();\ngoTo(0,false);\n</script>"
    assert out.count(tail_anchor) == 1, "script tail anchor"
    out = out.replace(tail_anchor,
                      "renderAll();\ngoTo(0,false);\n" + CD_JS + "\n" + TZ_JS + "\n"
                      + SEARCH_JS + "\n</script>")

    def swap(old, new, label):
        nonlocal out
        assert out.count(old) == 1, f"anchor not unique/found: {label}"
        out = out.replace(old, new)

    # Chrome: the marquee is interactive now (no aria-hidden), and the
    # day-jump strip is the hosts index.
    swap('<div class="ticker" aria-hidden="true">', '<div class="ticker">', "ticker div")
    swap('<button id="daysToggle" type="button" aria-expanded="false" aria-controls="dayChips">Days ▾</button>',
         '<button id="daysToggle" type="button" aria-expanded="false" aria-controls="dayChips">Hosts ▾</button>',
         "hosts toggle")
    swap('<nav class="fb-days" id="dayChips" aria-label="Jump to a day">',
         '<nav class="fb-days" id="dayChips" aria-label="Jump to a host">', "hosts nav")
    swap('<p class="flip-hint">Flip with Prev / Next, arrow keys, or a swipe — Days jumps you straight to a date</p>',
         '<p class="flip-hint">Flip with Prev / Next, arrow keys, or a swipe — Hosts jumps you straight to an organizer</p>',
         "flip hint")

    # Cover: page 1 is the swappable cover PHOTO carried in the template,
    # with the Newsstand words as a live HTML overlay computed from this
    # build's event data (cover_values / cover_overlay_html above). The
    # photo inlines below from the assets key "cover"; the words refresh
    # every build. Assert the anchors so a template regression fails loud.
    assert out.count('class="cover-screen photo"') == 1, "cover section anchor"
    assert out.count('src="assets/cover.webp"') == 1, "cover img anchor"
    assert out.count('__COVER_OVERLAY__') == 1, "cover overlay anchor"
    cvals = cover_values(events, today)
    out = out.replace('__COVER_OVERLAY__', cover_overlay_html(cvals))

    # Inline the artwork from assets-inline.json (the CI equivalent of
    # inline-assets.py: the repo holds the data URIs as text, substituted
    # here exactly where the local flow substitutes them).
    asset_map = json.loads(ASSETS_JSON.read_text(encoding="utf-8"))
    # The cover entry is keyed "cover" (not a path): substitute it only at
    # the cover <img> so the bare word "cover" elsewhere in the document
    # (CSS classes, object-fit, viewport-fit) is never touched.
    cover_uri = asset_map.pop("cover", None)
    if cover_uri:
        assert out.count('src="assets/cover.webp"') == 1, "cover inlining anchor"
        out = out.replace('src="assets/cover.webp"', f'src="{cover_uri}"')
    for rel, uri in asset_map.items():
        out = out.replace(rel, uri)

    # Sanity guard: never publish an empty or gutted magazine. Compare the
    # baked event count with the previous index.html (in CI, the file
    # checked out from the repo) and refuse to write on a bad pull.
    new_count = out.count('"dayiso"')
    prev_count = (OUT_HTML.read_text(encoding="utf-8").count('"dayiso"')
                  if OUT_HTML.exists() else 0)
    if new_count == 0 or (prev_count and new_count < prev_count / 2):
        sys.exit(f"sanity guard: new build has {new_count} events vs "
                 f"{prev_count} in the previous build - not writing")
    OUT_HTML.write_text(out, encoding="utf-8")

    # Build report -----------------------------------------------------------
    print(f"window : {today.isoformat()} -> {last_day.isoformat()} (today PT + {WINDOW_DAYS}d)")
    print(f"pulled : {len(raw)} calendar instances | skipped: {skipped} | rendered: {total} events "
          f"across {n_hosts} host pages")
    first = host_list[0]
    fe = events[first["eis"][0]]
    print(f"first host page: {first['handle']} — next up {fe['title']} ({fe['date_key']}, {fe['time']})")
    if cvals.get("count"):
        print(f"cover  : week {cvals['dates']} | {cvals['count']} meets inside | "
              f"biggest night {day_label(cvals['big_day'])} ({cvals['big_n']}) | "
              f"spotlight {cvals['host_brand']} {cvals['host_handle']} | "
              f"server watch: {len(cvals['openings'])} openings")
    else:
        print("cover  : no events in the cover week — board/night/spotlight lines omitted")
    timed_n = sum(1 for e in events if e["start_ts"] is not None)
    print(f"countdowns: {timed_n} timed events | {total - timed_n} time-TBA (no countdown)")
    now = time.time()
    soon = [e for e in events if e["start_ts"] and 0 < e["start_ts"] - now <= 1800]
    if soon:
        print("marquee at build time: STARTING SOON branch — "
              + "; ".join(f"{e['title']} — {e['host']}" for e in soon))
    else:
        up = sorted((e for e in events if e["start_ts"] and e["start_ts"] > now),
                    key=lambda e: e["start_ts"])[:5]
        print("marquee at build time: fallback (nothing within 30 min) — "
              + "; ".join(f"{e['title']} — {e['host']} ({e['date_key']} {e['time']})" for e in up))
    print("structure: cover + host pages (soonest first) + back page | marquee on top")
    print("time-zone toggle: Posted / My time / PT / ET / CT (persisted, in Filter panel) | name search: in Filter panel")
    print("share meta: OG + Twitter (no og:image — binary push unsupported)")
    print(f"wrote  : {OUT_HTML} ({OUT_HTML.stat().st_size} bytes) + assets/")


if __name__ == "__main__":
    main()
