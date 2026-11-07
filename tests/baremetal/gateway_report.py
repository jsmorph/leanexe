# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Writes an HTML page with embedded SVG that shows a run of the energy controller's gateway: the
input records that tests/baremetal/uart_gateway.py sent and the output records that the gateway
returned, one tick a minute.

The page draws, on one time axis in hours from the start of the run, the measured load and PV, the
battery power inside the limits that the inverter's read-back reports, the stored energy interval
between the site's floor and ceiling, and the gateway's decisions: proposals accepted as commands,
proposals rejected with the authorizer's status, commands in force, and requests to return to
fallback.  A hover readout lists every value at the nearest tick, and tables give the events and
the records.  Every value comes from RECORDS.in and RECORDS.out, whose layout Demos/Energy/README.md
gives; signed powers are words p + 2^32, and energies are joules.

Usage: uv run tests/baremetal/gateway_report.py RECORDS META OUTPUT.html [FIRST LAST]
RECORDS names RECORDS.in and RECORDS.out.  FIRST and LAST, when given, limit the chart to those
ticks, whose time axis then reads in hours and minutes; the summary and the tables still cover
every tick.  META is a JSON file of strings that the page states as
facts of the run, such as "board", "image", "image_sha256", "started", "summary", and "lean".
"""

import html
import json
import sys

OFFSET = 2 ** 32
STATUS = {0: "accepted", 1: "length", 2: "version", 3: "range", 4: "order", 5: "power",
          6: "export cap", 7: "floor", 8: "import cap", 9: "ceiling"}
STATUS_TEXT = {
    6: "the lower limit would let the site export more than the 2,000 W cap",
    7: "the discharge could take stored energy below the floor",
    9: "the charge could take stored energy above the ceiling",
    8: "the upper limit would let the site import more than the 5,000 W cap",
    5: "a limit lies beyond the battery's rating",
}
# The site's profile, Demos/Energy/Gateway.lean siteProf.
FLOOR_J, CEILING_J = 10_800_000, 34_200_000
FALLBACK = (-50, 50)
# uart_gateway.py's defaults: a proposal every PROPOSE ticks, and a load spike of 5,000 W every
# SPIKE ticks from SPIKE / 2 on.
PROPOSE, SPIKE = 5, 360


def signed(w):
    return w - OFFSET


def load(path):
    with open(path) as f:
        return [list(map(int, line.split())) for line in f if line.strip()]


def ticks(records):
    ins, outs = load(records + ".in"), load(records + ".out")
    if len(ins) != len(outs):
        raise SystemExit(f"{len(ins)} input records but {len(outs)} output records")
    rows = []
    for i, o in zip(ins, outs):
        if i[0] != o[0]:
            raise SystemExit(f"output {o[0]} answers input {i[0]}")
        mode = "fallback" if i[8] else "command"
        lo, hi = (FALLBACK if i[8] else (signed(i[9]), signed(i[10])))
        rows.append({
            "n": i[0], "clock": i[1], "battery": signed(i[3]), "load": i[4], "pv": i[5],
            "eLow": i[6], "eHigh": i[7], "mode": mode, "limLow": lo, "limHigh": hi,
            "proposal": bool(i[11]), "loadLow": i[12], "loadHigh": i[13], "pvLow": i[14],
            "pvHigh": i[15], "propLow": signed(i[16]) if i[11] else None,
            "propHigh": signed(i[17]) if i[11] else None,
            "kind": o[1], "outLow": signed(o[2]) if o[1] == 1 else None,
            "outHigh": signed(o[3]) if o[1] == 1 else None, "revert": o[4], "status": o[5],
            "spike": i[0] >= SPIKE // 2 and (i[0] - SPIKE // 2) % SPIKE == 0,
        })
    return rows


def events(rows):
    ev = []
    for r in rows:
        if r["kind"] == 1:
            ev.append((r["n"], "command", f"limits {r['outLow']:,} to {r['outHigh']:,} W, "
                       f"revert in {r['revert']} s"))
        elif r["kind"] == 2:
            ev.append((r["n"], "fallback request", fallback_reason(rows, r["n"])))
        if r["proposal"] and r["kind"] == 0:
            ev.append((r["n"], "proposal rejected",
                       f"limits {r['propLow']:,} to {r['propHigh']:,} W: {STATUS[r['status']]}"))
        if r["proposal"] and r["kind"] == 2:
            ev.append((r["n"], "proposal not considered",
                       f"limits {r['propLow']:,} to {r['propHigh']:,} W: the tick requested "
                       f"fallback"))
        if r["spike"]:
            ev.append((r["n"], "load spike", "the host adds 5,000 W to the measured load; "
                       + spike_note(rows, r["n"]).split(": ", 1)[-1]
                       if ":" in spike_note(rows, r["n"]) else
                       "the host adds 5,000 W to the measured load"))
    return ev


def legend(x0, y0, items):
    """A legend row from (kind, class, text) items, each placed after the previous one's text."""
    g, xx = [f'<g class="legend" transform="translate({x0},{y0})">'], 0
    for kind, cls, text in items:
        if kind == "line":
            g.append(f'<line class="{cls}" x1="{xx}" x2="{xx + 18}" y1="-4" y2="-4"/>')
            w = 18
        elif kind == "rect":
            g.append(f'<rect class="{cls}" x="{xx}" y="-10" width="18" height="10" rx="2"/>')
            w = 18
        elif kind == "square":
            g.append(f'<rect class="{cls}" x="{xx + 4}" y="-9" width="10" height="10" rx="2"/>')
            w = 18
        else:
            g.append(f'<circle class="{cls}" cx="{xx + 9}" cy="-4" r="5"/>')
            w = 18
        g.append(f'<text x="{xx + w + 6}" y="0">{text}</text>')
        xx += w + 6 + int(len(text) * 6.4) + 22
    return "".join(g) + "</g>"


WINDOW_TICKS = 15  # the profile's window W of 900 s, in ticks of 60 s


def last_command(rows, n):
    return max((r["n"] for r in rows[:n] if r["kind"] == 1), default=None)


def fallback_reason(rows, n):
    if n == 0:
        return "first tick"
    if rows[n]["spike"]:
        return "load spike inside a window"
    return "monitoring"


def spike_note(rows, n):
    if rows[n]["kind"] == 2:
        return "spike +5,000 W: fallback requested"
    c = last_command(rows, n)
    if c is None or n - c > WINDOW_TICKS:
        return "spike +5,000 W: no window in force"
    return "spike +5,000 W"


def signed_text(v):
    return f"{v:,}".replace("-", "\u2212")


def summary(rows):
    """A paragraph of facts computed from the records."""
    props = [r for r in rows if r["proposal"]]
    full = [r for r in props if (r["propLow"], r["propHigh"]) == (-5000, 5000)]
    rest = [r for r in props if (r["propLow"], r["propHigh"]) != (-5000, 5000)]
    def outcome(rs):
        acc = sum(r["kind"] == 1 for r in rs)
        rej = [r for r in rs if r["kind"] == 0]
        skip = sum(r["kind"] == 2 for r in rs)
        why = {}
        for r in rej:
            why[STATUS[r["status"]]] = why.get(STATUS[r["status"]], 0) + 1
        parts = []
        if acc:
            parts.append(f"{acc:,} were accepted")
        if rej and len(why) == 1:
            code = rej[0]["status"]
            reason = STATUS_TEXT.get(code, STATUS[code])
            many = "all " if len(rej) == len(rs) and len(rej) > 1 else ""
            parts.append(f"{many}{len(rej):,} were rejected with the status {STATUS[code]}, "
                         f"because {reason}")
        elif rej:
            parts.append(f"{len(rej):,} were rejected, with the statuses "
                         + ", ".join(f"{k} ({v:,})" for k, v in sorted(why.items())))
        if skip:
            parts.append(f"{skip:,} were not considered, because they arrived on ticks that "
                         f"requested fallback")
        return (", ".join(parts[:-1]) + ", and " + parts[-1] if len(parts) > 2 else
                " and ".join(parts)) or "none"
    cmds = [r for r in rows if r["kind"] == 1]
    reverts = sorted({r["revert"] for r in cmds})
    inforce = sum(r["mode"] == "command" for r in rows)
    emin = min(r["eLow"] for r in rows) / 3.6e6
    emax = max(r["eHigh"] for r in rows) / 3.6e6
    bmin = min(r["battery"] for r in rows)
    bmax = max(r["battery"] for r in rows)
    last_prop = max((r["n"] for r in props), default=None)
    fbs = [r for r in rows if r["kind"] == 2]
    spikes = [r for r in rows if r["spike"]]
    text = [f"The host proposed limits {len(props):,} times."]
    if full:
        text.append(f"Of the {len(full):,} proposals of the full range, −5,000 to +5,000 W, "
                    f"{outcome(full)}.")
    if rest:
        text.append(f"Of the other {len(rest):,} proposals, whose limits were narrower, "
                    f"{outcome(rest)}.")
    if last_prop is not None and len(rows) - 1 - last_prop >= PROPOSE:
        text.append(f"No proposal arrived after tick {last_prop:,}.")
    if cmds:
        text.append(f"The gateway sent {len(cmds):,} commands, each with a revert timeout of "
                    + " or ".join(f"{v:,} s" for v in reverts)
                    + f", and the inverter reported a command in force for {inforce:,} of the "
                    f"{len(rows):,} minutes.")
    mids = [((r["eLow"] + r["eHigh"]) / 2 / 3.6e6, r) for r in rows]
    floor, ceiling = FLOOR_J / 3.6e6, CEILING_J / 3.6e6
    lo_mid, hi_mid = min(m for m, _ in mids), max(m for m, _ in mids)
    text.append("\n")
    text.append(f"Battery power ranged from {signed_text(bmin)} W to {signed_text(bmax)} W.  The "
                f"simulated stored energy, the middle of the interval that the gateway receives, "
                f"ranged from {lo_mid:.3f} to {hi_mid:.3f} kWh.")
    under = [r for m, r in mids if m < floor]
    if under:
        deficit = (floor - lo_mid) * 1000
        bat = [r["battery"] for r in under]
        modes = sorted({r["mode"] for r in under})
        text.append(f"It lay below the floor of {floor:.1f} kWh in {len(under):,} minutes, between "
                    f"{hhmm(under[0]['n'])} and {hhmm(under[-1]['n'])}, by at most {deficit:.1f} Wh, "
                    f"while the inverter was in {' or '.join(modes)} mode and the battery's power "
                    f"lay between {signed_text(min(bat))} and {signed_text(max(bat))} W.")
    over = [r for m, r in mids if m > ceiling]
    if over:
        text.append(f"It lay above the ceiling of {ceiling:.1f} kWh in {len(over):,} minutes.")
    text.append("\n")
    if fbs:
        text.append(f"The gateway requested fallback {len(fbs):,} times: "
                    + "; ".join(f"tick {r['n']:,} ({hhmm(r['n'])}), {fallback_reason(rows, r['n'])}"
                                for r in fbs) + ".")
    quiet = [r for r in spikes if r["kind"] != 2]
    if quiet:
        text.append("Load spikes that drew no request: "
                    + "; ".join(f"tick {r['n']:,} ({hhmm(r['n'])}), "
                                f"{spike_note(rows, r['n']).split(': ', 1)[-1]}" for r in quiet)
                    + ", since the last command's window of 900 s had ended.")
    paras, cur = [], []
    for t in text:
        if t == "\n":
            paras.append(cur); cur = []
        else:
            cur.append(t)
    paras.append(cur)
    return "<h2>The day in numbers</h2>" + "".join(
        "<p>" + html.escape("  ".join(ps)) + "</p>" for ps in paras if ps)


def hhmm(n):
    return f"{n // 60:02d}:{n % 60:02d}"


def page(rows, meta, t0=0, t1=None):
    n = len(rows)
    t1 = n - 1 if t1 is None else t1
    sel = rows[t0:t1 + 1]
    W, L, R = 1200, 100, 24
    PW = W - L - R
    x = lambda t: L + PW * (t - t0) / max(t1 - t0, 1)
    out = []

    def axis_x(y0, h, labels):
        g = []
        span = t1 - t0
        step = 10 if span <= 180 else (60 if span <= 360 else 120)
        t = -(-t0 // step) * step
        while t <= t1:
            g.append(f'<line class="grid" x1="{x(t):.1f}" x2="{x(t):.1f}" y1="{y0}" y2="{y0 + h}"/>')
            if labels:
                text = hhmm(t) if span <= 360 else f"{t // 60} h"
                g.append(f'<text class="tick" x="{x(t):.1f}" y="{y0 + h + 16}" '
                         f'text-anchor="middle">{text}</text>')
            t += step
        return "".join(g)

    def axis_y(y0, h, lo, hi, step, fmt):
        g = []
        v = (lo // step) * step
        while v <= hi:
            if v >= lo:
                yy = y0 + h - h * (v - lo) / (hi - lo)
                g.append(f'<line class="{"base" if v == 0 else "grid"}" x1="{L}" x2="{L + PW}" '
                         f'y1="{yy:.1f}" y2="{yy:.1f}"/>')
                g.append(f'<text class="tick" x="{L - 8}" y="{yy + 4:.1f}" '
                         f'text-anchor="end">{fmt(v)}</text>')
            v += step
        return "".join(g)

    def path(vals, y0, h, lo, hi):
        pts = []
        for k, v in enumerate(vals):
            yy = y0 + h - h * (min(max(v, lo), hi) - lo) / (hi - lo)
            pts.append(f"{'M' if k == 0 else 'L'}{x(t0 + k):.1f},{yy:.1f}")
        return "".join(pts)

    def band(lows, highs, y0, h, lo, hi):
        yv = lambda v: y0 + h - h * (min(max(v, lo), hi) - lo) / (hi - lo)
        top, bot = [], []
        for k, v in enumerate(highs):
            t = t0 + k
            top += [f"{x(t):.1f},{yv(v):.1f}", f"{x(min(t + 1, t1)):.1f},{yv(v):.1f}"]
        for k, v in reversed(list(enumerate(lows))):
            t = t0 + k
            bot += [f"{x(min(t + 1, t1)):.1f},{yv(v):.1f}", f"{x(t):.1f},{yv(v):.1f}"]
        return "M" + " L".join(top + bot) + " Z"

    fmtw = lambda v: f"{v:,.0f}".replace("-", "−")
    y = 20
    panels = []

    # Panel 1: load and PV.
    h1 = 190
    peak = max(max(r["load"] for r in sel), max(r["pv"] for r in sel))
    top1 = ((peak + 999) // 1000) * 1000
    p = [f'<text class="ptitle" x="{L}" y="{y}">Measured load and PV, W</text>',
         legend(L, y + 18, [("line", "k1", "Load"), ("line", "k2", "PV")])]
    y += 30
    p.append(axis_x(y, h1, False) + axis_y(y, h1, 0, top1, 1000 if top1 <= 8000 else 2000, fmtw))
    p.append(f'<path class="s1" d="{path([r["load"] for r in sel], y, h1, 0, top1)}"/>')
    p.append(f'<path class="s2" d="{path([r["pv"] for r in sel], y, h1, 0, top1)}"/>')
    for r in sel:
        if r["spike"]:
            yy = y + h1 - h1 * min(r["load"], top1) / top1
            right = x(r["n"]) > L + PW - 230
            p.append(f'<text class="note" x="{x(r["n"]) + (-6 if right else 6):.1f}" '
                     f'y="{yy + 4:.1f}" text-anchor="{"end" if right else "start"}">'
                     f'{spike_note(rows, r["n"])}</text>')
    panels.append(("load", y, h1, 0, top1))
    out.append("".join(p))
    y += h1 + 44

    # Panel 2: battery power inside the inverter's limits.
    h2 = 210
    lo2, hi2 = -5000, 5000
    p = [f'<text class="ptitle" x="{L}" y="{y}">Battery power and the inverter’s limits, W '
         f'(positive charges)</text>',
         legend(L, y + 18, [("line", "k3", "Battery power"), ("rect", "bandkey", "Limits in force, from the inverter’s read-back: the commanded limits, or the fallback interval of −50 to +50 W")])]
    y += 30
    p.append(axis_x(y, h2, False) + axis_y(y, h2, lo2, hi2, 2500, fmtw))
    p.append(f'<path class="band3" d="{band([r["limLow"] for r in sel], [r["limHigh"] for r in sel], y, h2, lo2, hi2)}"/>')
    p.append(f'<path class="s3" d="{path([r["battery"] for r in sel], y, h2, lo2, hi2)}"/>')
    panels.append(("battery", y, h2, lo2, hi2))
    out.append("".join(p))
    y += h2 + 44

    # Panel 3: stored energy.
    h3 = 150
    lo3, hi3 = 0, 10
    kwh = lambda j: j / 3.6e6
    p = [f'<text class="ptitle" x="{L}" y="{y}">Stored energy, kWh</text>',
         legend(L, y + 18, [("rect", "bandkeye", "The energy interval that the gateway receives: the simulated energy ±0.1 kWh"), ("line", "ref", "The site’s floor and ceiling")])]
    y += 30
    p.append(axis_x(y, h3, False) + axis_y(y, h3, lo3, hi3, 2, lambda v: f"{v:g}"))
    for j, name in ((FLOOR_J, "floor 3.0"), (CEILING_J, "ceiling 9.5")):
        yy = y + h3 - h3 * (kwh(j) - lo3) / (hi3 - lo3)
        p.append(f'<line class="ref" x1="{L}" x2="{L + PW}" y1="{yy:.1f}" y2="{yy:.1f}"/>'
                 f'<text class="note" x="{L + PW - 4}" y="{yy - 5:.1f}" text-anchor="end">{name}</text>')
    p.append(f'<path class="band3e" d="{band([kwh(r["eLow"]) for r in sel], [kwh(r["eHigh"]) for r in sel], y, h3, lo3, hi3)}"/>')
    panels.append(("energy", y, h3, lo3, hi3))
    out.append("".join(p))
    y += h3 + 44

    # Panel 4: decisions, one lane each.
    lanes = [("Accepted", 0), ("Rejected", 1), ("In force", 2), ("Fallback", 3)]
    lh = 30
    p = [f'<text class="ptitle" x="{L}" y="{y}">Gateway decisions</text>',
         legend(L, y + 18, [("rect", "okkey2", "Proposal accepted: a command sent"),
                            ("rect", "rejkey", "Proposal rejected"),
                            ("rect", "skipkey", "Proposal not considered (fallback tick)"),
                            ("rect", "okkey", "Command in force"),
                            ("square", "fb", "Request to return to fallback")])]
    y += 30
    h4 = lh * len(lanes)
    p.append(axis_x(y, h4, True))
    for name, k in lanes:
        yy = y + lh * k + lh / 2
        p.append(f'<text class="lane" x="{L - 8}" y="{yy + 4:.1f}" text-anchor="end">{name}</text>')
    lane_y = lambda k: y + lh * k + 8
    for r in sel:
        if r["proposal"]:
            k, cls = {1: (0, "okt"), 0: (1, "rejt"), 2: (1, "skipt")}[r["kind"]]
            p.append(f'<rect class="{cls}" x="{x(r["n"]) - 1:.1f}" y="{lane_y(k)}" width="2" '
                     f'height="14" rx="1"/>')
    start = None
    for r in sel + [None]:
        on = r is not None and r["mode"] == "command"
        if on and start is None:
            start = r["n"]
        if not on and start is not None:
            end = (r["n"] if r is not None else t1 + 1) - 1
            p.append(f'<rect class="okbar" x="{x(start):.1f}" y="{lane_y(2) + 1}" '
                     f'width="{max(x(min(end + 1, t1)) - x(start) - 2, 2):.1f}" height="12" rx="3"/>')
            start = None
    for r in sel:
        if r["kind"] == 2:
            why = fallback_reason(rows, r["n"])
            p.append(f'<rect class="fb" x="{x(r["n"]) - 5:.1f}" y="{lane_y(3) + 2}" width="10" '
                     f'height="10" rx="2"/>'
                     f'<text class="note" x="{x(r["n"]) + 9:.1f}" y="{lane_y(3) + 11}">{why}</text>')
    panels.append(("decisions", y, h4, 0, 1))
    out.append("".join(p))
    y += h4 + 36
    height = y

    svg = (f'<svg id="chart" viewBox="0 0 {W} {height}" role="img" aria-labelledby="ctitle">'
           f'<title id="ctitle">The gateway’s run, minute by minute</title>{"".join(out)}'
           f'<line id="cross" class="cross" x1="0" x2="0" y1="0" y2="{height - 30}" '
           f'visibility="hidden"/>'
           f'<rect id="hit" x="{L}" y="0" width="{PW}" height="{height}" fill="transparent"/></svg>')

    ev = events(rows)
    counts = {
        "commands": sum(r["kind"] == 1 for r in rows),
        "fallback": sum(r["kind"] == 2 for r in rows),
        "proposals": sum(r["proposal"] for r in rows),
        "rejected": sum(r["proposal"] and r["kind"] == 0 for r in rows),
        "skipped": sum(r["proposal"] and r["kind"] == 2 for r in rows),
        "inForce": sum(r["mode"] == "command" for r in rows),
    }
    rej = {}
    for r in rows:
        if r["proposal"] and r["kind"] == 0:
            rej[r["status"]] = rej.get(r["status"], 0) + 1
    return svg, ev, counts, rej, {"L": L, "PW": PW, "n": n, "W": W, "t0": t0, "t1": t1}


def document(rows, meta, records, t0=0, t1=None):
    svg, ev, counts, rej, geo = page(rows, meta, t0, t1)
    e = html.escape
    rej_text = ", ".join(f"{c:,} for {STATUS[s]}" for s, c in sorted(rej.items()))
    facts = "".join(f"<tr><th>{e(k)}</th><td>{e(v)}</td></tr>" for k, v in meta.get("facts", []))
    minus = lambda t: t.replace("-", "\u2212")
    row = lambda n, k, d: (f"<tr><td>{n:,}</td><td>{hhmm(n)}</td><td>{e(k)}</td>"
                           f"<td>{e(minus(d))}</td></tr>")
    ev_rows = "".join(row(*x) for x in ev if x[1] != "proposal rejected")
    rej_rows = "".join(row(*x) for x in ev if x[1] == "proposal rejected")
    def record_row(r):
        proposed = f"{r['propLow']:,} to {r['propHigh']:,}" if r["proposal"] else ""
        output = ["nothing", "command", "fallback request"][r["kind"]]
        if r["kind"] == 1:
            output += f" {r['outLow']:,} to {r['outHigh']:,}"
        return (f"<tr><td>{r['n']:,}</td><td>{hhmm(r['n'])}</td><td>{r['load']:,}</td>"
                f"<td>{r['pv']:,}</td><td>{r['battery']:,}</td><td>{r['mode']}</td>"
                f"<td>{r['limLow']:,} to {r['limHigh']:,}</td>"
                f"<td>{r['eLow'] / 3.6e6:.3f} to {r['eHigh'] / 3.6e6:.3f}</td>"
                f"<td>{proposed}</td><td>{output}</td><td>{STATUS[r['status']]}</td></tr>")

    rec_rows = "".join(record_row(r) for r in rows)
    data = json.dumps([[r["n"], r["load"], r["pv"], r["battery"], r["mode"], r["limLow"],
                        r["limHigh"], round(r["eLow"] / 3.6e6, 3), round(r["eHigh"] / 3.6e6, 3),
                        r["propLow"], r["propHigh"], r["kind"], r["outLow"], r["outHigh"],
                        STATUS[r["status"]], r["spike"]] for r in rows])
    return TEMPLATE.format(
        title=e(meta.get("title", "Energy controller run")),
        lede=e(meta.get("lede", "")),
        n=f"{len(rows):,}", commands=f"{counts['commands']:,}", fallback=f"{counts['fallback']:,}",
        proposals=f"{counts['proposals']:,}", rejected=f"{counts['rejected']:,}",
        rejtext=e(rej_text) or "none", skipped=f"{counts['skipped']:,}", inforce=f"{counts['inForce']:,}",
        facts=facts, svg=svg, events=ev_rows, rejected_rows=rej_rows, records=rec_rows,
        data=data, nrej=f"{sum(1 for x in ev if x[1] == 'proposal rejected'):,}",
        L=geo["L"], PW=geo["PW"], W=geo["W"], T0=geo["t0"], T1=geo["t1"], prose=meta.get("prose_html", ""),
        summary=summary(rows))


TEMPLATE = """<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<style>
:root {{
  color-scheme: light;
  --surface: #fcfcfb; --page: #f9f9f7; --ink: #0b0b0b; --ink2: #52514e; --muted: #898781;
  --grid: #e1e0d9; --base: #c3c2b7; --ring: rgba(11,11,11,0.10);
  --s1: #2a78d6; --s2: #eb6834; --s3: #1baf7a;
  --good: #0ca30c; --serious: #ec835a; --critical: #d03b3b;
  --band: 0.18; --barop: 0.35;
}}
@media (prefers-color-scheme: dark) {{
  :root:where(:not([data-theme="light"])) {{
    color-scheme: dark;
    --surface: #1a1a19; --page: #0d0d0d; --ink: #f0efec; --ink2: #c3c2b7; --muted: #898781;
    --grid: #2c2c2a; --base: #383835; --ring: rgba(255,255,255,0.10);
    --s1: #3987e5; --s2: #d95926; --s3: #199e70;
    --band: 0.28; --barop: 0.55;
  }}
}}
:root[data-theme="dark"] {{
  color-scheme: dark;
  --surface: #1a1a19; --page: #0d0d0d; --ink: #f0efec; --ink2: #c3c2b7; --muted: #898781;
  --grid: #2c2c2a; --base: #383835; --ring: rgba(255,255,255,0.10);
  --s1: #3987e5; --s2: #d95926; --s3: #199e70;
    --band: 0.28; --barop: 0.55;
}}
body {{ margin: 0; background: var(--page); color: var(--ink);
  font: 15px/1.5 system-ui, -apple-system, "Segoe UI", sans-serif; }}
main {{ max-width: 1240px; margin: 0 auto; padding: 24px 16px 48px; }}
h1 {{ font-size: 24px; margin: 0 0 6px; }}
h2 {{ font-size: 18px; margin: 32px 0 8px; }}
p {{ max-width: 920px; color: var(--ink2); }}
.tiles {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(170px, 1fr)); gap: 12px;
  margin: 20px 0; }}
.tile {{ background: var(--surface); border: 1px solid var(--ring); border-radius: 8px;
  padding: 12px 14px; }}
.tile .label {{ color: var(--ink2); font-size: 13px; }}
.tile .value {{ font-size: 26px; font-weight: 600; }}
.tile .sub {{ color: var(--muted); font-size: 12px; }}
.card {{ background: var(--surface); border: 1px solid var(--ring); border-radius: 8px;
  padding: 16px 12px 8px; position: relative; }}
svg {{ width: 100%; height: auto; display: block; }}
.ptitle {{ fill: var(--ink); font-size: 14px; font-weight: 600; }}
.legend text, .lane {{ fill: var(--ink2); font-size: 12px; }}
.tick {{ fill: var(--muted); font-size: 11px; font-variant-numeric: tabular-nums; }}
.note {{ fill: var(--ink2); font-size: 11px; }}
.grid {{ stroke: var(--grid); stroke-width: 1; }}
.base {{ stroke: var(--base); stroke-width: 1; }}
.ref {{ stroke: var(--muted); stroke-width: 1; }}
.s1, .s2, .s3 {{ fill: none; stroke-width: 1.5; stroke-linejoin: round; stroke-linecap: round; }}
.s1 {{ stroke: var(--s1); }} .s2 {{ stroke: var(--s2); }} .s3 {{ stroke: var(--s3); }}
.k1, .k2, .k3 {{ stroke-width: 2; stroke-linecap: round; }}
.k1 {{ stroke: var(--s1); }} .k2 {{ stroke: var(--s2); }} .k3 {{ stroke: var(--s3); }}
.band3, .bandkey {{ fill: var(--s3); opacity: var(--band); }}
.bandkeye {{ fill: var(--s3); opacity: 0.55; }}
.okkey {{ fill: var(--good); opacity: var(--barop); }}
.skip {{ fill: var(--muted); stroke: var(--surface); stroke-width: 2; }}
.okt, .okkey2 {{ fill: var(--good); }}
.rejt, .rejkey {{ fill: var(--serious); }}
.skipt, .skipkey {{ fill: var(--muted); }}
.band3e {{ fill: var(--s3); opacity: 0.55; }}
.ok {{ fill: var(--good); stroke: var(--surface); stroke-width: 2; }}
.rej {{ fill: var(--serious); stroke: var(--surface); stroke-width: 2; }}
.okbar {{ fill: var(--good); opacity: var(--barop); }}
.fb {{ fill: var(--critical); stroke: var(--surface); stroke-width: 2; }}
.cross {{ stroke: var(--ink2); stroke-width: 1; }}
#tip {{ position: absolute; pointer-events: none; background: var(--surface); color: var(--ink);
  border: 1px solid var(--ring); border-radius: 6px; padding: 8px 10px; font-size: 12px;
  box-shadow: 0 2px 8px rgba(0,0,0,0.15); display: none; min-width: 230px; }}
#tip b {{ font-size: 13px; }}
#tip table {{ border-collapse: collapse; }}
#tip td {{ padding: 1px 6px 1px 0; }}
#tip td:first-child {{ color: var(--ink2); }}
table.data {{ border-collapse: collapse; font-size: 13px; font-variant-numeric: tabular-nums; }}
table.data th, table.data td {{ border-bottom: 1px solid var(--grid); padding: 4px 10px 4px 0;
  text-align: left; vertical-align: top; }}
table.facts th {{ color: var(--ink2); font-weight: normal; padding-right: 16px; }}
details {{ margin: 12px 0; }}
summary {{ cursor: pointer; color: var(--ink2); }}
.wrap {{ overflow-x: auto; }}
</style></head>
<body><main>
<h1>{title}</h1>
<p>{lede}</p>
<div class="tiles">
<div class="tile"><div class="label">Ticks, one a minute</div><div class="value">{n}</div></div>
<div class="tile"><div class="label">Commands sent to the inverter</div><div class="value">{commands}</div>
<div class="sub">in force for {inforce} minutes</div></div>
<div class="tile"><div class="label">Proposals</div><div class="value">{proposals}</div>
<div class="sub">{rejected} rejected ({rejtext}); {skipped} not considered, on a tick that requested fallback</div></div>
<div class="tile"><div class="label">Requests to return to fallback</div><div class="value">{fallback}</div></div>
</div>
<div class="card" id="card">{svg}<div id="tip" role="status"></div></div>
{summary}
{prose}
<h2>Facts of the run</h2>
<table class="data facts">{facts}</table>
<h2>Commands, fallback requests, and load spikes</h2>
<div class="wrap"><table class="data"><thead><tr><th>Tick</th><th>Time</th><th>Event</th>
<th>Detail</th></tr></thead><tbody>{events}</tbody></table></div>
<details><summary>The {nrej} rejected proposals</summary>
<div class="wrap"><table class="data"><thead><tr><th>Tick</th><th>Time</th><th>Event</th>
<th>Detail</th></tr></thead><tbody>{rejected_rows}</tbody></table></div></details>
<details><summary>All records, one row a tick</summary>
<div class="wrap"><table class="data"><thead><tr><th>Tick</th><th>Time</th><th>Load W</th>
<th>PV W</th><th>Battery W</th><th>Inverter</th><th>Limits W</th><th>Energy kWh</th>
<th>Proposed W</th><th>Output</th><th>Status</th></tr></thead><tbody>{records}</tbody></table></div>
</details>
</main>
<script>
const D = {data};
const L = {L}, PW = {PW}, W = {W}, T0 = {T0}, T1 = {T1};
const svg = document.getElementById('chart'), hit = document.getElementById('hit');
const cross = document.getElementById('cross'), tip = document.getElementById('tip');
const card = document.getElementById('card');
const fmt = v => v === null ? '' : v.toLocaleString('en-US').replace('-', '\\u2212');
const hm = n => String(Math.floor(n / 60)).padStart(2, '0') + ':' + String(n % 60).padStart(2, '0');
function row(t, label, value) {{
  const tr = document.createElement('tr');
  const a = document.createElement('td'); a.textContent = label;
  const b = document.createElement('td'); const s = document.createElement('b');
  s.textContent = value; b.appendChild(s); tr.append(a, b); t.appendChild(tr);
}}
function show(ev) {{
  const pt = svg.createSVGPoint(); pt.x = ev.clientX; pt.y = ev.clientY;
  const p = pt.matrixTransform(svg.getScreenCTM().inverse());
  const i = Math.max(T0, Math.min(T1, T0 + Math.round((p.x - L) / PW * (T1 - T0))));
  const d = D[i]; const xx = L + PW * (i - T0) / Math.max(T1 - T0, 1);
  cross.setAttribute('x1', xx); cross.setAttribute('x2', xx); cross.setAttribute('visibility', 'visible');
  tip.replaceChildren();
  const head = document.createElement('div'); head.textContent = 'Tick ' + fmt(d[0]) + ', ' + hm(d[0]);
  tip.appendChild(head);
  const t = document.createElement('table');
  row(t, 'Load', fmt(d[1]) + ' W' + (d[15] ? ' (spike)' : ''));
  row(t, 'PV', fmt(d[2]) + ' W');
  row(t, 'Battery', fmt(d[3]) + ' W');
  row(t, 'Inverter', d[4] + ', ' + fmt(d[5]) + ' to ' + fmt(d[6]) + ' W');
  row(t, 'Energy', d[7].toFixed(3) + ' to ' + d[8].toFixed(3) + ' kWh');
  if (d[9] !== null) row(t, 'Proposal', fmt(d[9]) + ' to ' + fmt(d[10]) + ' W');
  row(t, 'Output', ['nothing', 'command ' + fmt(d[12]) + ' to ' + fmt(d[13]) + ' W', 'fallback request'][d[11]]);
  row(t, 'Last snapshot', d[14]);
  tip.appendChild(t); tip.style.display = 'block';
  const r = card.getBoundingClientRect(), sx = ev.clientX - r.left;
  tip.style.left = (sx + 250 > r.width ? sx - 250 : sx + 14) + 'px';
  tip.style.top = (ev.clientY - r.top + 12) + 'px';
}}
hit.addEventListener('pointermove', show);
hit.addEventListener('pointerleave', () => {{ tip.style.display = 'none'; cross.setAttribute('visibility', 'hidden'); }});
</script>
</body></html>
"""


def main():
    if len(sys.argv) not in (4, 6):
        raise SystemExit(__doc__.split("Usage:")[1].strip().split("\n")[0])
    records, meta_path, output = sys.argv[1:4]
    t0, t1 = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) == 6 else (0, None)
    with open(meta_path) as f:
        meta = json.load(f)
    rows = ticks(records)
    with open(output, "w") as f:
        f.write(document(rows, meta, records, t0, t1))
    print(f"{output}: {len(rows)} ticks")


main()
