# /// script
# requires-python = ">=3.12"
# dependencies = ["matplotlib==3.11.2"]
# ///
"""Draws a run of tests/baremetal/uart_bms.py from its files PREFIX.in, PREFIX.out, and PREFIX.log,
whose formats Demos/Bms/Host.md gives, and writes OUTPUT.png and OUTPUT.md.

The figure's panels share one time axis, in seconds from the start of the run.  From the top they
show the cell voltages against V_max and V_min, the temperatures against their limits, the pack
current against the current limits, the pack and bus voltages, the pack voltage minus the sum of
the cells against tol_sum, the relays (the permit bits of the answers, the coils that the bridge
energized, and the auxiliary contacts that the records report), the state of the answers, and
their diagnostic codes.  Alternating bands and the numbers in the top row mark the scenarios, and
a key under the axis names them.  OUTPUT.md holds a summary, the figure, and a table of events:
scenario starts with their results, injections, board resets, the bytes that the bridge discarded
at power-up or after a board reset, timeouts, lease expiries, and each answer that changed the
state or the code, was not current, arrived after a timeout, or changed the leases or the coils,
with the check behind a fault, the answered record, and the bridge's actions.

The records come from PREFIX.in, split into segments by the framing of bms_proto.py, and the
answers from PREFIX.out, decoded by the same module, so that the k-th answer after a board reset
answers the k-th non-empty segment after it.  PREFIX.log gives the times, the scenario names, and
the bridge's actions, and its k-th line "tx" and k-th line "rx" must equal the k-th write of
PREFIX.in and the k-th answer of PREFIX.out.  A record's readings are drawn at its sampling, the
line "sample" with the same bytes, and only for segments that decode to 35 bytes with a matching
CRC.  An answer holds from its arrival to the next answer or a board reset, and the lines of the
readings break where no record arrived for more than GAP seconds.  In the schedule's runs two
drawn records lie at most 0.52 s apart except across the bridge's silence and a board reset that
takes time, such as the reset command's on the board.

Usage: uv run tests/baremetal/bms_report.py PREFIX OUTPUT
"""

import os
import sys
from dataclasses import dataclass, field

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Patch
from matplotlib.ticker import MaxNLocator
from matplotlib.transforms import blended_transform_factory

import bms_proto as bp
from bms_proto import FAULT, NORMAL, PRECHARGE, RESET_REQUIRED, STANDBY, STATES
from uart_bms import RELAYS, T_LEASE

GAP = 1.0

CODES = {
    0x0000: "no fault",
    0x0001: "board reset",
    0x1001: "COBS decode error",
    0x1002: "segment overflow",
    0x1003: "length other than 35 bytes",
    0x1004: "CRC mismatch",
    0x1005: "tag other than 0x10",
    0x1006: "unexpected sequence number",
    0x1007: "nonzero reserved bit",
    0x2001: "reading out of sensor range",
    0x2002: "cell overvoltage",
    0x2003: "cell undervoltage",
    0x2004: "overtemperature",
    0x2005: "undertemperature",
    0x2006: "charge overcurrent",
    0x2007: "discharge overcurrent",
    0x2008: "charging outside 0 to 45 °C",
    0x2009: "cell sum differs from pack",
    0x3001: "auxiliary contact disagrees",
    0x3002: "precharge timeout",
    0x5001: "stop demanded",
}

INK, INK2, MUTED = "#0b0b0b", "#52514e", "#898781"
GRID, SURFACE, BAND = "#e1e0d9", "#fcfcfb", "#efeee9"
SERIES = ("#2a78d6", "#eb6834", "#1baf7a", "#eda100")
STATE_COLORS = {RESET_REQUIRED: "#ec835a", STANDBY: MUTED, PRECHARGE: "#fab219", NORMAL: "#0ca30c",
                FAULT: "#d03b3b"}


@dataclass
class Reply:
    """An answer that the bridge received, with what the log records of it."""
    t: float
    frame: bytes
    part: int
    scenario: int
    answer: bp.Answer | None
    applied: str | None = None
    dropped: bool = False
    inauthentic: bytes | None = None
    late: bool = False
    revoked: list = field(default_factory=list)
    coils: tuple | None = None
    segment: object = None
    prev: bp.Answer | None = None
    expected: int | None = None


@dataclass
class Expiry:
    t: float
    scenario: int
    relays: list
    ends: list
    coils: tuple | None = None


@dataclass
class Note:
    t: float
    scenario: int
    event: str
    detail: str
    coils: tuple | None = None
    where: str = ""
    data: str = ""


@dataclass
class Part:
    """The bytes written between two board resets and the answers received."""
    stream: bytearray = field(default_factory=bytearray)
    replies: list = field(default_factory=list)


@dataclass
class Run:
    parts: list
    items: list
    samples: dict
    sampled: list
    coils: list
    scenarios: list
    resets: list
    end: float
    timeouts: int
    records: list = field(default_factory=list)


def lines(path):
    with open(path) as f:
        return [line.strip() for line in f if line.strip()]


def read_log(path):
    events = []
    with open(path) as f:
        for n, line in enumerate(f, 1):
            parts = line.rstrip("\n").split(" ", 2)
            if len(parts) < 2:
                raise SystemExit(f"{path}:{n}: no event")
            events.append((float(parts[0]) / 1000, parts[1], parts[2] if len(parts) > 2 else ""))
    return events


def load(prefix):
    ins, outs = lines(prefix + ".in"), lines(prefix + ".out")
    events = read_log(prefix + ".log")
    i = o = 0
    parts = [Part()]
    items, samples, sampled, coils, scenarios, resets = [], {}, [], [(0.0, 0)], [], []
    scenario, cause, timeouts, late = 0, None, 0, False

    def take(lst, k, value, name):
        if k >= len(lst) or lst[k] != value:
            raise SystemExit(f"line {k + 1} of {prefix}.{name} differs from the log's "
                             f"{'board reset' if value == 'reset' else value}")

    for t, kind, text in events:
        if kind not in ("revoke", "coils", "answer", "drop", "inauthentic", "expire"):
            cause = None
        if kind == "tx":
            take(ins, i, text, "in")
            i += 1
            parts[-1].stream += bytes.fromhex(text)
        elif kind == "board-reset":
            take(ins, i, "reset", "in")
            take(outs, o, "reset", "out")
            i, o = i + 1, o + 1
            parts.append(Part())
            resets.append(t)
            items.append(Note(t, scenario, "board reset", "The bridge resets the board."))
        elif kind == "rx":
            take(outs, o, text, "out")
            o += 1
            frame = bytes.fromhex(text)
            try:
                answer = bp.decode_answer(bp.cobs_decode(frame[:-1]))
            except bp.DecodeError:
                answer = None
            cause = Reply(t, frame, len(parts) - 1, scenario, answer, late=late)
            parts[-1].replies.append(cause)
            items.append(cause)
        elif kind == "answer":
            cause.applied = text.split()[-1]
        elif kind == "drop":
            cause.dropped = True
        elif kind == "inauthentic":
            cause.inauthentic = bytes.fromhex(text)
        elif kind == "revoke":
            relay, how = text.split()
            cause.revoked.append((relay, how))
        elif kind == "expire":
            relay, end = text.split()
            if not isinstance(cause, Expiry):
                cause = Expiry(t, scenario, [], [])
                items.append(cause)
            cause.relays.append(relay)
            cause.ends.append(float(end) / 1000)
        elif kind == "coils":
            mask = int(text, 16)
            change = (coils[-1][1], mask)
            coils.append((t, mask))
            if cause is not None and cause.coils is None:
                cause.coils = change
            else:
                items.append(Note(t, scenario, "relays", "", change))
            cause = None
        elif kind == "sample":
            seq, raw = text.split()
            samples[raw] = t
            sampled.append((int(seq), t))
            late = False
        elif kind == "scenario":
            scenario += 1
            scenarios.append([t, None, text, "incomplete"])
            items.append(Note(t, scenario, "scenario", ""))
        elif kind == "result":
            name, result = text.split()
            scenarios[-1][1:] = [t, name, result]
        elif kind == "inject":
            items.append(Note(t, scenario, "injection", text[0].upper() + text[1:] + "."))
        elif kind == "discard":
            where, data = text.split()
            if not (items and isinstance(items[-1], Note) and items[-1].event == "discard"
                    and items[-1].where == where):
                items.append(Note(t, scenario, "discard", "", where=where))
            items[-1].data += data
        elif kind == "timeout":
            timeouts += 1
            late = True
            items.append(Note(t, scenario, "timeout", "No current answer within T_ans of the "
                                                      "record's end.  The bridge sends `0x00`."))
    if i != len(ins) or o != len(outs):
        raise SystemExit(f"{prefix}.in has {len(ins) - i} and {prefix}.out {len(outs) - o} lines "
                         f"that the log does not record")
    end = events[-1][0]
    for s in scenarios:
        if s[1] is None:
            s[1] = end
    for item in items:
        if isinstance(item, Note) and item.event == "scenario":
            name, result = scenarios[item.scenario - 1][2:]
            item.detail = f"`{name}`: {result}."
    run = Run(parts, items, samples, sampled, coils, scenarios, resets, end, timeouts)
    pair(run, prefix)
    return run


def pair(run, prefix):
    """Gives each answer the segment it answers, the answer before it, and the sequence number
    that the board expected, and collects the records' readings."""
    for p, part in enumerate(run.parts):
        segs = bp.segments(bytes(part.stream))
        if len(part.replies) > len(segs):
            raise SystemExit(f"{len(part.replies)} answers to {len(segs)} segments in part {p} of "
                             f"{prefix}.in")
        prev, synced, expected = None, False, 0
        for reply, x in zip(part.replies, segs):
            reply.segment, reply.prev = x, prev
            reply.expected = expected if synced else None
            synced = bp.good(x)
            if synced:
                expected = (bp.decode_scan(x).seq + 1) % (1 << 32)
            if reply.answer is not None:
                prev = reply.answer
        for x in segs:
            if bp.record_ok(x):
                if x.hex() not in run.samples:
                    raise SystemExit(f"the record {x.hex()} has no sampling in {prefix}.log")
                run.records.append((run.samples[x.hex()], bp.decode_scan(x)))
    run.records.sort(key=lambda r: r[0])


def num(v):
    return f"{v:,}".replace("-", "−")


def deg(tenths):
    return f"{tenths / 10:.1f}".replace("-", "−") + " °C"


def names(items):
    """The items joined with commas and "and", with the serial comma."""
    items = list(items)
    if len(items) < 3:
        return " and ".join(items)
    return ", ".join(items[:-1]) + ", and " + items[-1]


def bits(mask):
    return [RELAYS[r] for r in range(3) if mask >> r & 1]


def fault_detail(code, x, expected, permit):
    """The readings or the segment behind the fault code of the answer to x."""
    if code == 0x1003:
        return f"the segment decodes to {len(x)} bytes"
    if code == 0x1005:
        return f"tag `{x[0]:#04x}`"
    if code < 0x1006:
        return ""
    sc = bp.decode_scan(x)
    if code == 0x1006:
        return f"record {sc.seq}, where {expected} is expected"
    if code == 0x1007:
        return f"digital word `{sc.digital:#06x}`"
    cells = lambda test: [f"cell {k} at {num(v)} mV" for k, v in enumerate(sc.cells) if test(v)]
    temps = lambda test: [f"sensor {k} at {deg(v)}" for k, v in enumerate(sc.temps) if test(v)]
    if code == 0x2001:
        out = (cells(lambda v: not bp.V_SENS_LO <= v <= bp.V_SENS_HI)
               + temps(lambda v: not bp.T_SENS_LO <= v <= bp.T_SENS_HI))
        out += [f"{n} at {num(v)} mV" for n, v in (("pack", sc.pack), ("bus", sc.bus))
                if v > bp.P_SENS_HI]
        return ", ".join(out)
    if code == 0x2002:
        return ", ".join(cells(lambda v: v > bp.V_MAX))
    if code == 0x2003:
        return ", ".join(cells(lambda v: v < bp.V_MIN))
    if code == 0x2004:
        return ", ".join(temps(lambda v: v > bp.T_MAX))
    if code == 0x2005:
        return ", ".join(temps(lambda v: v < bp.T_MIN))
    if code in (0x2006, 0x2007):
        return f"current {num(sc.current)} mA"
    if code == 0x2008:
        return f"current {num(sc.current)} mA with " + ", ".join(
            temps(lambda v: not bp.T_CHG_MIN <= v <= bp.T_CHG_MAX))
    if code == 0x2009:
        return f"pack {num(sc.pack)} mV, cell sum {num(sum(sc.cells))} mV"
    if code == 0x3001:
        aux = sc.digital & 7
        out = [f"{RELAYS[r]} reports {'closed' if aux >> r & 1 else 'open'} with its permit bit "
               f"{'set' if permit >> r & 1 else 'clear'}"
               for r in range(3) if (aux ^ permit) >> r & 1]
        return ", ".join(out)
    if code == 0x3002:
        return (f"{bp.N_PC} records without the precharge condition, the last with bus "
                f"{num(sc.bus)} mV and pack {num(sc.pack)} mV")
    return ""


def transition(reply):
    """Why the answer's state or code differs from the answer before it, or ""."""
    a, prev, x = reply.answer, reply.prev, reply.segment
    if prev is None:
        first = "First answer after the board reset" if reply.part else "First answer of the run"
        if a.state != FAULT:
            return first
        detail = fault_detail(a.code, x, reply.expected, 0)
        return f"{first}: {CODES.get(a.code, 'unknown code')}" + (f", {detail}" if detail else "")
    if (prev.state, prev.code) == (a.state, a.code):
        return ""
    lead = f"From `{STATES[prev.state]}`: "
    if a.state == FAULT:
        detail = fault_detail(a.code, x, reply.expected, prev.permit)
        return lead + CODES.get(a.code, "unknown code") + (f", {detail}" if detail else "")
    if a.state == RESET_REQUIRED and a.code == 0x5001:
        return lead + "stop, `STOP_OK` 0"
    if a.state == STANDBY:
        return lead + ("reset accepted" if prev.state in (RESET_REQUIRED, FAULT) else "`RUN` 0")
    if a.state == PRECHARGE:
        return lead + "start"
    if a.state == NORMAL:
        sc = bp.decode_scan(x)
        return lead + f"precharge condition, bus {num(sc.bus)} mV and pack {num(sc.pack)} mV"
    return lead.rstrip(": ")


def coils_actions(change):
    if change is None:
        return []
    before, after = change
    out = []
    if after & ~before:
        out.append(f"energizes {names(bits(after & ~before))}")
    if before & ~after:
        out.append(f"de-energizes {names(bits(before & ~after))}")
    return out


def bridge(actions):
    """A sentence of the bridge's actions, or ""."""
    return f"The bridge {names(actions)}." if actions else ""


def reply_row(reply):
    """The table row of an answer, or None when the answer changes nothing worth a row."""
    a = reply.answer
    if a is None:
        return ("not authentic", f"A frame of {len(reply.frame) - 1} bytes that is not an "
                                 f"authentic answer.")
    why = transition(reply)
    applied = reply.applied
    if not (why or applied != "current" or reply.late or reply.revoked or reply.coils):
        return None
    record = f"record {a.answered}" if bp.record_ok(reply.segment) else "a damaged segment"
    text = [why + "." if why else ""]
    if reply.dropped and reply.inauthentic is not None:
        lost = len(reply.frame) - 1 - len(reply.inauthentic)
        text.append(f"Answer {a.board} to {record}.  The injection dropped {lost} of its bytes, "
                    f"and the bridge read the other {len(reply.inauthentic)} as a frame that is "
                    f"not an authentic answer.")
    elif reply.dropped:
        text.append(f"Answer {a.board} to {record}, dropped by the injection.")
    else:
        text.append(f"Answer {a.board} to {record}, "
                    f"{'current' if applied == 'current' else 'not current'}"
                    + (", after the timeout." if reply.late else "."))
    ended = [r for r, _ in reply.revoked]
    actions = coils_actions(reply.coils)
    if ended:
        if actions == [f"de-energizes {names(ended)}"]:
            actions = [f"de-energizes {'them' if len(ended) > 1 else 'it'}"]
        actions.insert(0, f"ends the lease{'s' if len(ended) > 1 else ''} of {names(ended)}")
    text.append(bridge(actions))
    if any(how == "other" for _, how in reply.revoked):
        text.append("BR6 blocks re-energization.")
    return f"`{a}`", "  ".join(s for s in text if s)


def expiry_text(run, item):
    """The leases that ended, the records whose answers granted them, and the release."""
    text = []
    for end in sorted(set(item.ends)):
        relays = [r for r, e in zip(item.relays, item.ends) if e == end]
        seqs = [seq for seq, t in run.sampled if abs(t + T_LEASE - end) < 2e-6]
        plural = len(relays) > 1
        text.append(f"The lease{'s' if plural else ''} of {names(relays)} "
                    + (f"from the answer to record {seqs[-1]} " if seqs else "")
                    + f"end{'' if plural else 's'} {1000 * T_LEASE:.0f} ms after the record's "
                    f"sampling, and BR6 blocks re-energization.")
    if item.coils:
        lag = 1000 * (item.t - max(item.ends))
        text.append(bridge(coils_actions(item.coils))[:-1] + f" {lag:.1f} ms after the end.")
    return "  ".join(text)


def table(run):
    rows = []
    for item in run.items:
        if isinstance(item, Reply):
            row = reply_row(item)
            if row:
                rows.append((item.t, item.scenario) + row)
        elif isinstance(item, Expiry):
            rows.append((item.t, item.scenario, "lease expiry", expiry_text(run, item)))
        elif item.event == "discard":
            when = "at power-up" if item.where == "power-up" else "after the board reset"
            rows.append((item.t, item.scenario, "discarded bytes",
                         f"The bridge discards `{item.data}`, received {when} before its next "
                         f"write."))
        else:
            detail = "  ".join(s for s in [item.detail, bridge(coils_actions(item.coils))] if s)
            rows.append((item.t, item.scenario, item.event, detail))
    return rows


def spans(points, stops, end):
    """The intervals (t0, t1, value) of a step function given by points (t, value): each value
    holds until the next point or the first stop after it, and the last until end."""
    out = []
    for k, (t, v) in enumerate(points):
        nxt = points[k + 1][0] if k + 1 < len(points) else end
        stop = min([s for s in stops if s > t] + [nxt])
        out.append((t, stop, v))
    return out


def broken(times, values):
    """The series with a gap wherever consecutive times lie more than GAP apart."""
    xs, ys = [], []
    for k, (t, v) in enumerate(zip(times, values)):
        if k and t - times[k - 1] > GAP:
            xs.append(float("nan"))
            ys.append(float("nan"))
        xs.append(t)
        ys.append(v)
    return xs, ys


def style(ax, end):
    ax.set_facecolor(SURFACE)
    ax.set_xlim(0, end)
    for s in ax.spines.values():
        s.set_color(GRID)
        s.set_linewidth(0.8)
    ax.tick_params(colors=MUTED, labelsize=8.5, length=0, labelbottom=False)
    ax.xaxis.set_major_locator(MaxNLocator(nbins=12, steps=[1, 2, 5, 10]))
    ax.grid(axis="x", color=GRID, linewidth=0.6)
    ax.set_axisbelow(True)


def bands(ax, scenarios):
    for k, (t0, t1, _, _) in enumerate(scenarios):
        if k % 2:
            ax.axvspan(t0, t1, color=BAND, linewidth=0, zorder=0)


def limit(ax, y, label, dashed=False):
    ax.axhline(y, color=MUTED, linewidth=0.9, linestyle=(0, (4, 3)) if dashed else "-", zorder=1)
    ax.text(1.006, y, label, transform=blended_transform_factory(ax.transAxes, ax.transData),
            ha="left", va="center", fontsize=8, color=INK2)


def figure(run, path):
    W, LEFT, RIGHT = 16.0, 2.45, 1.35
    LANE = 0.17
    steps = spans([(r.t, r.answer) for p in run.parts for r in p.replies if r.answer],
                  run.resets, run.end)
    codes = sorted({a.code for _, _, a in steps})
    panels = [
        ("Cell voltages, V", 1.7, True),
        ("Temperatures, °C", 1.8, True),
        ("Pack current, A, positive while charging", 1.4, False),
        ("Pack and bus voltages, V", 1.3, True),
        ("Pack voltage minus the sum of the cells, mV", 1.1, False),
        ("Relays: the permit bits of the answers, the coils that the bridge energizes, and the "
         "auxiliary contacts that the records report", 9 * LANE + 0.1, True),
        ("State of the answers", 5 * LANE + 0.1, False),
        ("Diagnostic code of the answers", len(codes) * LANE + 0.1, False),
    ]
    TOP, GAPH = 0.45, 0.32
    heads = [0.58 if legend else 0.34 for _, _, legend in panels]
    cols = 5
    key_rows = -(-len(run.scenarios) // cols)
    BOTTOM = 0.75 + 0.3 + key_rows * 0.19 + 0.1
    H = TOP + sum(h for _, h, _ in panels) + sum(heads) + GAPH * (len(panels) - 1) + BOTTOM
    fig = plt.figure(figsize=(W, H), facecolor=SURFACE)
    width = (W - LEFT - RIGHT) / W
    axes, y = [], TOP
    for (title, h, _), head in zip(panels, heads):
        y += head
        ax = fig.add_axes([LEFT / W, 1 - (y + h) / H, width, h / H])
        fig.text(LEFT / W, 1 - (y - head + 0.2) / H, title, fontsize=10.5, fontweight="bold",
                 color=INK, va="baseline")
        style(ax, run.end)
        bands(ax, run.scenarios)
        axes.append(ax)
        y += h + GAPH

    top = fig.add_axes([LEFT / W, 1 - TOP / H, width, (TOP - 0.05) / H])
    top.set_xlim(0, run.end)
    top.set_ylim(0, 1)
    top.axis("off")
    top.text(-0.006, 0.5, "Scenario", transform=top.transAxes, ha="right", va="center",
             fontsize=9, color=INK2)
    for k, (t0, t1, _, _) in enumerate(run.scenarios):
        top.text((t0 + t1) / 2, 0.72 if k % 2 == 0 else 0.22, str(k + 1), ha="center",
                 va="center", fontsize=8.5, color=INK2)

    def legend(ax, handles):
        ax.legend(handles=handles, loc="lower left", bbox_to_anchor=(0, 1.0), ncol=len(handles),
                  frameon=False, borderaxespad=0.15, handlelength=1.6, columnspacing=1.6,
                  fontsize=9, labelcolor=INK2)

    times = [t for t, _ in run.records]
    recs = [sc for _, sc in run.records]

    ax = axes[0]
    for k in range(4):
        ax.plot(*broken(times, [sc.cells[k] / 1000 for sc in recs]), color=SERIES[k],
                linewidth=1.2, solid_joinstyle="round", zorder=3)
    ax.set_ylim(2.35, 3.8)
    ax.set_yticks([2.5, 2.75, 3.0, 3.25, 3.5, 3.75])
    ax.grid(axis="y", color=GRID, linewidth=0.6)
    limit(ax, bp.V_MAX / 1000, "V_max 3.650")
    limit(ax, bp.V_MIN / 1000, "V_min 2.500")
    legend(ax, [Line2D([], [], color=SERIES[k], linewidth=2, label=f"Cell {k}")
                for k in range(4)])

    ax = axes[1]
    for k in range(2):
        ax.plot(*broken(times, [sc.temps[k] / 10 for sc in recs]), color=SERIES[k],
                linewidth=1.2, zorder=3)
    ax.set_ylim(-60, 65)
    ax.set_yticks(range(-60, 61, 20))
    ax.grid(axis="y", color=GRID, linewidth=0.6)
    limit(ax, bp.T_MAX / 10, "T_max 55.0")
    limit(ax, bp.T_CHG_MAX / 10, "T_chg_max 45.0", dashed=True)
    limit(ax, bp.T_CHG_MIN / 10, "T_chg_min 0.0", dashed=True)
    limit(ax, bp.T_MIN / 10, "T_min −20.0")
    limit(ax, bp.T_SENS_LO / 10, "T_sens_lo −40.0")
    legend(ax, [Line2D([], [], color=SERIES[k], linewidth=2, label=f"Sensor {k}")
                for k in range(2)]
           + [Line2D([], [], color=MUTED, linewidth=1, label="Limit"),
              Line2D([], [], color=MUTED, linewidth=1, linestyle=(0, (4, 3)),
                     label="Limit while the current exceeds I_chg_detect, 2.8 A")])

    ax = axes[2]
    ax.plot(*broken(times, [sc.current / 1000 for sc in recs]), color=SERIES[0], linewidth=1.2,
            zorder=3)
    ax.set_ylim(-320, 320)
    ax.set_yticks(range(-300, 301, 100))
    ax.grid(axis="y", color=GRID, linewidth=0.6)
    limit(ax, bp.I_CHG_MAX / 1000, "I_chg_max 280")
    limit(ax, -bp.I_DIS_MAX / 1000, "−I_dis_max −280")

    ax = axes[3]
    ax.plot(*broken(times, [sc.pack / 1000 for sc in recs]), color=SERIES[0], linewidth=1.2,
            zorder=3)
    ax.plot(*broken(times, [sc.bus / 1000 for sc in recs]), color=SERIES[1], linewidth=1.2,
            zorder=3)
    ax.set_ylim(-0.5, 15)
    ax.set_yticks(range(0, 16, 5))
    ax.grid(axis="y", color=GRID, linewidth=0.6)
    legend(ax, [Line2D([], [], color=SERIES[0], linewidth=2, label="Pack"),
                Line2D([], [], color=SERIES[1], linewidth=2, label="Bus")])

    ax = axes[4]
    ax.plot(*broken(times, [sc.pack - sum(sc.cells) for sc in recs]), color=SERIES[0],
            linewidth=1.2, zorder=3)
    ax.set_ylim(-400, 400)
    ax.set_yticks(range(-400, 401, 200))
    ax.grid(axis="y", color=GRID, linewidth=0.6)
    limit(ax, bp.TOL_SUM, "tol_sum 300")
    limit(ax, -bp.TOL_SUM, "−tol_sum −300")

    ax = axes[5]
    lanes = [f"{n} {kind}" for n in RELAYS for kind in ("permit", "coil", "contact")]
    for r in range(3):
        permit = [(t, t1 - t) for t, t1, a in steps if a.permit >> r & 1]
        coil = [(t, t1 - t) for t, t1, m in spans(run.coils, [], run.end) if m >> r & 1]
        ax.broken_barh(permit, (3 * r - 0.3, 0.6), facecolor=SERIES[0], linewidth=0)
        ax.broken_barh(coil, (3 * r + 1 - 0.3, 0.6), facecolor=SERIES[1], linewidth=0)
        closed = [t for t, sc in run.records if sc.digital >> r & 1]
        ax.plot(closed, [3 * r + 2] * len(closed), linestyle="none", marker="|", markersize=7,
                markeredgewidth=1.4, color=SERIES[2])
    for y in (2.5, 5.5):
        ax.axhline(y, color=GRID, linewidth=0.8)
    ax.set_ylim(len(lanes) - 0.5, -0.5)
    ax.set_yticks(range(len(lanes)), lanes)
    ax.tick_params(axis="y", colors=INK2, labelsize=8.5)
    legend(ax, [Patch(color=SERIES[0], label="Permit bit set"),
                Patch(color=SERIES[1], label="Coil energized"),
                Line2D([], [], color=SERIES[2], linestyle="none", marker="|", markersize=9,
                       markeredgewidth=1.6, label="Contact reported closed, one mark a record")])

    ax = axes[6]
    for t, t1, a in steps:
        ax.broken_barh([(t, t1 - t)], (a.state - 0.3, 0.6), facecolor=STATE_COLORS[a.state],
                       linewidth=0)
    ax.set_ylim(4.5, -0.5)
    ax.set_yticks(range(5), STATES)
    ax.tick_params(axis="y", colors=INK2, labelsize=8.5)

    ax = axes[7]
    for t, t1, a in steps:
        ax.broken_barh([(t, t1 - t)], (codes.index(a.code) - 0.3, 0.6), facecolor=SERIES[0],
                       linewidth=0)
    ax.set_ylim(len(codes) - 0.5, -0.5)
    ax.set_yticks(range(len(codes)), [f"{c:#06x} {CODES.get(c, '')}" for c in codes])
    ax.tick_params(axis="y", colors=INK2, labelsize=8.5)
    ax.tick_params(axis="x", labelbottom=True)
    ax.set_xlabel("Seconds from the start of the run", color=INK2, fontsize=9, labelpad=8)

    base = 1 - (H - BOTTOM + 0.75) / H
    fig.text(LEFT / W, base, "Scenarios", fontsize=10.5, fontweight="bold", color=INK,
             va="baseline")
    colw = width / cols
    for k, (_, _, name, result) in enumerate(run.scenarios):
        c, r = divmod(k, key_rows)
        text = f"{k + 1}  {name}" + ("" if result == "pass" else f" ({result})")
        fig.text(LEFT / W + c * colw, base - (0.3 + r * 0.19) / H, text, fontsize=9,
                 color=INK2, va="baseline")
    fig.savefig(path, dpi=150, facecolor=SURFACE)
    plt.close(fig)


def markdown(run, prefix, png):
    rows = table(run)
    outcomes = [f"{k} {text}" for k, text in (
        (sum(s[3] == result for s in run.scenarios), text) for result, text in (
            ("pass", "passed"), ("fail", "failed"), ("skip", "were skipped"),
            ("incomplete", "did not finish"))) if k]
    answers = sum(len(p.replies) for p in run.parts)
    discards = any(isinstance(i, Note) and i.event == "discard" for i in run.items)
    base = os.path.basename(prefix)
    out = ["# BMS run report", "",
           f"The files `{base}.in`, `{base}.out`, and `{base}.log` hold {len(run.sampled):,} "
           f"records sent over {run.end:.1f} s, {answers:,} answers, {run.timeouts} timeouts, "
           f"and {len(run.resets)} board resets.  Of the {len(run.scenarios)} scenarios, "
           f"{names(outcomes)}.  The table lists each scenario's start, the "
           f"injections that the log records, board resets, "
           f"{'the bytes that the bridge discarded, ' if discards else ''}timeouts, lease "
           f"expiries, and each "
           f"answer that changed the state or the code, was not current, arrived after a "
           f"timeout, or changed the leases or the coils.", "",
           f"![Cell voltages, temperatures, current, pack and bus voltages, relays, states, and "
           f"codes over the run, with the scenarios numbered]({os.path.basename(png)})", "",
           "| Time, s | Scenario | Event | Detail |", "|---:|---:|---|---|"]
    for t, s, event, detail in rows:
        out.append(f"| {t:.3f} | {s or ''} | {event} | {detail} |")
    return "\n".join(out) + "\n", len(rows)


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__.strip().splitlines()[-1])
    prefix, output = sys.argv[1:]
    run = load(prefix)
    png = output + ".png"
    os.makedirs(os.path.dirname(output) or ".", exist_ok=True)
    figure(run, png)
    text, n = markdown(run, prefix, png)
    with open(output + ".md", "w") as f:
        f.write(text)
    print(f"{png}, {output}.md: {len(run.records)} records, "
          f"{sum(len(p.replies) for p in run.parts)} answers, {n} events")


if __name__ == "__main__":
    main()
