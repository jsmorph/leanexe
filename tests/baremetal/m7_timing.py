# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Cycle estimates for the windows of the Cortex-M7 back end's generated programs, from the
traces that `m7-windows run` writes to RUNDIR, with a cost model calibrated on the board's
measurements of step G0 (b) for the ITCM fetch path, whose directory BENCH holds `results.txt` and
the suites' `layout.json` (`tmp/m7/bench` of the checkout that ran them).

The model charges each executed instruction a cost by its class and each word load a penalty that
depends on the number k of instructions since the last store to the same word: 4 cycles for k up
to 2, then 6 - k, and 0 from k = 6, the shape of the hazard suite's store-then-load blocks.  The
class costs come from single blocks: a load or store 0.5 (slot_copy), a data-processing
instruction 0.615 (the mean over the register-only pair sequences), UMULL and MLA 0.99
(mulI64_reg), a conditional branch not taken 0.27 (br_not_taken less CMP and MOV) and taken 5.885
(br_taken less CMP), B.W 4.0 (b_uncond), and BL and BX LR 4.0 and 8.0, whose sum, 12, both call
blocks give.  LDRD and STRD cost 1.0 each (ldrd_copy) with one penalty per pair.  The script
prints the model's prediction for every block of the main and hazard suites beside the
measurement, then the cycles of each window trace, the cycles with every SP-relative pair of LDR
or STR whose offset lies within 1,020 bytes merged into LDRD or STRD, and the loads that reread a
word stored within the last 8 instructions with no call or return between, with the cycles of
those loads, their stores, and their penalties, which keeping the top of the operand stack in
registers would remove.

Usage: uv run tests/baremetal/m7_timing.py BENCH RUNDIR NAME...
"""
import json
import re
import sys
from pathlib import Path

COST = {"mem": 0.5, "alu": 0.615, "mul": 0.99, "bnt": 0.27, "bt": 5.885, "b": 4.0, "bl": 4.0,
        "bx": 8.0, "memd": 1.0, "div": 0.0}
SP = 0x2000F000
LINE = re.compile(r"^(\d+) (.*?)(?: @(\d+))?$")
SPOFF = re.compile(r"\[sp, #(\d+)\]")


def hazard(k):
    return max(0, min(4, 6 - k))


def kind(text):
    op = text.split()[0]
    if op in ("ldr.w", "ldr.n", "str.w", "str.n"):
        return "mem"
    if op in ("ldrd", "strd"):
        return "memd"
    if op in ("umull", "mla", "mls"):
        return "mul"
    if op == "bl":
        return "bl"
    if op == "bx":
        return "bx"
    if op == "b.w":
        return "b"
    if re.match(r"^b(eq|ne|cs|cc|mi|pl|vs|vc|hi|ls|ge|lt|gt|le)\.w$", op):
        return "bcond"
    if op == "udivmod64":
        return "div"
    return "alu"


def cost(lines):
    """Cycles of the executed lines, each (address, text, memory addresses, taken)."""
    total = 0.0
    last = {}
    for i, (_, text, addrs, taken) in enumerate(lines):
        k = kind(text)
        total += (COST["bt"] if taken else COST["bnt"]) if k == "bcond" else COST[k]
        if text.startswith("ldr"):
            ks = [i - last[a] - 1 for a in addrs if a in last]
            if ks:
                total += hazard(min(ks))
        if text.startswith("str"):
            for a in addrs:
                last[a] = i
    return total


def read_trace(path):
    raw = []
    for line in path.read_text().splitlines():
        m = LINE.match(line)
        if not m:
            raise SystemExit(f"{path}: unreadable line {line!r}")
        raw.append((int(m.group(1)), m.group(2), int(m.group(3)) if m.group(3) else None))
    lines = []
    for i, (a, text, mem) in enumerate(raw):
        taken = i + 1 < len(raw) and raw[i + 1][0] != a + 4
        lines.append((a, text, [mem] if mem is not None else [], taken))
    return lines


def merge_pairs(lines, reach=1020):
    """The lines with each SP-relative LDR or STR pair of consecutive words whose offset lies
    within `reach` merged into one LDRD or STRD, and the number of merged pairs."""
    out = []
    merged = 0
    i = 0
    while i < len(lines):
        a, text, addrs, taken = lines[i]
        if i + 1 < len(lines):
            _, text2, addrs2, _ = lines[i + 1]
            m1, m2 = SPOFF.search(text), SPOFF.search(text2)
            op1, op2 = text.split()[0], text2.split()[0]
            if (m1 and m2 and op1 == op2 and op1 in ("ldr.w", "str.w")
                    and int(m2.group(1)) == int(m1.group(1)) + 4 and int(m1.group(1)) <= reach):
                out.append((a, ("ldrd" if op1 == "ldr.w" else "strd") + " pair",
                            addrs + addrs2, False))
                merged += 1
                i += 2
                continue
        out.append(lines[i])
        i += 1
    return out, merged


def rereads(lines, window=8):
    """The number of loads that reread a word stored within `window` instructions with no BL or
    BX between, and the cycles of those loads, their stores, and their penalties."""
    last = {}
    barrier = -1
    count = 0
    cycles = 0.0
    for i, (_, text, addrs, _) in enumerate(lines):
        if kind(text) in ("bl", "bx"):
            barrier = i
        if text.startswith("ldr") and addrs:
            a = addrs[0]
            if a in last and last[a] > barrier and i - last[a] <= window:
                count += 1
                cycles += 2 * COST["mem"] + hazard(i - last[a] - 1)
        if text.startswith("str"):
            for a in addrs:
                last[a] = i
    return count, cycles


def bench_lines(body, functions, name):
    """The executed lines of one copy of a bench block's body, with synthetic addresses."""
    out = []
    for text in body:
        if text.endswith(":"):
            continue
        if text.startswith("bl "):
            out.append((0, "bl f", [], True))
            for t in functions[text.split()[1]]:
                m = SPOFF.search(t)
                out.append((0, t, [SP + int(m.group(1))] if m else [], False))
            continue
        if text.startswith(("bne.w", "b.w")):
            taken = name.startswith("br_taken") or text.startswith("b.w")
            out.append((0, text, [], taken))
            if taken:
                break
            continue
        m = SPOFF.search(text)
        addrs = [SP + int(m.group(1))] if m else []
        if text.startswith(("ldrd", "strd")):
            off = int(re.search(r"#(\d+)", text).group(1))
            addrs = [SP + off, SP + off + 4]
        out.append((0, text, addrs, False))
    return out


def measured(bench):
    """The ITCM cycles per copy of each block of results.txt, by suite and tag."""
    out = {}
    suite = None
    for line in (bench / "results.txt").read_text().splitlines():
        if line.startswith("suite "):
            suite = line.split()[1].rstrip(":")
        f = line.split()
        if suite and len(f) >= 5 and re.match(r"^[A-Za-z0-9_]+_\d+$", f[0]):
            out[(suite, f[0])] = float(f[3])
    return out


def calibration(bench):
    meas = measured(bench)
    print("block                           measured   model   error")
    for suite in ("main", "hazard"):
        lay = json.loads((bench / suite / "layout.json").read_text())
        for m in lay["measurements"]:
            key = (suite, m["tag"])
            if m["name"] == "empty" or key not in meas or m["tag"].endswith("_128"):
                continue
            one = bench_lines(m["body"], lay["functions"], m["name"])
            pred = cost(one * 3) - cost(one * 2)
            got = meas[key]
            err = 100 * (pred - got) / got
            print(f"{suite + '/' + m['tag']:30} {got:9.2f} {pred:7.2f} {err:6.1f}%")


def windows(rundir, names):
    print()
    print(f"{'trace':42} {'instr':>6} {'cycles':>8} {'LDRD/STRD':>10} {'pairs':>6} "
          f"{'rereads':>8} {'their cycles':>12}")
    for name in names:
        paths = sorted(rundir.glob(f"{name}.*.trace")) + sorted(rundir.glob(f"{name}.*.longest"))
        for path in paths:
            lines = read_trace(path)
            n = sum(1 for l in lines if kind(l[1]) != "div")
            d, merged = merge_pairs(lines)
            rr, rc = rereads(lines)
            print(f"{path.name:42} {n:6} {cost(lines):8.0f} {cost(d):10.0f} {merged:6} "
                  f"{rr:8} {rc:12.0f}")


def main():
    if len(sys.argv) < 4:
        raise SystemExit("usage: uv run tests/baremetal/m7_timing.py BENCH RUNDIR NAME...")
    bench = Path(sys.argv[1])
    calibration(bench)
    windows(Path(sys.argv[2]), sys.argv[3:])


main()
