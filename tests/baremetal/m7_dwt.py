# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The results of the cycle measurements of tests/TestSupport/M7/Dwt.lean, read from the board's
DTCM over SWD.

"m7_dwt.py div RESULTS" reads the records of divDwt.  For each call of udivmod64 it checks the
quotient and the remainder against Python's integer division, classifies the routine's path as
the routine's code takes it (high: the divisor's low word is 0; low: both high words are 0;
small: the dividend lies below the divisor; loop: s + 1 passes, where s is the divisor's leading
zero count less the dividend's), counts the routine's instructions from its entry to its BX LR
on that path, and prints the cycles of the call less those of the empty call, the median, least,
and most over the passes.  For the blocks of 16 UDIV it prints the cycles of the block less those
of the block of 16 MOV, divided by 16.

"m7_dwt.py echo RESULTS" reads the window table of echoDwt and prints, for each kind of window,
the count, the least, the most, and the mean of the cycles, with the instructions that the model
counts for that kind (tests/TestSupport/M7/Windows.lean) plus the
five instructions of the measurement.  "m7_dwt.py crc RESULTS" does the same for the window table
of crcDwt, the CRC-32 step's, whose windows have the echo's phases.

"m7_dwt.py gateway RESULTS" reads the window table of gwDwt and prints the same for each kind of
the gateway's windows, with the range of the tick's instructions over the day of
Demos/Energy/board-day/gateway1440.records.in, and marks the kinds whose most cycles exceed
16,667, half a byte's time at 4,800 baud at 16 MHz.  The table's keys are the phase plus 4 when
the byte count is 7, before and after the window.

"m7_dwt.py bootlog LOG" prints the boot log: each reset's RCC_CSR flags.

Each command exits with status 1 when the results are malformed or a quotient is wrong.
"""
import statistics
import struct
import sys

MASK64 = (1 << 64) - 1

# The model's instruction counts of the echo's windows, from the loop's head to the loop's head
# (tests/TestSupport/M7/Windows.lean), with the 8 instructions of udivmod64's high path in tx.
ECHO_KINDS = {
    (0, 0): ("idle", 319),
    (0, 1): ("rxne", 318),
    (1, 2): ("byte", 361),
    (2, 2): ("txwait", 414),
    (2, 3): ("tx", 515 + 8),
    (3, 0): ("sent", 355),
}
MEAS = 5

# The model's instruction counts of the CRC-32 step's windows, from the loop's head to the loop's
# head, with the 8 instructions of udivmod64's high path in tx.
CRC_KINDS = {
    (0, 0): ("idle", 337),
    (0, 1): ("rxne", 348),
    (1, 2): ("byte", 612),
    (2, 2): ("txwait", 432),
    (2, 3): ("tx", 557 + 8),
    (3, 0): ("sent", 373),
}

# The model's instruction counts of the gateway's windows, from the loop's head to the loop's head
# (tests/TestSupport/M7/Windows.lean), over the day of gateway1440.records.in, by the phase and
# whether the byte count is 7 before the window and the phase after it, with the 8 instructions of
# udivmod64's high path in tx.
GW_KINDS = {
    (0, 0, 0): ("idle", 2501), (0, 1, 0): ("idle", 2501),
    (0, 0, 1): ("rxne", 2500), (0, 1, 1): ("rxne", 2500),
    (1, 0, 0): ("byte", 2936),
    (1, 1, 0): ("word", 3643),
    (1, 1, 2): ("tick", (11614, 29962)),
    (2, 0, 2): ("txwait", 3300), (2, 1, 2): ("txwait", 3300),
    (2, 0, 3): ("tx", 3401 + 8), (2, 1, 3): ("tx", 3401 + 8),
    (3, 0, 2): ("sent", 3367),
    (3, 1, 2): ("sentword", 3700),
    (3, 1, 0): ("sentrecord", 3689),
}
HALF_BYTE = 16667

FLAGS = [(31, "LPWR"), (30, "WWDG"), (29, "IWDG"), (28, "SFT"), (27, "POR"), (26, "PIN"),
         (25, "BOR")]


def words(path):
    data = open(path, "rb").read()
    return list(struct.unpack(f"<{len(data) // 4}I", data[: len(data) // 4 * 4]))


def clz64(x):
    return 64 - x.bit_length()


def path_of(n, d):
    """The path and the instruction count of udivmod64 from its entry through its BX LR."""
    nl, nh, dl, dh = n & 0xFFFFFFFF, n >> 32, d & 0xFFFFFFFF, d >> 32
    if dl == 0:
        return "high", 8
    if nh | dh == 0:
        return "low", 8
    if n < d:
        return "small", 12
    s = clz64(d) - clz64(n)
    r, dd, borrows = n, d << s, 0
    for _ in range(s + 1):
        if r >= dd:
            r -= dd
        else:
            borrows += 1
        dd >>= 1
    return f"loop {s + 1}", 29 + 12 * (s + 1) + 2 * borrows


def div(path):
    w = words(path)
    if w[0] != 0x600DCAFE:
        print(f"m7_dwt: {path}: no magic word, 0x{w[0]:08x}")
        return 1
    count = w[1]
    recs = []
    for k in range(count):
        r = w[4 + 10 * k: 14 + 10 * k]
        if len(r) < 10:
            print(f"m7_dwt: {path}: record {k} is incomplete")
            return 1
        kind, cid = r[0] >> 16, r[0] & 0xFFFF
        recs.append((kind, cid, r[1], r[2] | r[3] << 32, r[4] | r[5] << 32,
                     r[6] | r[7] << 32, r[8] | r[9] << 32))
    by = {}
    for kind, cid, cyc, q, rem, n, d in recs:
        by.setdefault(cid, []).append((kind, cyc, q, rem, n, d))
    status = 0
    empty = [cyc for kind, _, cyc, *_ in recs if kind == 1]
    mov = [cyc for kind, _, cyc, *_ in recs if kind == 3]
    e0 = statistics.median(empty)
    m0 = statistics.median(mov)
    print(f"empty call: {e0} cycles (from {min(empty)} to {max(empty)}); "
          f"16 MOV: {m0} cycles (from {min(mov)} to {max(mov)})")
    print("udivmod64: case, path, instructions, cycles less the empty call: median (least, most)")
    for cid in sorted(by):
        rows = by[cid]
        kind = rows[0][0]
        if kind != 0:
            continue
        n, d = rows[0][4], rows[0][5]
        for _, _, q, rem, n2, d2 in rows:
            if (n2, d2) != (n, d) or q != n // d or rem != n % d:
                print(f"m7_dwt: case {cid}: {n2:#x} / {d2:#x} gave {q:#x} rem {rem:#x}")
                status = 1
        p, ins = path_of(n, d)
        cyc = [c - e0 for _, c, *_ in rows]
        print(f"  {cid:2} {p:8} {ins:4}  {statistics.median(cyc):6} ({min(cyc)}, {max(cyc)})"
              f"  {n:#x} / {d:#x}")
    print("UDIV r4, r0, r2: case, cycles per UDIV less those per MOV: median (least, most)")
    for cid in sorted(by):
        rows = by[cid]
        if rows[0][0] != 2:
            continue
        n, d = rows[0][4] & 0xFFFFFFFF, rows[0][5] & 0xFFFFFFFF
        cyc = [(c - m0) / 16 for _, c, *_ in rows]
        print(f"  {cid:2} {statistics.median(cyc):6.2f} ({min(cyc):.2f}, {max(cyc):.2f})"
              f"  {n:#010x} / {d:#010x}")
    return status


def phases(path, kinds):
    w = words(path)
    status = 0
    print("window, count, least, most, mean cycles, model instructions plus the measurement's")
    for key in range(16):
        count, least, most, lo, hi = w[4 + 8 * key: 9 + 8 * key]
        total = lo | hi << 32
        if count == 0:
            continue
        name, ins = kinds.get((key >> 2, key & 3), (f"key {key}", None))
        mean = total / count
        extra = "" if ins is None else f"  {ins + MEAS}"
        print(f"  {name:7} {count:9} {least:6} {most:6} {mean:9.1f}{extra}")
        if ins is None:
            status = 1
    return status


def gateway(path):
    w = words(path)
    status = 0
    kinds = {}
    for key in range(64):
        count, least, most, lo, hi = w[4 + 8 * key: 9 + 8 * key]
        if count == 0:
            continue
        before, after = key >> 3, key & 7
        kind = GW_KINDS.get((before & 3, before >> 2, after & 3))
        if kind is None:
            print(f"m7_dwt: {path}: {count} windows with the keys {before} and {after}")
            status = 1
            continue
        k = kinds.setdefault(kind[0], [0, None, 0, 0, kind[1]])
        k[0] += count
        k[1] = least if k[1] is None else min(k[1], least)
        k[2] = max(k[2], most)
        k[3] += lo | hi << 32
    print("window, count, least, most, mean cycles, model instructions plus the measurement's")
    for name, (count, least, most, total, ins) in kinds.items():
        model = f"{ins[0] + MEAS} to {ins[1] + MEAS}" if isinstance(ins, tuple) else ins + MEAS
        over = f"  above {HALF_BYTE}" if most > HALF_BYTE else ""
        print(f"  {name:10} {count:9} {least:6} {most:6} {total / count:9.1f}  {model}{over}")
    return status


def bootlog(path):
    w = words(path)
    if w[0] != 0xB007106E:
        print(f"m7_dwt: {path}: no magic word, 0x{w[0]:08x}")
        return 1
    count = w[1]
    print(f"boot log: {count} resets")
    for k in range(min(count, 64)):
        csr = w[2 + k]
        names = [name for bit, name in FLAGS if csr >> bit & 1]
        print(f"  {k}: RCC_CSR 0x{csr:08x} {' '.join(names)}")
    return 0


def main():
    commands = {"div": div, "echo": lambda path: phases(path, ECHO_KINDS),
                "crc": lambda path: phases(path, CRC_KINDS), "gateway": gateway,
                "bootlog": bootlog}
    if len(sys.argv) != 3 or sys.argv[1] not in commands:
        print("usage: m7_dwt.py div RESULTS | echo RESULTS | crc RESULTS | gateway RESULTS | "
              "bootlog LOG", file=sys.stderr)
        return 2
    return commands[sys.argv[1]](sys.argv[2])


if __name__ == "__main__":
    sys.exit(main())
