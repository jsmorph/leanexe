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
counts for that kind (tests/TestSupport/M7/Windows.lean, the counts of G0 in devnotes.md) plus the
five instructions of the measurement.

"m7_dwt.py bootlog LOG" prints the boot log: each reset's RCC_CSR flags.

Each command exits with status 1 when the results are malformed or a quotient is wrong.
"""
import statistics
import struct
import sys

MASK64 = (1 << 64) - 1

# The model's instruction counts of the echo's windows, from the loop's head to the loop's head
# (devnotes.md, "Cortex-M7 back end, G0"), with the 8 instructions of udivmod64's high path in tx.
ECHO_KINDS = {
    (0, 0): ("idle", 319),
    (0, 1): ("rxne", 318),
    (1, 2): ("byte", 361),
    (2, 2): ("txwait", 414),
    (2, 3): ("tx", 515 + 8),
    (3, 0): ("sent", 355),
}
MEAS = 5

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


def echo(path):
    w = words(path)
    status = 0
    print("window, count, least, most, mean cycles, model instructions plus the measurement's")
    for key in range(16):
        count, least, most, lo, hi = w[4 + 8 * key: 9 + 8 * key]
        total = lo | hi << 32
        if count == 0:
            continue
        name, ins = ECHO_KINDS.get((key >> 2, key & 3), (f"key {key}", None))
        mean = total / count
        extra = "" if ins is None else f"  {ins + MEAS}"
        print(f"  {name:7} {count:9} {least:6} {most:6} {mean:9.1f}{extra}")
        if ins is None:
            status = 1
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
    if len(sys.argv) != 3 or sys.argv[1] not in ("div", "echo", "bootlog"):
        print("usage: m7_dwt.py div RESULTS | echo RESULTS | bootlog LOG", file=sys.stderr)
        return 2
    return {"div": div, "echo": echo, "bootlog": bootlog}[sys.argv[1]](sys.argv[2])


if __name__ == "__main__":
    sys.exit(main())
