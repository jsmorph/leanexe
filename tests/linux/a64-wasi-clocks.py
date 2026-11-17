# /// script
# requires-python = ">=3.12"
# ///
"""Checks the standard output of a run of a case module of tests/linux/a64-wasi-clocks.sh, or of
runs of the clock and random example of Verified/Examples/WasiClockRandom.lean.

Usage: uv run tests/linux/a64-wasi-clocks.py KIND PAGES A B FILE NOW
       uv run tests/linux/a64-wasi-clocks.py example NOW FILE...
       uv run tests/linux/a64-wasi-clocks.py calls ELF TRACE CAP [clock ID | random PTR N]...

For calls, TRACE holds the output of `strace -X raw -e raw=clock_gettime,getrandom` for a run of
the executable ELF, whose memory's cap is CAP pages, and the run's calls of `clock_gettime` and
`getrandom` must be those that the expectations after CAP give, in their order.  `clock ID` is one
`clock_gettime` of clock ID into the timespec, 1,040 bytes into the scratch that follows the area.
`random PTR N` is a `getrandom` with flags 0 of the N bytes at guest address PTR, or at any address
for a PTR of `-`, within the memory, which starts 4,096 bytes into the area that the second program
header maps, and after each count from 1 to the bytes asked for, exclusive, a `getrandom` of the
rest.  The program prints the number of calls and each call's clock or count and result.

For the example, each FILE must hold 5,072 bytes: the errno and time of clock 0, the errno and
time of clock 1, the errno of clock 2, the errno and 16 bytes of the first `randomGet`, and the
errno and 5,000 bytes of the second, each errno and time as 8 little-endian bytes.  The errnos
must be 0, 0, 8, 0, and 0, each realtime reading must lie within a day of NOW and within 600
seconds of the first file's, each monotonic reading must lie below 10^17, the 5,000 random bytes
must hold at most 64 zero bytes, and the 16 random bytes of two files must differ.

For a case, KIND is clock, with A the clock and B the time's pointer, or random, with A the buffer's
pointer and B its length, in a memory of PAGES pages.  FILE holds the run's output: the errno as 8
little-endian bytes and then the regions that the module writes when they lie in memory.  For a
clock, the 8 bytes before the pointer when it is at least 32, the 8 bytes at it, and the 8 bytes
after, each prefilled with 0x11; for random, the guard byte before the pointer (0x5A) when it is at
least 32, the first min(B, 4096) bytes, the last min(B - 4096, 4096) bytes when B exceeds 4096, and
the guard byte after (0xA5).  The guards must keep their values, a slot that the call did not fill
must keep 0x11, a realtime reading must lie within a day of NOW, in seconds, a monotonic reading
must lie below 10^17, and each buffer of at least 4,096 random bytes must hold at most 64 zero
bytes.  The program prints the errno and exits with status 1 on a failure.
"""
import re
import sys


def regions(kind, size, a, b):
    """The regions that the module writes, as (start, end, role) in the order of the output."""
    out = []

    def region(lo, hi, role):
        if lo < hi <= size:
            out.append((lo, hi, role))

    if kind == "clock":
        ptr = b
        lo = ptr - 8 if ptr >= 32 else ptr
        hi = ptr + 16 if ptr + 16 <= size else ptr + 8
        region(lo, hi, "clock")
    else:
        ptr, n = a, b
        head = min(n, 4096)
        if ptr >= 32:
            region(ptr - 1, ptr + head, "head-guarded")
        else:
            region(ptr, ptr + head, "head")
        if n > 4096:
            tail = min(n - 4096, 4096)
            region(ptr + n - tail, ptr + n, "tail")
        region(ptr + n, ptr + n + 1, "after")
    return out


def example(now, paths):
    """Checks the runs of the example; returns the failures."""
    fails = []
    walls = []
    smalls = []
    for path in paths:
        data = open(path, "rb").read()
        if len(data) != 5072:
            fails.append(f"{path}: {len(data)} bytes")
            continue

        def word(offset):
            return int.from_bytes(data[offset:offset + 8], "little")

        errnos = [word(0), word(16), word(32), word(40), word(64)]
        if errnos != [0, 0, 8, 0, 0]:
            fails.append(f"{path}: errnos {errnos}")
        wall, mono = word(8), word(24)
        if abs(wall / 1e9 - now) > 86400:
            fails.append(f"{path}: realtime reading {wall}")
        if walls and abs(wall - walls[0]) / 1e9 > 600:
            fails.append(f"{path}: realtime reading {wall} far from {walls[0]}")
        walls.append(wall)
        if not 0 < mono < 10**17:
            fails.append(f"{path}: monotonic reading {mono}")
        smalls.append(data[48:64])
        if data[72:].count(0) > 64:
            fails.append(f"{path}: {data[72:].count(0)} zero bytes in 5000 random bytes")
    if len(smalls) >= 2 and len(set(smalls)) < 2:
        fails.append("the 16 random bytes are the same in every run")
    return fails


def area_of(elf):
    """The address of the data segment, the area: the second PT_LOAD header's address."""
    data = open(elf, "rb").read()
    phoff = int.from_bytes(data[32:40], "little")
    phnum = int.from_bytes(data[56:58], "little")
    loads = []
    for i in range(phnum):
        h = data[phoff + 56 * i: phoff + 56 * (i + 1)]
        if int.from_bytes(h[0:4], "little") == 1:
            loads.append(int.from_bytes(h[16:24], "little"))
    return loads[1]


def shown(name, args):
    """A call as strace writes it, with each argument in hexadecimal."""
    return f"{name}({', '.join(hex(a) for a in args)})"


CALL = re.compile(r"(clock_gettime|getrandom)\(([^)]*)\)\s+=\s+(-?(?:0x[0-9a-f]+|[0-9]+))")


def calls(elf, trace, cap, expect):
    """Checks the calls of a run that `strace -X raw -e raw=clock_gettime,getrandom` wrote to
    `trace` against `expect`, a list of ("clock", ID) and ("random", PTR, N) with PTR None for any
    address, for the executable `elf` with a memory's cap of `cap` pages; returns the failures and
    the calls, each its name, arguments, and result."""
    area = area_of(elf)
    base = area + 4096
    size = cap * 65536
    timespec = base + size + 1040
    seen = []
    for line in open(trace):
        if line.startswith(("clock_gettime(", "getrandom(")):
            m = CALL.match(line)
            if m is None:
                return [f"unread line {line.strip()}"], seen
            seen.append((m[1], [int(x, 0) for x in m[2].split(",")], int(m[3], 0)))
    pending = list(expect)
    rest = None
    for name, args, result in seen:
        if rest is None:
            if not pending:
                return [f"{shown(name, args)} after the expected calls"], seen
            item = pending.pop(0)
            if item[0] == "clock":
                if name != "clock_gettime" or args != [item[1], timespec]:
                    return [f"{shown(name, args)} where"
                            f" {shown('clock_gettime', [item[1], timespec])} is due"], seen
                continue
            rest = (None if item[1] is None else base + item[1], item[2])
        if name != "getrandom":
            return [f"{shown(name, args)} where getrandom is due"], seen
        buf, length, flags = args
        if (flags != 0 or buf < base or buf + length > base + size or length != rest[1]
                or rest[0] is not None and buf != rest[0]):
            due = "any address" if rest[0] is None else f"{rest[0]:#x}"
            return [f"{shown(name, args)} where the {rest[1]} bytes at {due} within the memory"
                    f" from {base:#x} are due"], seen
        rest = (buf + result, length - result) if 0 < result < length else None
    if rest is not None or pending:
        return ["the run ends before the expected calls"], seen
    return [], seen


def main():
    if sys.argv[1] == "calls":
        elf, trace, cap = sys.argv[2], sys.argv[3], int(sys.argv[4])
        words = sys.argv[5:]
        expect = []
        while words:
            if words[0] == "clock":
                expect.append(("clock", int(words[1])))
                words = words[2:]
            else:
                expect.append(("random", None if words[1] == "-" else int(words[1]),
                               int(words[2])))
                words = words[3:]
        fails, seen = calls(elf, trace, cap, expect)
        for f in fails:
            print("fail:", f)
        print(f"{len(seen)} call{'' if len(seen) == 1 else 's'}" + "".join(
            f", clock_gettime {args[0]} = {result}" if name == "clock_gettime"
            else f", getrandom {args[1]} = {result}" for name, args, result in seen))
        sys.exit(1 if fails else 0)
    if sys.argv[1] == "example":
        fails = example(int(sys.argv[2]), sys.argv[3:])
        for f in fails:
            print("fail:", f)
        sys.exit(1 if fails else 0)
    kind, pages, a, b, path, now = sys.argv[1:7]
    pages, a, b, now = int(pages), int(a), int(b), int(now)
    size = pages * 65536
    data = open(path, "rb").read()
    errno = int.from_bytes(data[:8], "little")
    rest = data[8:]
    fails = []
    expected = regions(kind, size, a, b)
    if len(rest) != sum(hi - lo for lo, hi, _ in expected):
        fails.append(f"{len(rest)} bytes after the errno")
    else:
        pos = 0
        for lo, hi, role in expected:
            part = rest[pos:pos + hi - lo]
            pos += hi - lo
            if role == "clock":
                ptr = b
                slot = part[ptr - lo:ptr - lo + 8]
                guards = part[:ptr - lo] + part[ptr - lo + 8:]
                if any(x != 0x11 for x in guards):
                    fails.append("a byte around the time changed")
                value = int.from_bytes(slot, "little")
                if errno != 0 and slot != bytes([0x11] * 8):
                    fails.append(f"the time's slot changed with errno {errno}")
                if errno == 0 and a == 0 and abs(value / 1e9 - now) > 86400:
                    fails.append(f"realtime reading {value}")
                if errno == 0 and a == 1 and not 0 < value < 10**17:
                    fails.append(f"monotonic reading {value}")
            elif role == "after":
                if part != b"\xa5":
                    fails.append("the guard byte after the buffer changed")
            else:
                if role == "head-guarded":
                    if part[0] != 0x5A:
                        fails.append("the guard byte before the buffer changed")
                    part = part[1:]
                if errno == 0 and len(part) >= 4096 and part.count(0) > 64:
                    fails.append(f"{part.count(0)} zero bytes in {len(part)} random bytes")
    print(f"errno {errno}")
    for f in fails:
        print("fail:", f)
    sys.exit(1 if fails else 0)


main()
