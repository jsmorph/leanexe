# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Writes the test command of tests/linux/a64-wasi-files.sh: a WASI module that exercises
`path_open`, `fd_close`, and `fd_read` and `fd_write` on a handle, the cases' descriptions, and
the `open_how` flags that the shim gives each open of the flag scenario.

Usage: files-cases.py MODULE.wat CASES.txt FLAGS.txt

The module imports the three stream functions, then `path_open`, `fd_close`, `fd_read`, and
`fd_write`, the last two in their handle forms, `fd_prestat_get`, `clock_time_get`, and
`fd_prestat_dir_name`.  It reads one byte from
standard input, the scenario, and runs the scenario's cases one after another.  It writes to
standard output through `fd_write` with the iovec at address 0 and the count at address 8, as the
stream stub requires: the byte 0xFE at the start of each case, the byte 0xFF at the start of each
call's record, and then the call's errno as one byte.  A read's or a write's record adds the 4
bytes at the count's pointer, which hold 0xDD bytes before the call, and a read's record adds,
after errno 0, the buffer's 8 bytes, which hold 0xCC bytes before the call.  A record of
`fd_prestat_get` adds, after errno 0, the record's 8 bytes, which hold zeros before the call.  An
open that succeeds is followed by the probe of the descriptor: a read of 4 bytes, a write of the 2
bytes `xy`, and a close.  The module never writes a descriptor's number, since the Wasmtime host
and the executable number descriptors differently.

Scenarios, by the byte read:
  'p'  the 39 path cases of step 4's probes under descriptor 3, byte strings that are not UTF-8,
       UTF-8 names that `creat` creates, and the order of `openCheck`'s checks;
  'f'  every combination of `oflags`, the rights `fd_read` and `fd_write`, and `symlink_follow` on
       a file, a directory, a missing name, and symbolic links to the file and the directory, and
       every `fdflags` value on the file;
  'c'  closes of descriptors that the shim holds and does not hold, double closes, the close of
       the preopened directory, an open after it, and `fd_prestat_get` of descriptor 3 before and
       after the closes;
  'h'  reads and writes on handles: at the end of a file, of zero bytes, at the end of memory, with
       the iovec in the memory's last 8 bytes, on descriptors opened for reading or writing only,
       and on descriptors that the shim does not hold;
  'm'  opens under descriptor 3 of magic links and of a file, for a preopened /proc/self;
  't'  after `clock_time_get` of clocks 0 and 1, which writes the scratch's timespec at the place
       of the byte of descriptor 1,024, `fd_prestat_dir_name`, `fd_close`, `fd_read`, `fd_write`,
       and `path_open` on descriptor 1,024, which the shim does not hold;
  'l'  opens of `f` without closes until an open fails, at most 1,100, and then the close of
       descriptor 1,023;
  '1' to '9'  a request that the shim refuses with a trap: an iovec count of 2, an iovec, a
       buffer, or a count's pointer beyond memory, a path or a result's pointer beyond memory, an
       iovec 7 bytes before the memory's end, a count's pointer 3 bytes before it, and an iovec
       count of 2 on a descriptor that the shim does not hold.

CASES.txt holds one line for each case, its scenario, its index, and its description, separated
by tabs.  FLAGS.txt holds, for each open of scenario 'f' that reaches `openat2`, in order, the path
and the `flags` word of `open_how` that `openFlagsWord arm64Flags` gives, in hexadecimal.
"""

import sys

O_DIRECTORY = 0x4000
O_NOFOLLOW = 0x8000
MEMORY = 2 * 65536


def open_flags_word(dirflags: int, oflags: int, rights: int, fdflags: int) -> int:
    """`openFlagsWord arm64Flags` of Verified/Shim/Replies.lean."""
    creat = oflags & 1 != 0
    excl = creat and oflags & 4 != 0
    write = rights & 64 != 0 or creat or oflags & 8 != 0
    read = rights & 2 != 0 or rights & 64 == 0
    word = 2 if read and write else 1 if write else 0
    word |= 0x40 if creat else 0
    word |= O_DIRECTORY if oflags & 2 else 0
    word |= 0x80 if excl else 0
    word |= 0x200 if oflags & 8 and not excl else 0
    word |= 0x400 if fdflags & 1 else 0
    word |= 0x800 if fdflags & 4 else 0
    word |= O_NOFOLLOW if dirflags & 1 == 0 else 0
    return word | 0x80000


# Step 4's 27 path cases and its review's 12: (dir, path, symlink_follow, oflags, rights, fdflags).
PATHS = [
    (3, b"f", 1, 0, 2, 0), (3, b"sub/g", 1, 0, 2, 0), (3, b"sub/../f", 1, 0, 2, 0),
    (3, b"../x", 1, 0, 2, 0), (3, b"/etc/hostname", 1, 0, 2, 0), (3, b"in", 1, 0, 2, 0),
    (3, b"in", 0, 0, 2, 0), (3, b"out", 1, 0, 2, 0), (3, b"out", 0, 0, 2, 0),
    (3, b"up/f", 1, 0, 2, 0), (3, b"subup/f", 1, 0, 2, 0), (3, b"", 1, 0, 2, 0),
    (3, b"f/", 1, 0, 2, 0), (3, b"missing", 1, 0, 2, 0), (3, b"sub", 1, 0, 2, 0),
    (3, b"f\x00x", 1, 0, 2, 0), (3, b".", 1, 0, 2, 0), (3, b"..", 1, 0, 2, 0),
    (3, b"sub/../../x", 1, 0, 2, 0), (3, b"f", 1, 2, 2, 0), (3, b"new", 1, 3, 2, 0),
    (3, b"f", 1, 5, 2, 0), (3, b"\xff", 1, 0, 2, 0), (3, b"a" * 300, 1, 0, 2, 0),
    (3, b"sub/" * 1100, 1, 0, 2, 0), (3, b"dangling", 1, 0, 2, 0), (3, b"dangling", 1, 1, 2, 0),
    (3, b"in", 0, 2, 2, 0), (3, b"f\x00x", 1, 0, 2, 16), (3, b"\xff" * 5000, 1, 0, 2, 0),
    (3, b"f\x00\xff", 1, 0, 2, 0), (3, b"a" * 5000, 1, 0, 2, 16), (0, b"f", 1, 0, 2, 0),
    (4294967196, b"f", 1, 0, 2, 0), (3, b"f\x00x", 1, 3, 2, 0), (3, b"sub", 0, 0, 64, 0),
    (3, b"f", 1, 0, 2, 8), (3, b"sub", 1, 2, 2, 0), (3, b"up", 0, 2, 2, 0),
]

NOT_UTF8 = [
    b"\xff", b"\xfe", b"\x80", b"\xbf", b"\xc0\x80", b"\xc1\xbf", b"\xc2", b"\xc2\x41",
    b"\xc2\xc0", b"\xe0\x80\x80", b"\xe0\x9f\xbf", b"\xe1\x80", b"\xe1\x41\x80", b"\xe1\x80\x41",
    b"\xed\xa0\x80", b"\xed\xbf\xbf", b"\xf0\x80\x80\x80", b"\xf0\x8f\xbf\xbf", b"\xf1\x80\x80",
    b"\xf1\x80\x80\x41", b"\xf4\x90\x80\x80", b"\xf5\x80\x80\x80", b"\xf7\xbf\xbf\xbf",
    b"\xf8\x88\x80\x80\x80", b"ab\xff", b"a\xe2\x82", b"f\x00\xc0",
]
UTF8 = [
    b"\xc2\x80", b"\xdf\xbf", b"\xe0\xa0\x80", b"\xed\x9f\xbf", b"\xee\x80\x80", b"\xef\xbf\xbf",
    b"\xf0\x90\x80\x80", b"\xf4\x8f\xbf\xbf", b"caf\xc3\xa9", b"\xe4\xb8\xad\xe6\x96\x87",
    b"\xf0\x9f\x98\x80", b"\xe1\x80\x80\xf1\x80\x80\x80x",
]

# The order of `openCheck`'s checks: (dir, path, oflags, fdflags).
ORDER = [
    (99, b"f", 0, 0), (99, b"\xff", 0, 0), (99, b"f\x00", 0, 0), (99, b"a" * 5000, 0, 0),
    (1024, b"f", 0, 0), (2 ** 31, b"f", 0, 0), (2 ** 32 - 1, b"f", 0, 0),
    (3, b"f\x00", 0, 2), (3, b"f\x00", 3, 0), (3, b"f\x00", 0, 0), (3, b"a" * 4096, 0, 0),
    (3, b"a" * 4095, 0, 0), (3, b"a" * 4096 + b"\x00", 0, 0), (3, b"\xff" * 4096, 0, 16),
    (3, b"f", 2, 2), (3, b"f", 2 | 8, 0), (3, b"f", 2 | 4, 0), (3, b"f", 2 | 1, 0),
    (3, b"f", 3, 2),
]

MAGIC = [b"fd/0", b"fd/1", b"exe", b"cwd", b"cwd/f", b"root/etc/hostname", b"fd", b"status"]


def show(p: bytes) -> str:
    if len(p) > 24:
        return repr(p[:12]) + f"...({len(p)} bytes)"
    return repr(p)


class Module:
    def __init__(self) -> None:
        self.data: list[str] = []
        self.offset = 4096
        self.paths: dict[bytes, int] = {}
        self.scenarios: dict[str, list[tuple[str, str]]] = {}

    def path(self, p: bytes) -> int:
        if p not in self.paths:
            self.paths[p] = self.offset
            text = "".join(f"\\{b:02x}" for b in p)
            self.data.append(f'  (data (i32.const {self.offset}) "{text}")')
            self.offset += len(p) + 8
        return self.paths[p]

    def case(self, scenario: str, description: str, code: str) -> None:
        self.scenarios.setdefault(scenario, []).append((description, code))

    def open(self, scenario: str, dir: int, p: bytes, dirflags: int, oflags: int, rights: int,
             fdflags: int) -> None:
        self.case(scenario,
                  f"open dir={dir} path={show(p)} follow={dirflags} oflags={oflags} "
                  f"rights={rights} fdflags={fdflags}",
                  f"(call $case (i32.const {dir}) (i32.const {dirflags}) "
                  f"(i32.const {self.path(p)}) (i32.const {len(p)}) (i32.const {oflags}) "
                  f"(i64.const {rights}) (i32.const {fdflags}))")


def build() -> tuple[str, list[str], list[str]]:
    m = Module()
    flags_lines: list[str] = []
    for c in PATHS:
        m.open("p", *c)
    for p in NOT_UTF8:
        m.open("p", 3, p, 1, 0, 2, 0)
    for p in UTF8:
        m.open("p", 3, p, 1, 1, 66, 0)
    for d, p, o, f in ORDER:
        m.open("p", d, p, 1, o, 2, f)
    for target in [b"f", b"sub", b"absent", b"in", b"sublink"]:
        for oflags in range(16):
            for rights in [0, 2, 64, 66]:
                for dirflags in [0, 1]:
                    name = target
                    if target == b"absent":
                        name = b"absent-%d-%d-%d" % (oflags, rights, dirflags)
                    m.open("f", 3, name, dirflags, oflags, rights, 0)
                    if not (oflags & 2 and oflags & 0xD):
                        word = open_flags_word(dirflags, oflags, rights, 0)
                        flags_lines.append(f"{name.decode()} {word:#x}")
    for fdflags in range(32):
        m.open("f", 3, b"f", 1, 0, 66, fdflags)
        if fdflags & 0x1A == 0:
            flags_lines.append(f"f {open_flags_word(1, 0, 66, fdflags):#x}")
    for p in MAGIC:
        m.open("m", 3, p, 1, 0, 2, 0)
    f_at = m.path(b"f")
    xy = m.path(b"xy")

    def openf(rights: int, into: str) -> str:
        return f"(local.set {into} (call $openf (i64.const {rights})))"

    for description, code in [
        ("prestat 3", "(call $prestat (i32.const 3))"),
        ("close 4, which the shim does not hold", "(call $close (i32.const 4))"),
        ("close 1023", "(call $close (i32.const 1023))"),
        ("close 1024", "(call $close (i32.const 1024))"),
        ("close 2^31 - 1", "(call $close (i32.const 0x7fffffff))"),
        ("close 2^31", "(call $close (i32.const 0x80000000))"),
        ("close 2^32 - 1", "(call $close (i32.const 0xffffffff))"),
        ("open f as a", openf(2, "$a")),
        ("open f as b", openf(2, "$b")),
        ("close a", "(call $close (local.get $a))"),
        ("close a again", "(call $close (local.get $a))"),
        ("read a after its close", "(call $read (local.get $a) (i32.const 4))"),
        ("read b", "(call $read (local.get $b) (i32.const 4))"),
        ("open f as a again", openf(2, "$a")),
        ("read a", "(call $read (local.get $a) (i32.const 4))"),
        ("close a", "(call $close (local.get $a))"),
        ("close b", "(call $close (local.get $b))"),
        ("close b again", "(call $close (local.get $b))"),
        ("prestat 3 after the closes of a and b", "(call $prestat (i32.const 3))"),
        ("close 3, the preopened directory", "(call $close (i32.const 3))"),
        ("prestat 3 after its close", "(call $prestat (i32.const 3))"),
        ("close 3 again", "(call $close (i32.const 3))"),
        ("open f after the close of 3", openf(2, "$a")),
        ("read 3 after its close", "(call $read (i32.const 3) (i32.const 4))"),
    ]:
        m.case("c", description, code)

    for description, code in [
        ("open f to read and write as rw", openf(66, "$rw")),
        ("read 4 from rw", "(call $read (local.get $rw) (i32.const 4))"),
        ("read 0 from rw", "(call $read (local.get $rw) (i32.const 0))"),
        ("read 8 from rw", "(call $read (local.get $rw) (i32.const 8))"),
        ("read 8 from rw at its end", "(call $read (local.get $rw) (i32.const 8))"),
        ("write 2 to rw", f"(call $write (local.get $rw) (i32.const {xy}) (i32.const 2))"),
        ("write 0 to rw", f"(call $write (local.get $rw) (i32.const {xy}) (i32.const 0))"),
        ("open f to read as r", openf(2, "$r")),
        ("read 8 from r", "(call $read (local.get $r) (i32.const 8))"),
        ("write 2 to r", f"(call $write (local.get $r) (i32.const {xy}) (i32.const 2))"),
        ("open f to write as w", openf(64, "$w")),
        ("read 4 from w", "(call $read (local.get $w) (i32.const 4))"),
        ("write 1 to w", f"(call $write (local.get $w) (i32.const {xy}) (i32.const 1))"),
        ("read 4 from r into the end of memory", "(call $edge (local.get $r))"),
        ("write 1 to w with the count at the end of memory", "(call $edgeCount (local.get $w))"),
        ("read 4 from r with the iovec in the last 8 bytes of memory",
         "(call $edgeIovec (local.get $r))"),
        ("read 4 from 0", "(call $read (i32.const 0) (i32.const 4))"),
        ("write 2 to 2", f"(call $write (i32.const 2) (i32.const {xy}) (i32.const 2))"),
        ("read 4 from 3, the preopened directory", "(call $read (i32.const 3) (i32.const 4))"),
        ("read 4 from 1024", "(call $read (i32.const 1024) (i32.const 4))"),
        ("read 4 from 2^31", "(call $read (i32.const 0x80000000) (i32.const 4))"),
        ("write 2 to 1023", f"(call $write (i32.const 1023) (i32.const {xy}) (i32.const 2))"),
        ("close rw", "(call $close (local.get $rw))"),
        ("close r", "(call $close (local.get $r))"),
        ("close w", "(call $close (local.get $w))"),
    ]:
        m.case("h", description, code)

    for clock in [0, 1]:
        m.case("t", f"clock {clock}", f"(call $clock (i32.const {clock}))")
        m.case("t", f"prestat name of 1024 after clock {clock}", "(call $dirName (i32.const 1024))")
        m.case("t", f"close 1024 after clock {clock}", "(call $close (i32.const 1024))")
        m.case("t", f"read 4 from 1024 after clock {clock}",
               "(call $read (i32.const 1024) (i32.const 4))")
        m.case("t", f"write 2 to 1024 after clock {clock}",
               f"(call $write (i32.const 1024) (i32.const {xy}) (i32.const 2))")
        m.open("t", 1024, b"f", 1, 0, 2, 0)

    m.case("l", "opens of f without closes", "(call $limit)")
    m.case("l", "close 1023 after the opens", "(call $close (i32.const 1023))")
    for k, what in enumerate(["an iovec count of 2", "an iovec beyond memory",
                              "a buffer beyond memory", "a count's pointer beyond memory",
                              "a path beyond memory", "a result's pointer beyond memory",
                              "an iovec 7 bytes before the memory's end",
                              "a count's pointer 3 bytes before the memory's end",
                              "an iovec count of 2 on a descriptor that the shim does not hold"],
                             1):
        m.case(str(k), what, f"(call $trap (i32.const {k}))")

    functions = []
    dispatch = []
    cases_lines = []
    for scenario, cases in m.scenarios.items():
        name = f"$scenario_{ord(scenario)}"
        body = []
        for index, (description, code) in enumerate(cases):
            body.append(f"    (call $mark) {code}")
            cases_lines.append(f"{scenario}\t{index}\t{description}")
        functions += [f"  (func {name} (local $a i32) (local $b i32) (local $r i32) (local $w i32)",
                      "      (local $rw i32)", *body, "  )", ""]
        dispatch.append(f"    (if (i32.eq (local.get $s) (i32.const {ord(scenario)})) "
                        f"(then (call {name})))")

    body = "\n".join([
        "(module",
        '  (import "wasi_snapshot_preview1" "fd_read"',
        "    (func $fd_read (param i32 i32 i32 i32) (result i32)))",
        '  (import "wasi_snapshot_preview1" "fd_write"',
        "    (func $fd_write (param i32 i32 i32 i32) (result i32)))",
        '  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))',
        '  (import "wasi_snapshot_preview1" "path_open"',
        "    (func $path_open (param i32 i32 i32 i32 i32 i64 i64 i32 i32) (result i32)))",
        '  (import "wasi_snapshot_preview1" "fd_close" (func $fd_close (param i32) (result i32)))',
        '  (import "wasi_snapshot_preview1" "fd_read"',
        "    (func $h_read (param i32 i32 i32 i32) (result i32)))",
        '  (import "wasi_snapshot_preview1" "fd_write"',
        "    (func $h_write (param i32 i32 i32 i32) (result i32)))",
        '  (import "wasi_snapshot_preview1" "fd_prestat_get"',
        "    (func $fd_prestat_get (param i32 i32) (result i32)))",
        '  (import "wasi_snapshot_preview1" "clock_time_get"',
        "    (func $clock_time_get (param i32 i64 i32) (result i32)))",
        '  (import "wasi_snapshot_preview1" "fd_prestat_dir_name"',
        "    (func $fd_prestat_dir_name (param i32 i32 i32) (result i32)))",
        f'  (memory (export "memory") {MEMORY // 65536})',
        *m.data,
        "",
        "  ;; Writes the $n bytes at $p to standard output.",
        "  (func $emits (param $p i32) (param $n i32)",
        "    (i32.store (i32.const 0) (local.get $p))",
        "    (i32.store (i32.const 4) (local.get $n))",
        "    (i32.store (i32.const 52)",
        "      (call $fd_write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 8))))",
        "",
        "  ;; Writes the byte $b to standard output.",
        "  (func $emit (param $b i32)",
        "    (i32.store8 (i32.const 48) (local.get $b))",
        "    (call $emits (i32.const 48) (i32.const 1)))",
        "",
        "  (func $mark (call $emit (i32.const 0xfe)))",
        "",
        "  ;; path_open with the result at 16: the record, and the errno.",
        "  (func $open (param $dir i32) (param $dirflags i32) (param $p i32) (param $n i32)",
        "      (param $oflags i32) (param $rights i64) (param $fdflags i32) (result i32)",
        "    (local $e i32)",
        "    (call $emit (i32.const 0xff))",
        "    (i32.store (i32.const 16) (i32.const 0xaaaaaaaa))",
        "    (local.set $e (call $path_open (local.get $dir) (local.get $dirflags) (local.get $p)",
        "      (local.get $n) (local.get $oflags) (local.get $rights) (i64.const 0)",
        "      (local.get $fdflags) (i32.const 16)))",
        "    (call $emit (local.get $e))",
        "    (local.get $e))",
        "",
        "  ;; A read of $n bytes into 64 from $fd.",
        "  (func $read (param $fd i32) (param $n i32)",
        "    (local $e i32)",
        "    (call $emit (i32.const 0xff))",
        "    (i64.store (i32.const 64) (i64.const 0xcccccccccccccccc))",
        "    (i32.store (i32.const 32) (i32.const 64))",
        "    (i32.store (i32.const 36) (local.get $n))",
        "    (i32.store (i32.const 40) (i32.const 0xdddddddd))",
        "    (local.set $e (call $h_read (local.get $fd) (i32.const 32) (i32.const 1)",
        "      (i32.const 40)))",
        "    (call $emit (local.get $e))",
        "    (call $emits (i32.const 40) (i32.const 4))",
        "    (if (i32.eq (local.get $e) (i32.const 0))",
        "      (then (call $emits (i32.const 64) (i32.const 8)))))",
        "",
        "  ;; A write of the $n bytes at $p to $fd.",
        "  (func $write (param $fd i32) (param $p i32) (param $n i32)",
        "    (local $e i32)",
        "    (call $emit (i32.const 0xff))",
        "    (i32.store (i32.const 32) (local.get $p))",
        "    (i32.store (i32.const 36) (local.get $n))",
        "    (i32.store (i32.const 40) (i32.const 0xdddddddd))",
        "    (local.set $e (call $h_write (local.get $fd) (i32.const 32) (i32.const 1)",
        "      (i32.const 40)))",
        "    (call $emit (local.get $e))",
        "    (call $emits (i32.const 40) (i32.const 4)))",
        "",
        "  ;; fd_prestat_get of $fd with the record at 24.",
        "  (func $prestat (param $fd i32)",
        "    (local $e i32)",
        "    (call $emit (i32.const 0xff))",
        "    (i64.store (i32.const 24) (i64.const 0))",
        "    (local.set $e (call $fd_prestat_get (local.get $fd) (i32.const 24)))",
        "    (call $emit (local.get $e))",
        "    (if (i32.eq (local.get $e) (i32.const 0))",
        "      (then (call $emits (i32.const 24) (i32.const 8)))))",
        "",
        "  ;; clock_time_get of the clock $id with the time at 200, whose value differs between",
        "  ;; runs: the errno.",
        "  (func $clock (param $id i32)",
        "    (call $emit (i32.const 0xff))",
        "    (call $emit (call $clock_time_get (local.get $id) (i64.const 0) (i32.const 200))))",
        "",
        "  ;; fd_prestat_dir_name of $fd with a buffer of 1 byte at 208, 0 before the call: the errno",
        "  ;; and the buffer.",
        "  (func $dirName (param $fd i32)",
        "    (call $emit (i32.const 0xff))",
        "    (i32.store8 (i32.const 208) (i32.const 0))",
        "    (call $emit (call $fd_prestat_dir_name (local.get $fd) (i32.const 208) (i32.const 1)))",
        "    (call $emits (i32.const 208) (i32.const 1)))",
        "",
        "  ;; The close of $fd.",
        "  (func $close (param $fd i32)",
        "    (call $emit (i32.const 0xff))",
        "    (call $emit (call $fd_close (local.get $fd))))",
        "",
        "  ;; An open and, when it succeeds, the probe of the descriptor.",
        "  (func $case (param $dir i32) (param $dirflags i32) (param $p i32) (param $n i32)",
        "      (param $oflags i32) (param $rights i64) (param $fdflags i32)",
        "    (local $fd i32)",
        "    (if (i32.eq (call $open (local.get $dir) (local.get $dirflags) (local.get $p)",
        "        (local.get $n) (local.get $oflags) (local.get $rights) (local.get $fdflags))",
        "        (i32.const 0))",
        "      (then",
        "        (local.set $fd (i32.load (i32.const 16)))",
        "        (call $read (local.get $fd) (i32.const 4))",
        f"        (call $write (local.get $fd) (i32.const {xy}) (i32.const 2))",
        "        (call $close (local.get $fd)))))",
        "",
        "  ;; An open of f with the rights $rights: the descriptor, or -1.",
        "  (func $openf (param $rights i64) (result i32) (local $fd i32)",
        "    (local.set $fd (i32.const -1))",
        f"    (if (i32.eq (call $open (i32.const 3) (i32.const 1) (i32.const {f_at})",
        "        (i32.const 1) (i32.const 0) (local.get $rights) (i32.const 0)) (i32.const 0))",
        "      (then (local.set $fd (i32.load (i32.const 16)))))",
        "    (local.get $fd))",
        "",
        "  ;; A read of 4 bytes from $fd into the last 4 bytes of memory.",
        "  (func $edge (param $fd i32)",
        "    (call $emit (i32.const 0xff))",
        f"    (i32.store (i32.const 32) (i32.const {MEMORY - 4}))",
        "    (i32.store (i32.const 36) (i32.const 4))",
        "    (call $emit (call $h_read (local.get $fd) (i32.const 32) (i32.const 1)",
        "      (i32.const 40)))",
        "    (call $emits (i32.const 40) (i32.const 4))",
        f"    (call $emits (i32.const {MEMORY - 4}) (i32.const 4)))",
        "",
        "  ;; A write of 1 byte to $fd with the count in the last 4 bytes of memory.",
        "  (func $edgeCount (param $fd i32)",
        "    (call $emit (i32.const 0xff))",
        "    (i32.store (i32.const 32) (i32.const 64))",
        "    (i32.store (i32.const 36) (i32.const 1))",
        "    (call $emit (call $h_write (local.get $fd) (i32.const 32) (i32.const 1)",
        f"      (i32.const {MEMORY - 4})))",
        f"    (call $emits (i32.const {MEMORY - 4}) (i32.const 4)))",
        "",
        "  ;; A read of 4 bytes from $fd with the iovec in the last 8 bytes of memory.",
        "  (func $edgeIovec (param $fd i32)",
        "    (call $emit (i32.const 0xff))",
        f"    (i32.store (i32.const {MEMORY - 8}) (i32.const 64))",
        f"    (i32.store (i32.const {MEMORY - 4}) (i32.const 4))",
        "    (i64.store (i32.const 64) (i64.const 0xcccccccccccccccc))",
        "    (i32.store (i32.const 40) (i32.const 0xdddddddd))",
        f"    (call $emit (call $h_read (local.get $fd) (i32.const {MEMORY - 8}) (i32.const 1)",
        "      (i32.const 40)))",
        "    (call $emits (i32.const 40) (i32.const 4))",
        "    (call $emits (i32.const 64) (i32.const 8)))",
        "",
        "  ;; Opens of f without closes until one fails, at most 1,100.",
        "  (func $limit (local $k i64)",
        "    (block $out (loop $more",
        "      (br_if $out (i32.eq (call $openf (i64.const 2)) (i32.const -1)))",
        "      (local.set $k (i64.add (local.get $k) (i64.const 1)))",
        "      (br_if $more (i64.lt_u (local.get $k) (i64.const 1100))))))",
        "",
        "  ;; A request that the shim refuses with a trap, after an open of f.",
        "  (func $trap (param $which i32) (local $fd i32)",
        "    (local.set $fd (call $openf (i64.const 66)))",
        "    (i32.store (i32.const 32) (i32.const 64))",
        "    (i32.store (i32.const 36) (i32.const 4))",
        "    (i32.store (i32.const 72) (i32.const 64))",
        "    (i32.store (i32.const 76) (i32.const 4))",
        "    (call $emit (i32.const 0xff))",
        "    (if (i32.eq (local.get $which) (i32.const 1)) (then",
        "      (call $emit (call $h_read (local.get $fd) (i32.const 32) (i32.const 2)",
        "        (i32.const 40)))))",
        "    (if (i32.eq (local.get $which) (i32.const 2)) (then",
        f"      (call $emit (call $h_read (local.get $fd) (i32.const {MEMORY - 4}) (i32.const 1)",
        "        (i32.const 40)))))",
        "    (if (i32.eq (local.get $which) (i32.const 3)) (then",
        f"      (i32.store (i32.const 32) (i32.const {MEMORY - 2}))",
        "      (call $emit (call $h_write (local.get $fd) (i32.const 32) (i32.const 1)",
        "        (i32.const 40)))))",
        "    (if (i32.eq (local.get $which) (i32.const 4)) (then",
        "      (call $emit (call $h_read (local.get $fd) (i32.const 32) (i32.const 1)",
        f"        (i32.const {MEMORY - 2})))))",
        "    (if (i32.eq (local.get $which) (i32.const 5)) (then",
        f"      (call $emit (call $path_open (i32.const 3) (i32.const 1) (i32.const {MEMORY - 2})",
        "        (i32.const 4) (i32.const 0) (i64.const 2) (i64.const 0) (i32.const 0)",
        "        (i32.const 16)))))",
        "    (if (i32.eq (local.get $which) (i32.const 6)) (then",
        f"      (call $emit (call $path_open (i32.const 3) (i32.const 1) (i32.const {f_at})",
        "        (i32.const 1) (i32.const 0) (i64.const 2) (i64.const 0) (i32.const 0)",
        f"        (i32.const {MEMORY - 3})))))",
        "    (if (i32.eq (local.get $which) (i32.const 7)) (then",
        f"      (call $emit (call $h_read (local.get $fd) (i32.const {MEMORY - 7}) (i32.const 1)",
        "        (i32.const 40)))))",
        "    (if (i32.eq (local.get $which) (i32.const 8)) (then",
        "      (call $emit (call $h_read (local.get $fd) (i32.const 32) (i32.const 1)",
        f"        (i32.const {MEMORY - 3})))))",
        "    (if (i32.eq (local.get $which) (i32.const 9)) (then",
        "      (call $emit (call $h_read (i32.const 99) (i32.const 32) (i32.const 2)",
        "        (i32.const 40))))))",
        "",
        *functions,
        '  (func (export "_start") (local $s i32)',
        "    (i32.store (i32.const 0) (i32.const 48))",
        "    (i32.store (i32.const 4) (i32.const 1))",
        "    (i32.store8 (i32.const 48) (i32.const 0))",
        "    (i32.store (i32.const 52)",
        "      (call $fd_read (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 8)))",
        "    (local.set $s (i32.load8_u (i32.const 48)))",
        *dispatch,
        "  )",
        ")",
        "",
    ])
    return body, cases_lines, flags_lines


def main() -> None:
    if len(sys.argv) != 4:
        sys.exit("usage: files-cases.py MODULE.wat CASES.txt FLAGS.txt")
    body, cases_lines, flags_lines = build()
    for path, text in [(sys.argv[1], body), (sys.argv[2], "\n".join(cases_lines) + "\n"),
                       (sys.argv[3], "\n".join(flags_lines) + "\n")]:
        with open(path, "w") as f:
            f.write(text)


if __name__ == "__main__":
    main()
