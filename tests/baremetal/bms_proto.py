# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The wire format of the BMS protection demo (Demos/Bms/requirements.md): the scan record that
the bridge sends, the answer that the board returns, the CRC over the link identifier and a
record's bytes, COBS framing (Cheshire and Baker 1999) with a 0x00 after each encoded record, and
the board's communication checks.

The module also holds a mirror of the protection machine of Demos/Bms/Spec.lean, which is the
reference: State, INIT, failure, step, and machine transcribe the Lean definitions of the same
names, and Board feeds received bytes through the delimited framing of
LeanExe/Requests/Delimited.lean to the machine and returns each encoded answer.  The framing calls
the machine once for each non-empty segment, with "overflow" for a segment of more than 36 bytes,
"decode" when COBS decoding fails, and the decoded bytes otherwise.

"vectors" prints the two test vectors of the requirements and the line times at 4,800 baud.
"faults" applies every single-byte fault to the wire bytes of the first vector, one at a time: the
loss of each byte, the insertion of each value before each byte or after the delimiter, and the
replacement of each byte by each other value.  It runs the board's segmenter on the faulty bytes,
preceded by the delimiter of the record before, and then on the bytes that the bridge sends next:
the next record (sequence number 8) when some segment so far is the vector's record answered with
its own sequence number, which makes the answer current (BR3), and otherwise the 0x00 of the
timeout rule (BR4) followed by the next record.  It applies the communication checks to each
non-empty segment, starting with the board synchronized and expecting the vector's sequence
number, and prints, for each kind of fault, the number of faults that give each list of outcomes,
the last of which belongs to the next record.  An outcome is a diagnostic code or "accepted".  The
model has no timing, so it keeps every byte that arrives while the board answers, which USART3
may lose.  The script first checks its COBS encoder and decoder on random records, and the
machine's answer to the scan vector in NORMAL with the vector's sequence number expected and the
next answer numbered 8, which must be the answer vector, and exits with status 1 if a check fails.

"gen SEED N PREFIX" writes N random writes of a bridge to PREFIX.in, in the format of
tests/baremetal/uart_bms.py, and the mirror's answers to them to PREFIX.out, so that the native
replay of tests/TestSupport/Bms/Replay.lean compares the mirror with Demos/Bms/Spec.lean.  A write
is a scan record encoded with its 0x00, with the next sequence number, each field within the
profile's limits or, with probability 0.02, within 1 of a limit, and a digital word from a process
that follows the state of the mirror's last answer: in RESET_REQUIRED and FAULT it presses and
releases the reset button and clears RUN, in STANDBY it sets RUN, and in every state it toggles
STOP_OK now and then.  The auxiliary contacts report the permit of the last answer with
probability 0.95, and a reserved bit is set with probability 0.003.  With probability 0.04 the
write is the record with a lost, inserted, or changed byte, a byte set to 0x00, or a lost
delimiter, or a record with the CRC over another link identifier, another tag, a repeated or
skipped sequence number, random bytes, an empty segment, or more than 36 nonzero bytes.  A line
"reset" marks a board reset with probability 0.002 after each write.  The command prints the
number of answers in each state.

Usage: uv run tests/baremetal/bms_proto.py vectors | faults | gen SEED N PREFIX
"""

import random
import sys
import zlib
from collections import Counter
from dataclasses import dataclass

LINK = b"LeanExe-BMS-0001"
SCAN_TAG = 0x10
ANSWER_TAG = 0x80
SCAN_RAW = 35
ANSWER_RAW = 17
MAX_SEGMENT = SCAN_RAW + 1
BAUD = 4800
BITS_PER_BYTE = 10

CODES = {
    0x1001: "COBS decode error",
    0x1002: "segment overflow",
    0x1003: "length other than 35",
    0x1004: "CRC mismatch",
    0x1005: "tag other than 0x10",
    0x1006: "sequence number other than expected",
}


class DecodeError(Exception):
    pass


def crc(data):
    """CRC-32 of the link identifier followed by data, as zlib computes it."""
    return zlib.crc32(data, zlib.crc32(LINK))


def be(value, size):
    return (value % (1 << (8 * size))).to_bytes(size, "big")


def scan_record(seq, cells, temps, current, pack, bus, digital):
    body = bytes([SCAN_TAG]) + be(seq, 4)
    body += b"".join(be(c, 2) for c in cells)
    body += b"".join(be(t, 2) for t in temps)
    body += be(current, 4) + be(pack, 4) + be(bus, 4) + be(digital, 2)
    assert len(body) == SCAN_RAW - 4
    return body + be(crc(body), 4)


def answer_record(board_seq, answered, permit, state, diag):
    body = bytes([ANSWER_TAG]) + be(board_seq, 4) + be(answered, 4) + bytes([permit, state])
    body += be(diag, 2)
    assert len(body) == ANSWER_RAW - 4
    return body + be(crc(body), 4)


def cobs_encode(data):
    out = bytearray([0])
    code_at, code = 0, 1
    for b in data:
        if b == 0:
            out[code_at] = code
            code_at, code = len(out), 1
            out.append(0)
        else:
            out.append(b)
            code += 1
            if code == 0xFF:
                out[code_at] = code
                code_at, code = len(out), 1
                out.append(0)
    out[code_at] = code
    return bytes(out)


def cobs_decode(seg):
    out = bytearray()
    i = 0
    while i < len(seg):
        code = seg[i]
        if code == 0:
            raise DecodeError
        i += 1
        if i + code - 1 > len(seg):
            raise DecodeError
        out += seg[i:i + code - 1]
        i += code - 1
        if code < 0xFF and i < len(seg):
            out.append(0)
    return bytes(out)


def wire(raw):
    return cobs_encode(raw) + b"\x00"


def segments(stream):
    """The machine's inputs for the bytes of stream: one per non-empty segment, either the
    decoded bytes or the string "decode" or "overflow"."""
    calls = []
    seg = bytearray()
    over = False
    for b in stream:
        if b == 0:
            if over:
                calls.append("overflow")
            elif seg:
                try:
                    calls.append(cobs_decode(bytes(seg)))
                except DecodeError:
                    calls.append("decode")
            seg, over = bytearray(), False
        elif not over:
            seg.append(b)
            if len(seg) > MAX_SEGMENT:
                over = True
    return calls


def comm_check(x, synced, expected):
    """The board's communication checks: the diagnostic code of the first that fails, or 0."""
    if x == "decode":
        return 0x1001
    if x == "overflow":
        return 0x1002
    if len(x) != SCAN_RAW:
        return 0x1003
    if int.from_bytes(x[31:35], "big") != crc(x[:31]):
        return 0x1004
    if x[0] != SCAN_TAG:
        return 0x1005
    if synced and int.from_bytes(x[1:5], "big") != expected:
        return 0x1006
    return 0


V_MAX, V_MIN = 3650, 2500
T_MAX, T_MIN = 550, -200
T_CHG_MIN, T_CHG_MAX = 0, 450
I_CHG_MAX = I_DIS_MAX = 280_000
I_CHG_DETECT = 2800
V_SENS_LO, V_SENS_HI = 1000, 4500
T_SENS_LO, T_SENS_HI = -400, 1250
P_SENS_HI = 20_000
TOL_SUM, TOL_PC = 300, 500
N_PC, D_EDM = 10, 2
UNANSWERED = 0xFFFFFFFF

RESET_REQUIRED, STANDBY, PRECHARGE, NORMAL, FAULT = range(5)
STATES = ("RESET_REQUIRED", "STANDBY", "PRECHARGE", "NORMAL", "FAULT")
AUX_NEG, AUX_PRE, AUX_POS, STOP_OK, RESET, RUN = 0x01, 0x02, 0x04, 0x08, 0x10, 0x20


def permit_of(mode):
    return {PRECHARGE: 0x03, NORMAL: 0x05}.get(mode, 0x00)


def signed(bits, n):
    return n - (1 << bits) if n >= 1 << (bits - 1) else n


@dataclass(frozen=True)
class Scan:
    tag: int
    seq: int
    cells: tuple
    temps: tuple
    current: int
    pack: int
    bus: int
    digital: int


def decode_scan(raw):
    """The fields of a raw scan record of 35 bytes."""
    f = lambda off, n: int.from_bytes(raw[off:off + n], "big")
    return Scan(tag=raw[0], seq=f(1, 4), cells=tuple(f(5 + 2 * i, 2) for i in range(4)),
                temps=tuple(signed(16, f(13 + 2 * i, 2)) for i in range(2)),
                current=signed(32, f(17, 4)), pack=f(21, 4), bus=f(25, 4), digital=f(29, 2))


@dataclass(frozen=True)
class Answer:
    board: int
    answered: int
    permit: int
    state: int
    code: int

    def __str__(self):
        state = STATES[self.state] if self.state < len(STATES) else f"state {self.state}"
        return f"{self.permit:#04x} {state} {self.code:#06x}"


def decode_answer(raw):
    """The answer that raw holds when it is authentic in the sense of BR1: it has 17 bytes, the
    tag 0x80, and the CRC of the link identifier and bytes 0 to 12.  Otherwise None."""
    if (len(raw) != ANSWER_RAW or raw[0] != ANSWER_TAG
            or int.from_bytes(raw[13:17], "big") != crc(raw[:13])):
        return None
    return Answer(board=int.from_bytes(raw[1:5], "big"), answered=int.from_bytes(raw[5:9], "big"),
                  permit=raw[9], state=raw[10], code=int.from_bytes(raw[11:13], "big"))


@dataclass(frozen=True)
class State:
    mode: int
    diag: int
    synced: bool
    expected: int
    answers: int
    prev_reset: bool
    age: tuple
    pc_count: int
    first: bool


INIT = State(mode=RESET_REQUIRED, diag=0x0001, synced=False, expected=0, answers=0,
             prev_reset=True, age=(0, 0, 0), pc_count=0, first=True)


def record_ok(x):
    """Whether the segment result x decodes to 35 bytes whose CRC matches."""
    return (isinstance(x, bytes) and len(x) == SCAN_RAW
            and int.from_bytes(x[31:35], "big") == crc(x[:31]))


def good(x):
    return record_ok(x) and x[0] == SCAN_TAG


def content_failure(permit, age, sc):
    """The code of the first of checks 7 to 17 that the record sc fails, or None."""
    charging = sc.current > I_CHG_DETECT
    aux = any((sc.digital >> r & 1) != (permit >> r & 1) and age[r] >= D_EDM for r in range(3))
    for failed, code in (
            (sc.digital >> 6 != 0, 0x1007),
            (any(not V_SENS_LO <= c <= V_SENS_HI for c in sc.cells)
             or any(not T_SENS_LO <= t <= T_SENS_HI for t in sc.temps)
             or sc.pack > P_SENS_HI or sc.bus > P_SENS_HI, 0x2001),
            (any(c > V_MAX for c in sc.cells), 0x2002),
            (any(c < V_MIN for c in sc.cells), 0x2003),
            (any(t > T_MAX for t in sc.temps), 0x2004),
            (any(t < T_MIN for t in sc.temps), 0x2005),
            (sc.current > I_CHG_MAX, 0x2006),
            (sc.current < -I_DIS_MAX, 0x2007),
            (charging and any(not T_CHG_MIN <= t <= T_CHG_MAX for t in sc.temps), 0x2008),
            (abs(sum(sc.cells) - sc.pack) > TOL_SUM, 0x2009),
            (aux, 0x3001)):
        if failed:
            return code
    return None


def failure(s, x):
    """The code of the first check from 1 to 17 that the segment result x fails in the state s, or
    None."""
    if x == "decode":
        return 0x1001
    if x == "overflow":
        return 0x1002
    if len(x) != SCAN_RAW:
        return 0x1003
    if not record_ok(x):
        return 0x1004
    if x[0] != SCAN_TAG:
        return 0x1005
    sc = decode_scan(x)
    if s.synced and sc.seq != s.expected:
        return 0x1006
    return content_failure(permit_of(s.mode), s.age, sc)


def precharge_condition(sc):
    return abs(sc.bus - sc.pack) <= TOL_PC and sc.digital & (AUX_NEG | AUX_PRE) == AUX_NEG | AUX_PRE


def next_mode(s, x):
    """The next state, code, and precharge count: rules 1 to 5 of the requirements."""
    code = failure(s, x)
    if code is not None:
        return FAULT, s.diag if s.mode == FAULT else code, s.pc_count
    sc = decode_scan(x)
    run, aux = sc.digital & RUN, sc.digital & 7
    if not sc.digital & STOP_OK:
        if s.mode in (RESET_REQUIRED, FAULT):
            return s.mode, s.diag, s.pc_count
        return RESET_REQUIRED, 0x5001, s.pc_count
    if s.mode in (RESET_REQUIRED, FAULT):
        if s.synced and not s.prev_reset and sc.digital & RESET and not run and aux == 0:
            return STANDBY, 0x0000, s.pc_count
        return s.mode, s.diag, s.pc_count
    if s.mode == STANDBY:
        return (PRECHARGE, s.diag, 0) if run and aux == 0 else (STANDBY, s.diag, s.pc_count)
    if s.mode == PRECHARGE:
        if not run:
            return STANDBY, s.diag, s.pc_count
        if precharge_condition(sc):
            return NORMAL, s.diag, s.pc_count
        if s.pc_count + 1 >= N_PC:
            return FAULT, 0x3002, s.pc_count
        return PRECHARGE, s.diag, s.pc_count + 1
    return (STANDBY if not run else NORMAL), s.diag, s.pc_count


def step(s, x):
    """The state after the segment result x in the state s, and the answer to it."""
    mode, diag, pc_count = next_mode(s, x)
    is_good = good(x)
    sc = decode_scan(x) if is_good else None
    comm = is_good and not (s.synced and sc.seq != s.expected)
    before, after = permit_of(s.mode), permit_of(mode)
    age = tuple(0 if s.first or (after ^ before) >> r & 1
                else min(s.age[r] + 1, D_EDM) if comm else s.age[r] for r in range(3))
    nxt = State(mode=mode, diag=diag, synced=is_good,
                expected=(sc.seq + 1) % (1 << 32) if is_good else s.expected,
                answers=(s.answers + 1) % (1 << 32),
                prev_reset=bool(sc.digital & RESET) if comm else s.prev_reset,
                age=age, pc_count=pc_count, first=False)
    answered = int.from_bytes(x[1:5], "big") if record_ok(x) else UNANSWERED
    return nxt, Answer(board=s.answers, answered=answered, permit=after, state=mode, code=diag)


def answer_bytes(a):
    return answer_record(a.board, a.answered, a.permit, a.state, a.code)


def machine(s, x):
    s, a = step(s, x)
    return s, answer_bytes(a)


class Board:
    """The board's framing and machine from a board reset: push takes each byte that the program
    reads and returns the encoded answer, followed by 0x00, when the byte ends a non-empty
    segment, and None otherwise."""

    def __init__(self):
        self.state = INIT
        self.seg = bytearray()
        self.over = False

    def push(self, b):
        if b != 0:
            if not self.over:
                self.seg.append(b)
                self.over = len(self.seg) > MAX_SEGMENT
            return None
        seg, over = bytes(self.seg), self.over
        self.seg, self.over = bytearray(), False
        if over:
            x = "overflow"
        elif not seg:
            return None
        else:
            try:
                x = cobs_decode(seg)
            except DecodeError:
                x = "decode"
        self.state, raw = machine(self.state, x)
        return wire(raw)


def self_test():
    rng = random.Random(1)
    for _ in range(20000):
        n = rng.randrange(0, 300)
        data = bytes(rng.choice((0, 1, 255, rng.randrange(256))) for _ in range(n))
        enc = cobs_encode(data)
        if 0 in enc or cobs_decode(enc) != data:
            print("COBS self-test failed for", data.hex())
            sys.exit(1)
        if n < 254 and len(enc) != n + 1:
            print("COBS length", len(enc), "for", n, "bytes")
            sys.exit(1)
    s = State(mode=NORMAL, diag=0, synced=True, expected=7, answers=8, prev_reset=False,
              age=(2, 2, 2), pc_count=0, first=False)
    if machine(s, scan_record(**VECTOR_SCAN))[1] != answer_record(**VECTOR_ANSWER):
        print("the machine's answer to the scan vector is not the answer vector")
        sys.exit(1)


VECTOR_SCAN = dict(seq=7, cells=(3300, 3301, 3299, 3302), temps=(250, 245), current=-10000,
                   pack=13202, bus=13150, digital=0x002D)
VECTOR_ANSWER = dict(board_seq=8, answered=7, permit=0x05, state=3, diag=0x0000)


def spaced(bs):
    return " ".join(f"{b:02x}" for b in bs)


def vectors():
    scan = scan_record(**VECTOR_SCAN)
    ans = answer_record(**VECTOR_ANSWER)
    print("link identifier:", LINK.decode(), f"(CRC-32 {zlib.crc32(LINK):#010x})")
    for name, raw in (("scan", scan), ("answer", ans)):
        w = wire(raw)
        print(f"{name} raw ({len(raw)} bytes, CRC {int.from_bytes(raw[-4:], 'big'):#010x}):")
        print("  " + spaced(raw))
        print(f"{name} wire ({len(w)} bytes):")
        print("  " + spaced(w))
        print(f"  zlib.crc32 without the link identifier: {zlib.crc32(raw[:-4]):#010x}")
    rec, ans_len = len(wire(scan)), len(wire(ans))
    ms = lambda n: 1000 * n * BITS_PER_BYTE / BAUD
    print(f"line time at {BAUD} baud: record {ms(rec):.3f} ms, answer {ms(ans_len):.3f} ms, "
          f"exchange {ms(rec + ans_len):.3f} ms, byte {ms(1):.4f} ms")


def faults():
    scan = scan_record(**VECTOR_SCAN)
    w = wire(scan)
    exp = VECTOR_SCAN["seq"]
    following = wire(scan_record(**dict(VECTOR_SCAN, seq=exp + 1)))
    kinds = {"lost": Counter(), "inserted": Counter(), "replaced": Counter(),
             "replaced by 0x00": Counter()}

    def run(stream):
        res = []
        synced, expected = True, exp
        for x in segments(stream):
            code = comm_check(x, synced, expected)
            res.append((code, x))
            synced = code in (0, 0x1006)
            if synced:
                expected = (int.from_bytes(x[1:5], "big") + 1) % (1 << 32)
        return res

    def outcome(faulty):
        first = run(b"\x00" + faulty)
        current = any(code in (0, 0x1006) and x[1:5] == be(exp, 4) for code, x in first)
        rest = following if current else b"\x00" + following
        names = [f"{code:#06x}" if code else "accepted" for code, _ in run(b"\x00" + faulty + rest)]
        return ", ".join(names) if names else "no segment"

    for i in range(len(w)):
        kinds["lost"][outcome(w[:i] + w[i + 1:])] += 1
        for v in range(256):
            kinds["inserted"][outcome(w[:i] + bytes([v]) + w[i:])] += 1
            if v != w[i]:
                kind = "replaced by 0x00" if v == 0 else "replaced"
                kinds[kind][outcome(w[:i] + bytes([v]) + w[i + 1:])] += 1
    for v in range(256):
        kinds["inserted"][outcome(w + bytes([v]))] += 1
    print("wire bytes:", spaced(w))
    for kind, counts in kinds.items():
        print(f"{kind}: {sum(counts.values())} faults")
        for result, n in sorted(counts.items(), key=lambda kv: -kv[1]):
            print(f"  {n:6d}  {result}")
    lost_delim = outcome(w[:-1])
    print("lost delimiter alone:", lost_delim)


def gen(seed, n, prefix):
    rng = random.Random(seed)
    other = b"LeanExe-BMS-0002"
    board = Board()
    permit, mode = 0, RESET_REQUIRED
    seq = rng.randrange(1 << 32)
    digital = STOP_OK
    ins, outs = [], []
    seen = Counter()

    def pick(lo, hi, near):
        if near and rng.random() < 0.02:
            return rng.choice(near) + rng.choice((-1, 0, 1))
        return rng.randrange(lo, hi + 1)

    def raw_scan(s, d, link=LINK, tag=SCAN_TAG):
        cells = tuple(pick(2600, 3600, (V_MIN, V_MAX, V_SENS_LO, V_SENS_HI)) for _ in range(4))
        temps = tuple(pick(0, 450, (T_MIN, T_MAX, T_CHG_MIN, T_CHG_MAX, T_SENS_LO, T_SENS_HI))
                      for _ in range(2))
        current = pick(-250_000, 250_000, (I_CHG_MAX, -I_DIS_MAX, I_CHG_DETECT))
        pack = max(0, sum(cells) + pick(-280, 280, (TOL_SUM, -TOL_SUM)))
        if rng.random() < 0.7:
            bus = max(0, pack + pick(-600, 600, (TOL_PC, -TOL_PC)))
        else:
            bus = pick(0, 15000, ())
        body = bytes([tag]) + be(s, 4) + b"".join(be(c, 2) for c in cells)
        body += b"".join(be(t, 2) for t in temps) + be(current, 4) + be(pack, 4) + be(bus, 4)
        body += be(d, 2)
        return body + be(zlib.crc32(body, zlib.crc32(link)), 4)

    for _ in range(n):
        if mode in (RESET_REQUIRED, FAULT):
            toggles = ((0.3, RESET), (0.5, RUN if digital & RUN else 0), (0.03, STOP_OK))
        elif mode == STANDBY:
            toggles = ((0.1, RESET), (0.3, 0 if digital & RUN else RUN), (0.01, STOP_OK))
        else:
            toggles = ((0.05, RESET), (0.03, RUN), (0.01, STOP_OK))
        for p, bit in toggles:
            if rng.random() < p:
                digital ^= bit
        aux = permit if rng.random() < 0.95 else rng.randrange(8)
        d = (digital & ~7) | aux
        if rng.random() < 0.003:
            d |= 1 << rng.randrange(6, 16)
        w = wire(raw_scan(seq, d))
        seq = (seq + 1) % (1 << 32)
        if rng.random() < 0.96:
            data = w
        else:
            f = rng.randrange(12)
            i = rng.randrange(len(w) - 1)
            if f == 0:
                data = w[:i] + w[i + 1:]
            elif f == 1:
                data = w[:i] + bytes([rng.randrange(1, 256)]) + w[i:]
            elif f == 2:
                data = w[:i] + bytes([(w[i] + rng.randrange(1, 255)) % 256 or 1]) + w[i + 1:]
            elif f == 3:
                data = w[:i] + b"\x00" + w[i + 1:]
            elif f == 4:
                data = wire(raw_scan((seq - 1) % (1 << 32), d, link=other))
            elif f == 5:
                data = wire(raw_scan((seq - 1) % (1 << 32), d, tag=0x11))
            elif f == 6:
                data = wire(raw_scan((seq - 2) % (1 << 32), d))
            elif f == 7:
                seq = (seq + 1) % (1 << 32)
                data = wire(raw_scan((seq - 1) % (1 << 32), d))
            elif f == 8:
                data = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 45)))
            elif f == 9:
                data = b"\x00"
            elif f == 10:
                data = bytes(rng.randrange(1, 256) for _ in range(rng.randrange(37, 60))) + b"\x00"
            else:
                data = w[:-1]
        ins.append(data.hex())
        for b in data:
            frame = board.push(b)
            if frame:
                outs.append(frame.hex())
                a = decode_answer(cobs_decode(frame[:-1]))
                permit, mode = a.permit, a.state
                seen[STATES[a.state]] += 1
        if rng.random() < 0.002:
            ins.append("reset")
            outs.append("reset")
            board = Board()
            permit, mode = 0, RESET_REQUIRED
    with open(prefix + ".in", "w") as f:
        f.write("\n".join(ins) + "\n")
    with open(prefix + ".out", "w") as f:
        f.write("\n".join(outs) + "\n")
    print(f"{n} writes, {sum(o != 'reset' for o in outs)} answers, {outs.count('reset')} resets "
          f"to {prefix}.in and {prefix}.out; answers by state: "
          + ", ".join(f"{k} {v}" for k, v in sorted(seen.items())))


def main():
    if len(sys.argv) == 5 and sys.argv[1] == "gen":
        self_test()
        gen(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
        return
    if len(sys.argv) != 2 or sys.argv[1] not in ("vectors", "faults"):
        print(__doc__.strip().splitlines()[-1])
        sys.exit(2)
    self_test()
    vectors() if sys.argv[1] == "vectors" else faults()


if __name__ == "__main__":
    main()
