# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The wire format of the BMS protection demo (Demos/Bms/requirements.md): the scan record that
the bridge sends, the answer that the board returns, the CRC over the link identifier and a
record's bytes, COBS framing (Cheshire and Baker 1999) with a 0x00 after each encoded record, and
the board's communication checks.

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
may lose.  The script checks its COBS encoder and decoder on random records first and exits with
status 1 if they disagree.

Usage: uv run tests/baremetal/bms_proto.py vectors | faults
"""

import random
import sys
import zlib
from collections import Counter

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


def main():
    if len(sys.argv) != 2 or sys.argv[1] not in ("vectors", "faults"):
        print(__doc__.strip().splitlines()[-1])
        sys.exit(2)
    self_test()
    vectors() if sys.argv[1] == "vectors" else faults()


if __name__ == "__main__":
    main()
