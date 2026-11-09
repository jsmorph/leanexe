# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""A mirror of the delimited framing of LeanExe/Requests/Delimited.lean and of the echo of
records of tests/TestSupport/M7/Delim.lean, and its check against the Lean definitions.

cobs_encode transcribes StuffData of Cheshire and Baker (1999), as cobsEncode does: a block ends
with the code len + 1 at each zero byte and at the end of the data, and with the code 0xFF after
254 nonzero bytes, so a final run of 254 nonzero bytes gets a block 0x01 after it.  cobs_decode
is cobsDecode: each block is a code byte c from 1 to 255 followed by c - 1 nonzero bytes, and
gives them followed by a zero when c < 0xFF; the result must end with that zero, which it drops.
It rejects the variant without the final 0x01, which the cobs package on PyPI writes, so this
mirror does not use that package.  segments, seg_result, echo_mach, and answers mirror
segments, segResult, echoMach, and delimAnswers.

"gen SEED N FILE" writes N cases of each kind to FILE, one a line: "enc HEX" asks for
cobsEncode of a record, "dec HEX" for cobsDecode of a byte string, and "ans HEX" for
delimAnswers echoMach 36 0 of a byte stream.  The records have random lengths up to 600, with
long runs of nonzero bytes so that blocks of code 0xFF occur, and the byte strings and streams
are encodings with random corruptions: a byte changed, lost, inserted, or set to zero, a
truncation, a zero inserted, or a run of nonzero bytes longer than 36.  "check FILE LEAN" reads
FILE and the answers that tests/baremetal/DelimMirror.lean wrote to LEAN, one a line, HEX or
"none", and requires each to equal this mirror's.  It prints one line and exits with status 0
or 1.

Usage: uv run tests/baremetal/delim_frame.py gen SEED N FILE
       uv run tests/baremetal/delim_frame.py check FILE LEAN
"""

import random
import sys

MAX_LEN = 36


def cobs_encode(r):
    out = bytearray()
    blk = bytearray()
    for b in r:
        if b == 0:
            out.append(len(blk) + 1)
            out += blk
            blk = bytearray()
        elif len(blk) == 253:
            out.append(0xFF)
            out += blk + bytes([b])
            blk = bytearray()
        else:
            blk.append(b)
    out.append(len(blk) + 1)
    out += blk
    return bytes(out)


def cobs_unstuff(s):
    out = bytearray()
    i = 0
    while i < len(s):
        c = s[i]
        data = s[i + 1:i + c]
        if c == 0 or len(data) < c - 1 or 0 in data:
            return None
        out += data
        if c < 0xFF:
            out.append(0)
        i += c
    return bytes(out)


def cobs_decode(s):
    u = cobs_unstuff(s)
    if u is None or not u or u[-1] != 0:
        return None
    return u[:-1]


def segments(bs):
    """The complete segments: the bytes between consecutive zero bytes, the first beginning at
    the start of bs."""
    segs = []
    cur = bytearray()
    for b in bs:
        if b == 0:
            segs.append(bytes(cur))
            cur = bytearray()
        else:
            cur.append(b)
    return segs


def seg_result(s, max_len=MAX_LEN):
    if len(s) > max_len:
        return ("overflow", None)
    r = cobs_decode(s)
    return ("decode", None) if r is None else ("ok", r)


def echo_mach(c, res):
    kind, r = res
    if kind == "ok":
        return c + 1, bytes([0, c & 0xFF]) + r
    return c + 1, bytes([1 if kind == "decode" else 2, c & 0xFF])


def answer_list(bs, c=0):
    """The echo's answers, each encoded and followed by a zero, to the nonempty complete
    segments of bs, from the count c, and the count after them."""
    out = []
    for s in segments(bs):
        if s:
            c, a = echo_mach(c, seg_result(s))
            out.append(cobs_encode(a) + b"\x00")
    return out, c


def answers(bs):
    return b"".join(answer_list(bs)[0])


def record(rng, n):
    """A record of n bytes: runs of nonzero bytes, some long, separated by zeros."""
    out = bytearray()
    while len(out) < n:
        if rng.random() < 0.3:
            out.append(0)
        else:
            run = rng.choice([1, 3, 20, 253, 254, 255, 300])
            out += bytes(rng.randrange(1, 256) for _ in range(run))
    return bytes(out[:n])


def corrupt(rng, s):
    """The byte string s with one random corruption."""
    if not s:
        return bytes([rng.randrange(256)])
    i = rng.randrange(len(s))
    k = rng.randrange(7)
    if k == 0:
        return s[:i] + bytes([rng.randrange(1, 256)]) + s[i + 1:]
    if k == 1:
        return s[:i] + s[i + 1:]
    if k == 2:
        return s[:i] + bytes([rng.randrange(256)]) + s[i:]
    if k == 3:
        return s[:i] + b"\x00" + s[i + 1:]
    if k == 4:
        return s[:i]
    if k == 5:
        return s[:i] + b"\x00" + s[i:]
    return bytes(rng.randrange(1, 256) for _ in range(rng.randrange(37, 60)))


def stream(rng):
    """A stream of encoded short records and delimiters with corruptions, empty segments, and
    overlong segments."""
    out = bytearray()
    for _ in range(rng.randrange(1, 12)):
        enc = cobs_encode(record(rng, rng.randrange(0, 40)))
        k = rng.randrange(5)
        if k == 0:
            out += corrupt(rng, enc)
        elif k == 1:
            out += b""
        else:
            out += enc
        out += b"\x00" * rng.choice([1, 1, 1, 2])
    if rng.random() < 0.3:
        out += cobs_encode(record(rng, 5))
    return bytes(out)


VECTORS = [
    # Section 5.8 of the BMS design: a DIGITAL record and an ANSWER record with their wire bytes.
    ("40 00 00 00 07 00 08 d2 f3 34 b0", "02 40 01 01 02 07 06 08 d2 f3 34 b0 00"),
    ("80 00 00 00 07 00 00 00 07 00 01 00 00 78 9d b8 7b",
     "02 80 01 01 02 07 01 01 02 07 02 01 01 05 78 9d b8 7b 00"),
]


def gen(seed, n, path):
    rng = random.Random(seed)
    lines = ["enc " + raw.replace(" ", "") for raw, _ in VECTORS]
    for _ in range(n):
        lines.append("enc " + record(rng, rng.randrange(0, 600)).hex())
    for _ in range(n):
        enc = cobs_encode(record(rng, rng.randrange(0, 600)))
        lines.append("dec " + (enc if rng.random() < 0.3 else corrupt(rng, enc)).hex())
    for _ in range(n):
        lines.append("ans " + stream(rng).hex())
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def expected(kind, data):
    if kind == "enc":
        return "ok " + cobs_encode(data).hex()
    if kind == "dec":
        r = cobs_decode(data)
        return "none" if r is None else "ok " + r.hex()
    return "ok " + answers(data).hex()


def check(path, lean_path):
    for raw, wire in VECTORS:
        raw, wire = bytes.fromhex(raw.replace(" ", "")), bytes.fromhex(wire.replace(" ", ""))
        if cobs_encode(raw) + b"\x00" != wire:
            print(f"fail: the encoding of {raw.hex()} is not the design's {wire.hex()}")
            return 1
    with open(path) as f:
        cases = [line.split() for line in f if line.strip()]
    with open(lean_path) as f:
        got = [line.rstrip() for line in f if line.strip()]
    if len(got) != len(cases):
        print(f"fail: {len(got)} Lean answers for {len(cases)} cases")
        return 1
    counts = {"enc": 0, "dec": 0, "ans": 0}
    decoded = 0
    for i, (case, g) in enumerate(zip(cases, got)):
        kind, data = case[0], bytes.fromhex(case[1] if len(case) > 1 else "")
        e = expected(kind, data).rstrip()
        if g != e:
            print(f"fail: case {i}, {kind} {data.hex()[:80]}: Lean {g[:80]}, mirror {e[:80]}")
            return 1
        counts[kind] += 1
        decoded += kind == "dec" and e != "none"
    print(f"pass: {counts['enc']} encodings, {counts['dec']} decodings ({decoded} accepted), "
          f"and {counts['ans']} answer streams equal the Lean definitions'")
    return 0


def main():
    args = sys.argv[1:]
    if len(args) == 4 and args[0] == "gen":
        gen(int(args[1]), int(args[2]), args[3])
        return 0
    if len(args) == 3 and args[0] == "check":
        return check(args[1], args[2])
    print(__doc__.split("Usage:")[1].strip(), file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
