#!/usr/bin/env python3
"""Binary64 exp test inputs and a Python Decimal accuracy reference."""

import decimal
import json
import math
from pathlib import Path
import random
import struct
import sys

D = decimal.Decimal
INF = 0x7FF0000000000000
NAN = 0x7FF8000000000000


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def value(word):
    return struct.unpack("<d", struct.pack("<Q", word))[0]


def inputs():
    words = {0, 1, 0x8000000000000000, 0x8000000000000001,
             INF, INF | (1 << 63), NAN, NAN | (1 << 63), INF + 1, (INF + 1) | (1 << 63)}

    def around(x, radius=2):
        word = bits(x)
        words.update(w for w in range(word - radius, word + radius + 1) if 0 <= w < 2**64)

    for x in [-1024., -746., -745., -710., -709., -512., -1., -2**-54,
              2**-54, 1., 512., 709., 710., 1024.]:
        around(x, 16)
    with decimal.localcontext() as ctx:
        ctx.prec = 100
        ln2 = D(2).ln()
        for k in range(-137600, 131073, 64):
            around(float((D(k) + D('0.5')) * ln2 / 128))
        for y in [D(2)**-1075, D(2)**-1074, D(2)**-1022,
                  D(2)**1024 - D(2)**970]:
            around(float(y.ln()), 32)
    rng = random.Random(20260927)
    for _ in range(20000):
        words.add(bits(rng.uniform(-746., 710.)))
    for _ in range(4000):
        words.add(rng.getrandbits(64))
    for exponent in range(2047):
        word = (exponent << 52) | rng.getrandbits(52)
        words.update([word, word | (1 << 63)])
    return sorted(words)


def reference(word):
    x = value(word)
    if math.isnan(x):
        return NAN, None
    if x >= 1024:
        return INF, None
    if x <= -1024:
        return 0, None
    for precision in [100, 200, 400]:
        with decimal.localcontext() as ctx:
            ctx.prec = precision
            y = D.from_float(x).exp()
            lo, hi = y.next_minus(), y.next_plus()
            rounded = bits(float(lo))
            if rounded == bits(float(hi)):
                return rounded, (lo, hi)
    raise AssertionError(f"reference rounding unresolved for {x.hex()}")


def check(path):
    rows = json.loads(Path(path).read_text())
    report = {name: {"maxUlpError": "0", "worstInput": None, "roundedDifferences": 0}
              for name in ["wasm", "leanExp", "javascript"]}
    with decimal.localcontext() as ctx:
        ctx.prec = 120
        ctx.rounding = decimal.ROUND_CEILING
        for row in rows:
            word = int(row["input"])
            rounded, interval = reference(word)
            for name, stats in report.items():
                result = int(row[name])
                if rounded == NAN:
                    assert math.isnan(value(result)), (name, row)
                    if name == "wasm":
                        assert result == NAN, row
                    continue
                stats["roundedDifferences"] += result != rounded
                if (rounded in [0, INF] and interval is None) or rounded == INF:
                    assert result == rounded, (name, row, rounded)
                    continue
                assert math.isfinite(value(result)) and result < (1 << 63), (name, row)
                lo, hi = interval
                y = D.from_float(value(result))
                exponent = math.frexp(value(rounded))[1] - 1 if rounded else -1074
                if lo < D.from_float(math.ldexp(1., exponent)):
                    exponent -= 1
                ulp = D.from_float(math.ldexp(1., max(-1074, exponent - 52)))
                error = max(y - lo, hi - y) / ulp
                if error > D(stats["maxUlpError"]):
                    stats["maxUlpError"] = str(error)
                    stats["worstInput"] = f"{word:016x}"
                if name == "wasm":
                    assert error < 1, ("error exceeds target", row, str(error))
    print(json.dumps({"cases": len(rows), "reference": "Python Decimal.exp, at least 100 digits",
                      "results": report}, indent=2))


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "generate":
        Path(sys.argv[2]).write_text("".join(f"{word}\n" for word in inputs()))
    elif len(sys.argv) == 3 and sys.argv[1] == "check":
        check(sys.argv[2])
    else:
        raise SystemExit("usage: exp-reference.py generate INPUT | check RESULTS")
