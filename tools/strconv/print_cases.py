# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Generate data/strconv/print-cases.txt, the cases of Verified/Examples/PrintFloatAccuracy.lean.

Usage: uv run tools/strconv/print_cases.py OUTPUT

Each output line is `bits word sci ecma`: the format (64 or 32), the word in hexadecimal, and the
expected scientific and ECMAScript strings.  The expected strings come from this program, which
finds the shortest decimal by a search over the number of significant digits with exact rational
arithmetic: for each count n from 1 upward, every n-digit decimal in the rounding interval of the
word, at every decimal exponent the interval reaches, is a candidate, and the first count with a
candidate gives the result, the candidate nearest to the word's value, with an even last digit at a
tie.  This search does not use the largest-exponent method of PrintFloat.lean.  For binary64 the
digits and exponent must also agree with Python's repr, which prints the shortest decimal that
rounds to the float.  The words are the zeros, infinities, and NaNs, the smallest subnormals, the
largest subnormal, the smallest normal, the starts of binades, the largest finite word, values
next to powers of ten and to the ECMAScript layout's limits, and words drawn from a fixed seed.
"""
import math, random, struct, sys
from fractions import Fraction as F

FMT = {64: (53, 11, 1074), 32: (24, 8, 149)}


def decode(w, bits):
    p, eb, nu = FMT[bits]
    fb = p - 1
    neg = (w >> (bits - 1)) & 1 == 1
    ef = (w >> fb) & ((1 << eb) - 1)
    fr = w & ((1 << fb) - 1)
    if ef == (1 << eb) - 1:
        return ('nan',) if fr else ('inf', neg)
    if ef == 0 and fr == 0:
        return ('zero', neg)
    Q = fr if ef == 0 else fr + (1 << fb)
    E = 1 if ef == 0 else ef
    return ('num', neg, Q, E, ef >= 2 and fr == 0)


def interval(Q, E, low, nu):
    unit = F(2) ** (E - 1 - nu)
    v = Q * unit
    lo = (F(4 * Q - 1, 4) if low else F(2 * Q - 1, 2)) * unit
    hi = F(2 * Q + 1, 2) * unit
    return v, lo, hi, Q % 2 == 0


def inside(x, lo, hi, closed):
    return lo <= x <= hi if closed else lo < x < hi


def floor_log10(x):
    e = math.floor(math.log10(x.numerator) - math.log10(x.denominator))
    while F(10) ** e > x:
        e -= 1
    while F(10) ** (e + 1) <= x:
        e += 1
    return e


def shortest(Q, E, low, nu):
    v, lo, hi, closed = interval(Q, E, low, nu)
    for n in range(1, 30):
        cands = []
        for e in range(floor_log10(lo) - n, floor_log10(hi) - n + 3):
            s = F(10) ** e
            m0 = max(10 ** (n - 1), math.ceil(lo / s))
            m1 = min(10 ** n - 1, math.floor(hi / s))
            for m in range(m0, m1 + 1):
                if inside(m * s, lo, hi, closed):
                    cands.append((abs(m * s - v), m % 2, m, e))
        if cands:
            cands.sort()
            if len(cands) > 1 and cands[0][0] == cands[1][0]:
                assert cands[0][3] == cands[1][3], 'tie across exponents'
            _, _, m, e = cands[0]
            assert m % 10 != 0
            return m, e
    raise AssertionError('no decimal found')


def sci(neg, t, k):
    ds = str(t)
    x = k + len(ds) - 1
    return ('-' if neg else '') + ds[0] + ('' if len(ds) == 1 else '.' + ds[1:]) + 'e' + str(x)


def ecma(neg, t, k):
    ds = str(t)
    n = k + len(ds)
    sgn = '-' if neg else ''
    if len(ds) <= n <= 21:
        return sgn + ds + '0' * (n - len(ds))
    if 0 < n <= 21:
        return sgn + ds[:n] + '.' + ds[n:]
    if -6 < n <= 0:
        return sgn + '0.' + '0' * (-n) + ds
    x = n - 1
    return (sgn + ds[0] + ('' if len(ds) == 1 else '.' + ds[1:]) + 'e' + ('+' if x >= 0 else '-')
            + str(abs(x)))


def expected(w, bits):
    d = decode(w, bits)
    if d[0] == 'nan':
        return 'NaN', 'NaN'
    if d[0] == 'inf':
        s = '-Infinity' if d[1] else 'Infinity'
        return s, s
    if d[0] == 'zero':
        return ('-0e0', '-0') if d[1] else ('0e0', '0')
    _, neg, Q, E, low = d
    t, k = shortest(Q, E, low, FMT[bits][2])
    if bits == 64:
        r = repr(struct.unpack('<d', struct.pack('<Q', w))[0])
        mant, _, ex = r.lower().partition('e')
        mant = mant.lstrip('-')
        ip, _, fp = mant.partition('.')
        digits = (ip + fp).lstrip('0')
        exp = (int(ex) if ex else 0) - len(fp)
        stripped = digits.rstrip('0')
        exp += len(digits) - len(stripped)
        assert (int(stripped), exp) == (t, k), (hex(w), r, t, k)
    return sci(neg, t, k), ecma(neg, t, k)


def words(bits, rng):
    p, eb, _ = FMT[bits]
    fb = p - 1
    top = (1 << eb) - 1
    sign = 1 << (bits - 1)
    ws = [0, sign, top << fb, sign | (top << fb), (top << fb) | 1, (top << fb) | (1 << (fb - 1)),
          sign | (top << fb) | 5]
    ws += list(range(1, 13))
    ws += [(1 << fb) - 1, 1 << fb, (1 << fb) + 1, ((top - 1) << fb) | ((1 << fb) - 1)]
    ws += [e << fb for e in range(1, top, max(1, top // 40))]
    ws += [(e << fb) - 1 for e in range(2, top, max(1, top // 30))]
    for x in [1.0, 0.1, 0.2, 0.3, 1 / 3, 2 / 3, 1e21, 1e-6, 1e-7, 123456.789, 9007199254740993.0,
              5e-324, 2.2250738585072014e-308, 1.7976931348623157e308, 1e22, 1e23, 4.35,
              0.000001, 0.0000001, 1e20, 1e300, 1e-300, 299792458.0, 3.141592653589793]:
        if bits == 64:
            ws.append(struct.unpack('<Q', struct.pack('<d', x))[0])
        elif abs(x) < 3.4e38:
            ws.append(struct.unpack('<I', struct.pack('<f', x))[0])
    for k in range(-45 if bits == 32 else -324, 39 if bits == 32 else 309, 7):
        x = 10.0 ** k
        if bits == 64:
            if x == 0.0 or math.isinf(x):
                continue
            w = struct.unpack('<Q', struct.pack('<d', x))[0]
        else:
            try:
                w = struct.unpack('<I', struct.pack('<f', x))[0]
            except OverflowError:
                continue
            if w & ((top << fb) | ((1 << fb) - 1)) == 0:
                continue
        ws += [w - 1, w, w + 1]
    ws += [rng.getrandbits(bits) for _ in range(150)]
    ws += [rng.randrange(1, 1 << (fb + 3)) for _ in range(30)]
    out = []
    for w in ws:
        w &= (1 << bits) - 1
        if w not in out:
            out.append(w)
    return out


def main():
    rng = random.Random(20261012)
    lines = []
    for bits in (64, 32):
        for w in words(bits, rng):
            s, e = expected(w, bits)
            lines.append(f'{bits} {w:x} {s} {e}')
    with open(sys.argv[1], 'w') as f:
        f.write('\n'.join(lines) + '\n')
    print(len(lines), 'cases')


if __name__ == '__main__':
    main()
