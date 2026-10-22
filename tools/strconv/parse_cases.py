# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Generate data/strconv/parse-cases.txt, the cases of tests/TestSupport/Numerics/ParseFloatAccuracy.lean.

Usage: uv run tools/strconv/parse_cases.py TAO_DATA_DIR GO_TESTFP OUTPUT

Each output line is `mode ok64 bits64 ok32 bits32 hex`: the grammar (`j` for RFC 8259, `g` for the
general grammar), whether the string is a number of that grammar, the expected binary64 and binary32
words in hexadecimal (0 when rejected), and the string's bytes in hexadecimal.  The expected words
come from exact rational arithmetic in this program, independent of the Lean code.  The cases are:
lines of Nigel Tao's parse-number-fxx-test-data (Apache-2.0), chosen to cover each of its files
(the first lines, evenly spaced lines, the longest strings, and the subnormal, infinite, and zero
results), whose f32 and f64 fields must agree with the computed words; the decimal inputs of
Paxson's tables as Go's src/internal/strconv/testdata/testfp.txt reproduces them; strings next to
the midpoints between neighboring values, with up to 1,100 digits; and strings for every
production and rejection of the grammar.
"""
import os, re, sys, random
from fractions import Fraction as F

JSON = re.compile(r'-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?')
DEC = re.compile(r'[+-]?([0-9]+(\.[0-9]*)?|\.[0-9]+)([eE][+-]?[0-9]+)?')
HEX = re.compile(r'[+-]?0[xX]([0-9a-fA-F]+(\.[0-9a-fA-F]*)?|\.[0-9a-fA-F]+)[pP][+-]?[0-9]+')
INF = re.compile(r'[+-]?(inf|infinity)', re.I)
NAN = re.compile(r'[+-]?nan', re.I)

FMT = {64: (53, 2047, 1074), 32: (24, 255, 149)}


def round_fmt(x, bits):
    """The nearest-even encoding of the nonnegative rational x, infinity from the threshold on."""
    p, Fe, nu = FMT[bits]
    half = 1 << (p - 1)
    limit = Fe * half
    y = x * (1 << nu)
    if y == 0:
        return 0
    n, d = y.numerator, y.denominator
    L = n.bit_length() - d.bit_length()
    if F(n, d) < F(2) ** L:
        L -= 1
    E = 1 if L <= p - 1 else L - p + 2
    if E >= Fe:
        return limit
    z = y / F(2) ** (E - 1)
    q = z.numerator // z.denominator
    fr = z - q
    if fr > F(1, 2) or (fr == F(1, 2) and q % 2 == 1):
        q += 1
    enc = (E - 1) * half + q
    return limit if enc >= limit else enc


def denote(s, general):
    """None for no number; ('nan',), ('inf', neg), or ('num', neg, value) with saturation."""
    if not general:
        if not JSON.fullmatch(s):
            return None
    elif not (DEC.fullmatch(s) or HEX.fullmatch(s) or INF.fullmatch(s) or NAN.fullmatch(s)):
        return None
    neg = s.startswith('-')
    t = s[1:] if s[:1] in '+-' else s
    if NAN.fullmatch(t):
        return ('nan',)
    if INF.fullmatch(t):
        return ('inf', neg)
    if t[:2].lower() == '0x':
        mant, exp = re.split('[pP]', t[2:])
        ip, _, fp = mant.partition('.')
        d = int(ip + fp, 16) if ip + fp else 0
        e = int(exp) - 4 * len(fp)
        if d == 0:
            return ('num', neg, F(0))
        if e > 2000:
            return ('big', neg)
        if e < -2000 - 4 * len(ip + fp):
            return ('tiny', neg)
        return ('num', neg, F(d) * F(2) ** e)
    m = re.fullmatch(r'([0-9]*)(?:\.([0-9]*))?(?:[eE]([+-]?[0-9]+))?', t)
    ip, fp, exp = m.group(1), m.group(2) or '', m.group(3) or '0'
    d = int(ip + fp) if ip + fp else 0
    e = int(exp) - len(fp)
    if d == 0:
        return ('num', neg, F(0))
    nd = len(str(d))
    if e + nd > 400:
        return ('big', neg)
    if e + nd < -400:
        return ('tiny', neg)
    return ('num', neg, F(d) * F(10) ** e)


def expected(s, general, bits):
    r = denote(s, general)
    if r is None:
        return (0, 0)
    p, Fe, nu = FMT[bits]
    sign = 1 << (bits - 1)
    inf = Fe << (p - 1)
    if r[0] == 'nan':
        return (1, 0x7FF8000000000000 if bits == 64 else 0x7FC00000)
    neg = r[1]
    if r[0] == 'inf' or r[0] == 'big':
        w = inf
    elif r[0] == 'tiny':
        w = 0
    else:
        w = round_fmt(r[2], bits)
    return (1, (sign | w) if neg else w)


def line(s, general):
    ok64, w64 = expected(s, general, 64)
    ok32, w32 = expected(s, general, 32)
    assert ok64 == ok32
    return f"{'g' if general else 'j'} {ok64} {w64:016X} {ok32} {w32:08X} {s.encode().hex()}"


def tao_cases(data_dir):
    pat = re.compile(r'^([0-9A-F]{4}) ([0-9A-F]{8}) ([0-9A-F]{16}) (\S.*)$')
    out = []
    for name in sorted(os.listdir(data_dir)):
        rows = []
        with open(os.path.join(data_dir, name)) as f:
            for row in f:
                m = pat.match(row.rstrip('\n'))
                rows.append((int(m.group(2), 16), int(m.group(3), 16), m.group(4)))
        pick = set(range(min(3, len(rows))))
        pick |= {i * len(rows) // 12 for i in range(12)}
        pick |= set(sorted(range(len(rows)), key=lambda i: -len(rows[i][2]))[:3])
        for test, count in ((lambda w: (w >> 52) & 0x7FF == 0 and w & 0x7FFFFFFFFFFFFFFF, 3),
                            (lambda w: w & 0x7FFFFFFFFFFFFFFF == 0x7FF0000000000000, 2),
                            (lambda w: w & 0x7FFFFFFFFFFFFFFF == 0, 2)):
            found = [i for i, r in enumerate(rows) if test(r[1])][:count]
            pick |= set(found)
        for i in sorted(pick):
            f32, f64, s = rows[i]
            general = not JSON.fullmatch(s)
            l = line(s, True)
            ok64, w64, ok32, w32 = l.split()[1:5]
            assert int(w64, 16) == f64 and int(w32, 16) == f32, (name, s)
            out.append(l)
            if not general:
                out.append(line(s, False))
    return out


def paxson_cases(path):
    out = []
    for row in open(path):
        parts = row.split()
        if len(parts) == 4 and parts[1] == '%b' and 'p' not in parts[2]:
            out.append(line(parts[2], True))
    return out


def word_value(w, bits):
    p, Fe, nu = FMT[bits]
    e = w >> (p - 1)
    f = w & ((1 << (p - 1)) - 1)
    m = f if e == 0 else (1 << (p - 1)) + f
    return F(m) * F(2) ** (max(e, 1) - 1 - nu)


def decimal_of(x):
    """The exact decimal digits and exponent of a dyadic rational x > 0."""
    k = 0
    while x.denominator != 1:
        x *= 10
        k += 1
    return str(x.numerator), -k


def midpoint_cases(rnd, bits, count):
    out = []
    p, Fe, nu = FMT[bits]
    limit = Fe << (p - 1)
    for _ in range(count):
        w = rnd.choice([rnd.randrange(1, limit - 1), rnd.randrange(1, 1 << p),
                        rnd.randrange(limit - (1 << (p + 3)), limit - 1)])
        mid = (word_value(w, bits) + word_value(w + 1, bits)) / 2
        ds, e = decimal_of(mid)
        for s in (f"{ds}e{e}", f"{int(ds) + 1}e{e}", f"{int(ds) - 1}e{e}",
                  f"{ds}{'0' * 40}1e{e - 41}", f"{int(ds) - 1}{'9' * 50}e{e - 50}"):
            out.append(line(s, True))
    return out


GRAMMAR = [
    '', '-', '+', '.', 'e', '1e', '1e+', '1e-', '-.e1', '01', '00', '-01', '+1', '1.', '.5', '-.5',
    '1.5', '1.5e3', '1.5E-3', '1e+3', '0', '-0', '-0.0e5', '0.000', '1 ', ' 1', '1_000', '1,5',
    '0x10', '0x1p3', '0X1.8P+3', '0x.8p1', '0x1.p0', '0x', '0xp1', '0x1.8', '-0x1p-1074', '0x1p-1075',
    '0x1p1024', '0x1.fffffffffffff8p1023', '0x1.FFFFFFFFFFFFF7FFFp1023', 'inf', 'INF', '-Inf',
    '+infinity', 'Infinity', 'infinit', 'infinityy', 'nan', 'NaN', '-nan', '+NAN', 'nan(1)', 'snan',
    '1e99999999999999999999', '1e-99999999999999999999', '-1e400', '1e-400', '-1e-400',
    '0e99999999999999999999', '2.2250738585072011e-308', '2.2250738585072012e-308',
    '4.9406564584124654e-324', '2.4703282292062327e-324', '2.4703282292062328e-324',
    '1.7976931348623157e308', '1.7976931348623158e308', '1.7976931348623159e308',
    '3.4028234663852886e38', '3.4028235677973366e38', '1.401298464324817e-45', '7.006492321624085e-46',
    '7.006492321624086e-46', '9007199254740993', '9007199254740992.5', '1e23', '8.589973e9',
    '123456789012345678901234567890', '0.1', '0.2', '0.3', '1e-7', '1e22', '1e-22', '1e308',
    '1' + '0' * 400, '0.' + '0' * 400 + '1', '1.' + '0' * 1200 + '1',
]


def grammar_cases():
    out = []
    for s in GRAMMAR:
        out.append(line(s, True))
        out.append(line(s, False))
    return out


def main():
    data_dir, testfp, output = sys.argv[1:4]
    rnd = random.Random(20261012)
    lines = tao_cases(data_dir) + paxson_cases(testfp) + midpoint_cases(rnd, 64, 40) + \
        midpoint_cases(rnd, 32, 20) + grammar_cases()
    seen = set()
    unique = [l for l in lines if not (l in seen or seen.add(l))]
    with open(output, 'w') as f:
        f.write('\n'.join(unique) + '\n')
    print(len(unique), 'cases')


if __name__ == '__main__':
    main()
