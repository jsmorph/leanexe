# Python models of PolyBound's magBound and lowBound and of F64Horner's hornerErr, in exact rationals.
from fractions import Fraction as F
import struct
uQ = F(1, 2**53); etaQ = F(1, 2**1075)
def wordval(w):
    s = w >> 63; e = (w >> 52) & 0x7ff; f = w & ((1 << 52) - 1)
    m = f if e == 0 else (1 << 52) + f
    sh = (e - 1075) if e else -1074
    v = F(m) * (F(2) ** sh)
    return -v if s else v
def shift(c, p):
    # coefficients of p(c + h) in h
    n = len(p); q = list(p)
    for i in range(n):
        for j in range(n - 2, i - 1, -1):
            q[j] = q[j] + c * q[j + 1]
    return q
def absSum(R, p): return sum(abs(a) * R**k for k, a in enumerate(p))
def magBound(p, lo, hi): return absSum((hi - lo) / 2, shift((lo + hi) / 2, p))
def lowBound(p, lo, hi):
    q = shift((lo + hi) / 2, p)
    if not q: return F(0)
    r = (hi - lo) / 2
    return q[0] - r * absSum(r, q[1:])
def absMax(lo, hi): return max(abs(lo), abs(hi))
def hornerErr(cs, lo, hi):
    if len(cs) <= 1: return F(0)
    b = cs[1:]
    e1 = hornerErr(b, lo, hi); M1 = magBound(b, lo, hi); S = absMax(lo, hi)
    ep = S * e1 + uQ * (S * (M1 + e1)) + etaQ
    return ep + uQ * (magBound(cs, lo, hi) + ep)
def deriv(p): return [k * p[k] for k in range(1, len(p))]
def mul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q): r[i + j] += a * b
    return r
def sub(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)]
def ev(p, x):
    r = F(0)
    for a in reversed(p): r = a + x * r
    return r
