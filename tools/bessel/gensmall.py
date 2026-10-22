# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Generate the piecewise error chains of the Bessel functions below 2.

Usage: uv run tools/bessel/gensmall.py j0|j1|y0|y1 OUTPUT

The program models each step of `F64Approx` (`fapprox_mul`, `fapprox_div`, `fapprox_add_half`)
in exact rationals, rounds every error up to a multiple of `u/1000` with `u = 2^-53`, and writes
the Lean proof that repeats the steps; `norm_num` and the kernel check every number.
"""
import math, os, re, sys
from fractions import Fraction as F

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
U = F(1, 2**53)
ETA = F(1, 2**1075)

def wordval(w):
    s = w >> 63; e = (w >> 52) & 0x7ff; f = w & ((1 << 52) - 1)
    m = f if e == 0 else (1 << 52) + f
    v = F(m) * F(2) ** ((e - 1075) if e else -1074)
    return -v if s else v

# PolyBound and F64Horner models
def shift(c, p):
    q = list(p)
    for i in range(len(q)):
        for j in range(len(q) - 2, i - 1, -1):
            q[j] = q[j] + c * q[j + 1]
    return q
def absSum(R, p): return sum(abs(a) * R**k for k, a in enumerate(p))
def magBound(p, lo, hi): return absSum((hi - lo) / 2, shift((lo + hi) / 2, p))
def lowBound(p, lo, hi):
    q = shift((lo + hi) / 2, p); r = (hi - lo) / 2
    return q[0] - r * absSum(r, q[1:])
def hornerErr(cs, lo, hi):
    if len(cs) <= 1: return F(0)
    b = cs[1:]
    e1 = hornerErr(b, lo, hi); M1 = magBound(b, lo, hi); S = max(abs(lo), abs(hi))
    ep = S * e1 + U * (S * (M1 + e1)) + ETA
    return ep + U * (magBound(cs, lo, hi) + ep)
def deriv(p): return [k * p[k] for k in range(1, len(p))]

def up(q, d=1000):
    """The least multiple of 1/d at least q."""
    return F(math.ceil(q * d), d)
def down(q, d=10**6):
    """The greatest multiple of 1/d at most q."""
    return F(math.floor(q * d), d)
def qs(q):
    q = F(q)
    return '(%d : ℝ)' % q.numerator if q.denominator == 1 else '(%d / %d : ℝ)' % (q.numerator, q.denominator)
def qq(q):
    q = F(q)
    return '(%d : ℚ)' % q.numerator if q.denominator == 1 else '(%d / %d : ℚ)' % (q.numerator, q.denominator)
def eu(q):
    """An error in units of u, as Lean text."""
    return '%s * 𝐮' % qs(q)

# Error forms of the F64Approx lemmas, with errors and bounds as rationals
def mulE(ea, eb, Ma, Mb): return ea * Mb + Ma * eb + ea * eb + (Ma + ea) * (Mb + eb) * U + ETA
def divE(ea, eb, Ma, mb): return (ea + Ma * eb / mb) / (mb - eb) + (Ma + ea) / (mb - eb) * U + ETA

def table(name):
    src = open(os.path.join(ROOT, 'Verified', 'Examples', 'Bessel.lean')).read()
    return [int(m, 16) for m in re.findall(r'0x[0-9A-Fa-f]{16}', src.split('def ' + name)[1].split(']')[0])]

R1W = [0xBFB0000000000000, 0x3F570D9F98472C61, 0xBEF0C5C6BA169668, 0x3E6AAAFA46CA0BD9]
S1W = [0x3F939D0B12637E53, 0x3F285F56B9CDF664, 0x3EB3BFF8333F8498, 0x3E35AC88C97DFF2C, 0x3DAB2ACFCFB97ED8]
R1 = [wordval(w) for w in R1W]
S1 = [F(1)] + [wordval(w) for w in S1W]

R0W = [0x3F8FFFFFFFFFFFFD, 0xBF28E6A5B61AC6E9, 0x3EBEB1D10C503919, 0xBE33D5E773D63FCE]
S0W = [0x3F8FFCE882C8C2A4, 0x3F1EA6D2DD57DBF4, 0x3EA13B54CE84D5A9, 0x3E1408BCF4745D8F]
R0 = [wordval(w) for w in R0W]
S0 = [F(1)] + [wordval(w) for w in S0W]

def horner_data(P, Q, lo, hi, ez):
    """Rounded Horner facts of `P` and `Q` on `[lo, hi]` and the errors at a computed `z`."""
    d = dict(eRh=up(hornerErr(P, lo, hi) / U * 1000) / 1000 * U, LR=up(magBound(deriv(P), lo, hi), 10**6),
             MH=up(magBound(P, lo, hi), 10**6), eSh=up(hornerErr(Q, lo, hi) / U * 1000) / 1000 * U,
             LS=up(magBound(deriv(Q), lo, hi), 10**6), mS=down(lowBound(Q, lo, hi)))
    d['eH'] = up((d['eRh'] + d['LR'] * ez) / U) * U
    d['eS'] = up((d['eSh'] + d['LS'] * ez) / U) * U
    return d

def j0_pieces():
    return [(F(1), F(5, 4)), (F(5, 4), F(3, 2)), (F(3, 2), F(7, 4)), (F(7, 4), F(15, 8)), (F(15, 8), F(2))]

def j0_piece(k, a, b):
    """The chain of `(1 + x/2)(1 - x/2) + z (z R(z) / S(z))` with `z = x x` for `a ≤ x ≤ b`."""
    ez = b * b * U + ETA
    lo = a * a * (1 - F(1, 2**50)); hi = b * b * (1 + F(1, 2**50))
    d = dict(k=k, a=a, b=b, lo=lo, hi=hi, ez=ez)
    d.update(horner_data(R0, S0, lo, hi, ez))
    Mz = b * b
    er = up(mulE(ez, d['eH'], Mz, d['MH']) / U) * U; Mr = Mz * d['MH']
    eq = up(divE(er, d['eS'], Mr, d['mS']) / U) * U; Mq = up(Mr / d['mS'], 10**6)
    em = up(mulE(ez, eq, Mz, Mq) / U) * U; Mm = up(Mz * Mq, 10**6)
    Ma = 1 + b / 2; Mb = 1 - a / 2
    ep = up(mulE(U, 0, Ma, Mb) / U) * U
    Mp = 1 - a * a / 4
    tot = Mp + Mm + ep + em
    G = F(2)
    while tot < G / 2: G /= 2
    assert tot < G and G <= 2
    g = 1021 + int(math.log2(G))
    eres = up((ep + em + G * U / 2) / U) * U
    d.update(Mz=Mz, er=er, Mr=Mr, eq=eq, Mq=Mq, em=em, Mm=Mm, Ma=Ma, Mb=Mb, ep=ep, Mp=Mp, G=G, g=g,
             eres=eres)
    return d

U0W = [0xBFB2E4D699CBD01F, 0x3FC69D019DE9E3FC, 0xBF8C4CE8B16CFA97, 0x3F36C54D20B29B6B,
       0xBECFFEA773D25CAD, 0x3E5500573B4EABD4, 0xBDC5E43D693FB3C8]
V0W = [0x3F8A127091C9C71A, 0x3F13ECBBF578C6C1, 0x3E91642D7FF202FD, 0x3DFE50183BD6D9EF]
U0 = [wordval(w) for w in U0W]
V0 = [F(1)] + [wordval(w) for w in V0W]
TPI_E = F(36, 100) * U      # BesselCombine.tpi_near
TPI_M = F(6367, 10000)      # tpi_le
EJ0 = F(235, 100) * U       # BesselJ0Small.j0_small
LM = F(6932, 10000)         # |ln x| for 1/2 ≤ x ≤ 2

def y0_pieces():
    return [(F(1, 2), F(1), F(1)), (F(1), F(5, 4), F(827, 1000)), (F(5, 4), F(3, 2), F(768, 1000)),
            (F(3, 2), F(13, 8), F(5122, 10000)), (F(13, 8), F(7, 4), F(4415, 10000)),
            (F(7, 4), F(15, 8), F(3694, 10000)), (F(15, 8), F(2), F(2967, 10000))]

def uv_data(d, lo, hi, ez):
    """`U0(ẑ)/V0(ẑ)` on `[lo, hi]`."""
    d.update(horner_data(U0, V0, lo, hi, ez))
    d['euv'] = up(divE(d['eH'], d['eS'], d['MH'], d['mS']) / U) * U
    d['Muv'] = up(d['MH'] / d['mS'], 10**6)

def y0_piece(k, a, b, Jm):
    """`U(z)/V(z) + tpi (ĵ L̂)` for `a ≤ x ≤ b`, with `ĵ` within `EJ0` of `J₀` and `|J₀| ≤ Jm`."""
    ez = b * b * U + ETA
    lo = a * a * (1 - F(1, 2**50)); hi = b * b * (1 + F(1, 2**50))
    d = dict(k=k, a=a, b=b, lo=lo, hi=hi, ez=ez, Jm=Jm, Lm=LM)
    uv_data(d, lo, hi, ez)
    eLc = F(6, 5) * LM
    eL = eLc * U + F(1, 2**59)
    ep = up(mulE(EJ0, eL, Jm, LM) / U) * U; Mp = up(Jm * LM, 10**6)
    et = up(mulE(TPI_E, ep, TPI_M, Mp) / U) * U; Mt = up(TPI_M * Mp, 10**6)
    B = up(d['Muv'] + Mt + d['euv'] + et, 10**6)
    eres = up((d['euv'] + et + B * U) / U) * U
    d.update(eLc=eLc, ep=ep, Mp=Mp, et=et, Mt=Mt, B=B, eres=eres)
    return d

def aff_mulE(ea, eb, Ma, Mb):
    """`mulE` for errors and bounds `(A, B)` meaning `A ℓ + B`, at most one of each pair affine."""
    def mul(p, q):
        assert p[0] == 0 or q[0] == 0
        return (p[0] * q[1] + p[1] * q[0], p[1] * q[1])
    def add(*ps): return (sum(p[0] for p in ps), sum(p[1] for p in ps))
    Ba = add(Ma, ea); Bb = add(Mb, eb)
    r = add(mul(ea, Mb), mul(Ma, eb), mul(ea, eb), mul(mul(Ba, Bb), (0, U)), (0, ETA))
    return r

def y0_log():
    """The main path for `2^-27 ≤ x ≤ 1/2` with `ℓ = |ln x|`, errors as `α u ℓ + β u`."""
    a = F(1, 2**27); b = F(1, 2)
    ez = b * b * U + ETA
    lo = F(-1, 2**50); hi = b * b * (1 + F(1, 2**50))
    d = dict(k='log', a=a, b=b, lo=lo, hi=hi, ez=ez)
    uv_data(d, lo, hi, ez)
    eL = (F(6, 5) * U, F(1, 2**59))
    p = aff_mulE((0, EJ0), eL, (0, F(1)), (F(1), 0))
    ap, bp = up(p[0] / U), up(p[1] / U)
    t = aff_mulE((0, TPI_E), (ap * U, bp * U), (0, TPI_M), (F(1), 0))
    at, bt = up(t[0] / U), up(t[1] / U)
    # fapprox_add with B = Muv + TPI_M ℓ + euv + et
    Bq = (TPI_M + at * U, d['Muv'] + d['euv'] + bt * U)
    r = (at * U + Bq[0] * U, d['euv'] + bt * U + Bq[1] * U)
    ar, br = up(r[0] / U), up(r[1] / U)
    d.update(ap=ap, bp=bp, at=at, bt=bt, ar=ar, br=br)
    return d

def j1_pieces():
    return [(F(1, 2**27), F(1)), (F(1), F(5, 4)), (F(5, 4), F(3, 2)), (F(3, 2), F(7, 4)), (F(7, 4), F(2))]

def j1_piece(k, a, b):
    """The chain of `x * 0.5 + x x R(x x) x / S(x x)` for `a ≤ |x| ≤ b`."""
    ez = b * b * U + ETA                      # sq_near with M = b
    lo = F(-1, 2**50) if a < F(1, 2**10) else a * a * (1 - F(1, 2**50))
    hi = b * b * (1 + F(1, 2**50))
    eRh = up(hornerErr(R1, lo, hi) / U * 1000) / 1000 * U
    LR = up(magBound(deriv(R1), lo, hi), 10**6)
    MH = up(magBound(R1, lo, hi), 10**6)
    eSh = up(hornerErr(S1, lo, hi) / U * 1000) / 1000 * U
    LS = up(magBound(deriv(S1), lo, hi), 10**6)
    mS = F(math.floor(lowBound(S1, lo, hi) * 10**6), 10**6)
    eH = up((eRh + LR * ez) / U) * U
    eS = up((eSh + LS * ez) / U) * U
    Mz = b * b
    er = up(mulE(ez, eH, Mz, MH) / U) * U; Mr = Mz * MH
    erx = up(mulE(er, 0, Mr, b) / U) * U; Mrx = Mr * b
    eq = up(divE(erx, eS, Mrx, mS) / U) * U; Mq = Mrx / mS
    Mh = b / 2
    tot = Mh + Mq + eq
    assert tot < 2
    eres = up((eq + U) / U) * U
    return dict(k=k, a=a, b=b, lo=lo, hi=hi, eRh=eRh, LR=LR, MH=MH, eSh=eSh, LS=LS, mS=mS, ez=ez,
                eH=eH, eS=eS, Mz=Mz, er=er, Mr=Mr, erx=erx, Mrx=Mrx, eq=eq, Mq=Mq, eres=eres)

def facts_text(name, P, Q, d):
    return '''
theorem %(name)s : hornerOK %(P)s %(loq)s %(hiq)s = true ∧ hornerOK %(Q)s %(loq)s %(hiq)s = true ∧
    hornerErr %(P)s %(loq)s %(hiq)s ≤ %(eRhq)s ∧ magBound (derivP %(P)s) %(loq)s %(hiq)s ≤ %(LRq)s ∧
    magBound %(P)s %(loq)s %(hiq)s ≤ %(MHq)s ∧ hornerErr %(Q)s %(loq)s %(hiq)s ≤ %(eShq)s ∧
    magBound (derivP %(Q)s) %(loq)s %(hiq)s ≤ %(LSq)s ∧ %(mSq)s ≤ lowBound %(Q)s %(loq)s %(hiq)s := by
  decide +kernel
''' % dict(d, name=name, P=P, Q=Q)

def horner_steps(P, Q, pw, qw, z, d):
    '''The Lean steps from the facts to `hH`, `hS'`, `hHm`, and `hSm`.'''
    return '''  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP %(P)s) %(loq)s %(hiq)s := (abs_nonneg _).trans
    (magBound_sound _ %(loq)s %(hiq)s z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP %(Q)s) %(loq)s %(hiq)s := (abs_nonneg _).trans
    (magBound_sound _ %(loq)s %(hiq)s z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (%(pw)s.map Float.ofBits) (%(zf)s)) (eval %(P)s z) (%(eHu)s) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: %(qw)s.map Float.ofBits) (%(zf)s)) (eval %(Q)s z) (%(eSu)s) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval %(P)s z| ≤ %(MHr)s := (magBound_sound %(P)s %(loq)s %(hiq)s z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : %(mSr)s ≤ |eval %(Q)s z| := by
    have := (lowBound_sound %(Q)s %(loq)s %(hiq)s z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
''' % dict(d, P=P, Q=Q, pw=pw, qw=qw, zf=z)

def fmt(p, reals=(), rats=(), errs=()):
    d = dict(p)
    for key in reals: d[key + 'r'] = qs(p[key])
    for key in rats: d[key + 'q'] = qq(p[key])
    for key in errs: d[key + 'u'] = eu(p[key] / U)
    return d

def lean_j0(pieces):
    out = ['''import Library.Numerics.Float64.Bessel.BesselSmallJ0

/-!
The second form of `Bessel.j0`, `(1 + x/2)(1 - x/2) + z (z R(z)/S(z))` with `z = x x`, which the
code takes for `1 ≤ |x| < 2`.  Each lemma `form2_k` follows it through `F64Approx` on one range of
`|x|`, with the Horner bounds that the kernel checks on that range (`facts2_k`), the exact `x/2` of
`BesselSmallEval.half_exact`, and the exact `1 - x/2` of Sterbenz's lemma; this file is generated
by `tools/bessel/gensmall.py`.
-/

namespace Library.Numerics.Float64.Bessel.BesselSmallJ0Form2
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS BesselSmallEval BesselSmallApprox BesselJ0Large BesselSmallJ0
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048
''']
    for p in pieces:
        d = fmt(p, reals=('a', 'b', 'Mz', 'MH', 'Mr', 'Mq', 'Mm', 'mS', 'Ma', 'Mb', 'Mp', 'G'),
                rats=('lo', 'hi', 'LR', 'LS', 'MH', 'mS', 'eRh', 'eSh'),
                errs=('eH', 'eS', 'er', 'eq', 'em', 'ep', 'eres'))
        out.append(facts_text('facts2_%d' % p['k'], 'R0', 'S0', d))
        out.append('''
/-- The second form of `j0` for `%(a)s ≤ x ≤ %(b)s`. -/
theorem form2_%(k)d (xa : Float) (hf : Finite xa.toBits) (hs : Wasm.IEEE64.sign xa.toBits = false)
    (he : 2 ≤ Wasm.IEEE64.exponent xa.toBits) (v : ℝ) (hv : value xa.toBits = v) (ha : %(ar)s ≤ v)
    (hb : v ≤ %(br)s) (hlt : v < 2) :
    FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0) + xa * xa * (xa * xa *
        hornerF (r0w.map Float.ofBits) (xa * xa) / hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)))
      (1 - v ^ 2 / 4 + v ^ 2 * (v ^ 2 * eval R0 (v ^ 2)) / eval S0 (v ^ 2)) (%(eresu)s) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts2_%(k)d
  subst hv
  set v := value xa.toBits
  have hz := sq_near xa hf %(br)s (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : %(ar)s ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ %(br)s ^ 2 := by nlinarith
  have hzm : |z| ≤ %(Mzr)s := by
    rw [abs_of_nonneg (by rw [hzd]; positivity)]; norm_num at hzb ⊢; linarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := rs_at (xa * xa) hz.1 z _ %(loq)s %(hiq)s k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
''' % d)
        out.append(horner_steps('R0', 'S0', 'r0w', 's0w', 'xa * xa', d))
        out.append('''  have hr := fapprox_mul hz hH %(Mzr)s %(MHr)s hzm hHm _ le_rfl (by rw [hu]; norm_num)
  have hr' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa)) (z * eval R0 z) (%(eru)s) :=
    fmono hr (by rw [hu]; norm_num)
  have hrm : |z * eval R0 z| ≤ %(Mrr)s := by
    rw [abs_mul]; exact (mul_le_mul hzm hHm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hq := fapprox_div hr' hS' %(Mrr)s %(mSr)s hrm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (z * eval R0 z / eval S0 z) (%(equ)s) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |z * eval R0 z / eval S0 z| ≤ %(Mqr)s := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hrm (by norm_num) hSm).trans (by norm_num)
  have hm := fapprox_mul hz hq' %(Mzr)s %(Mqr)s hzm hqm _ le_rfl (by rw [hu]; norm_num)
  have hm' : FApprox (xa * xa * (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa))) (z * (z * eval R0 z / eval S0 z)) (%(emu)s) :=
    fmono hm (by rw [hu]; norm_num)
  have hmm : |z * (z * eval R0 z / eval S0 z)| ≤ %(Mmr)s := by
    rw [abs_mul]; exact (mul_le_mul hzm hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  obtain ⟨hwf, hwv⟩ := half_exact xa hf hs he (by linarith)
  have hw : FApprox (xa / 2.0) (v / 2) 0 := ⟨hwf, by rw [hwv]; show |v / 2 - v / 2| ≤ 0; simp⟩
  have hp1 := fapprox_add_half fapprox_one hw 1022 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
    rw [e, abs_of_pos (by linarith)]
    linarith)
  have hp1' : FApprox (1.0 + xa / 2.0) (1 + v / 2) 𝐮 := fmono hp1 (by rw [hu]; norm_num)
  have hone := fapprox_one
  have hm1 : FApprox (1.0 - xa / 2.0) (1 - v / 2) 0 := by
    have hs1 := F64Exact.sub_exact (1.0 : Float).toBits (xa / 2.0).toBits hone.1 hwf
      (by rw [one_bits, value_one]; norm_num) (by rw [hwv]; linarith)
      (by rw [hwv, one_bits, value_one]; linarith) (by rw [hwv, one_bits, value_one]; linarith)
      (by rw [one_bits, value_one]; norm_num) (by rw [hwv]; linarith)
    unfold FApprox Approx
    rw [F64Bits.toBits_sub]
    refine ⟨hs1.1, ?_⟩
    rw [hs1.2, hwv, one_bits, value_one]
    show |1 - v / 2 - (1 - v / 2)| ≤ 0
    simp
  have hp := fapprox_mul hp1' hm1 %(Mar)s %(Mbr)s (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0)) ((1 + v / 2) * (1 - v / 2)) (%(epu)s) :=
    fmono hp (by rw [hu]; norm_num)
  have hpm : |(1 + v / 2) * (1 - v / 2)| ≤ %(Mpr)s := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hres := fapprox_add_half hp' hm' %(g)d (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + %(g)d) / 2 ^ 1074 = %(Gr)s := by norm_num
    rw [e]
    have h1 := abs_add_le ((1 + v / 2) * (1 - v / 2)) (z * (z * eval R0 z / eval S0 z))
    have h2 : %(epu)s + %(emu)s < %(Gr)s - (%(Mpr)s + %(Mmr)s) := by rw [hu]; norm_num
    linarith)
  refine fmono (fcongr hres ?_) (by rw [hu]; norm_num)
  have : eval S0 z ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hSm; norm_num at hSm
  field_simp
  ring
''' % d)
    return ''.join(out)

def lean_y0(pieces, lg):
    out = ['''import Library.Numerics.Float64.Bessel.BesselSmallJ0

/-!
The main path of `Bessel.y0` below 2, `U(z)/V(z) + tpi (ĵ L̂)` with `z = x x`, for doubles `ĵ` and
`L̂` within given errors of `J₀(x)` and `ln x`.  Each lemma `piece_k` follows it through
`F64Approx` on one range of `x` from 1/2 to 2, with the Horner bounds that the kernel checks on
that range (`facts_k`) and `|J₀| ≤ Jm`, `|ln x| ≤ 0.6932`; `log_piece` covers `2^-27 ≤ x ≤ 1/2`
with the error as an affine function of `ℓ = |ln x|`.  This file is generated by
`tools/bessel/gensmall.py`.
-/

namespace Library.Numerics.Float64.Bessel.BesselSmallY0
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS BesselSmallEval BesselSmallApprox BesselJ0Large BesselSmallJ0
  BesselCombine Real
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

def u0w : List UInt64 := [%s]
def v0w : List UInt64 := [%s]

theorem words : (∀ w ∈ u0w, Finite w) ∧ (∀ w ∈ v0w, Finite w) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem lists : u0w.map ratOfWord = U0 ∧ 1 :: v0w.map ratOfWord = V0 := ⟨rfl, rfl⟩

theorem uv_at (zf : Float) (hzf : Finite zf.toBits) (z δ : ℝ) (lo hi : ℚ)
    (hR : hornerOK U0 lo hi = true) (hS : hornerOK V0 lo hi = true)
    (h1 : (lo : ℝ) ≤ value zf.toBits) (h2 : value zf.toBits ≤ hi) (h3 : (lo : ℝ) ≤ z)
    (h4 : z ≤ hi) (hδ : |value zf.toBits - z| ≤ δ) :
    FApprox (hornerF (u0w.map Float.ofBits) zf) (eval U0 z)
        (hornerErr U0 lo hi + magBound (derivP U0) lo hi * δ) ∧
      FApprox (hornerF (1.0 :: v0w.map Float.ofBits) zf) (eval V0 z)
        (hornerErr V0 lo hi + magBound (derivP V0) lo hi * δ) := by
  obtain ⟨wr, ws⟩ := words
  obtain ⟨b1, b2⟩ := words_rel u0w wr
  obtain ⟨c1, c2⟩ := words_rel_one v0w ws
  exact ⟨horner_at _ _ U0 b1 b2 (by decide) lo hi hR zf hzf z δ h1 h2 h3 h4 hδ,
    horner_at _ _ V0 c1 c2 (by decide) lo hi hS zf hzf z δ h1 h2 h3 h4 hδ⟩

theorem tpi_le : |2 / π| ≤ 6367 / 10000 := by
  rw [abs_of_pos (by positivity), div_le_iff₀ Real.pi_pos]
  have := pi_bounds.1
  linarith
''' % (', '.join('0x%016X' % w for w in U0W), ', '.join('0x%016X' % w for w in V0W))]
    for p in pieces + [lg]:
        d = fmt(p, rats=('lo', 'hi', 'LR', 'LS', 'MH', 'mS', 'eRh', 'eSh'))
        out.append(facts_text('facts_%s' % p['k'], 'U0', 'V0', d))
    head = '''  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_%(k)s
  subst hv
  set v := value x.toBits
  have hz := sq_near x hf %(br)s (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : %(ar)s ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ %(br)s ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ %(loq)s %(hiq)s k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
'''
    uvq = '''  have hq := fapprox_div hH hS' %(MHr)s %(mSr)s hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u0w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v0w.map Float.ofBits) (x * x)) (eval U0 z / eval V0 z) (%(euvu)s) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U0 z / eval V0 z| ≤ %(Muvr)s := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
'''
    for p in pieces:
        d = fmt(p, reals=('a', 'b', 'MH', 'mS', 'Muv', 'Jm', 'Lm', 'Mp', 'Mt', 'B', 'eLc'),
                rats=('lo', 'hi', 'LR', 'LS', 'MH', 'mS', 'eRh', 'eSh'),
                errs=('eH', 'eS', 'euv', 'ep', 'et', 'eres'))
        d['k'] = str(p['k'])
        out.append('''
/-- The main path of `y0` for `%(a)s ≤ x ≤ %(b)s`. -/
theorem piece_%(k)s (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : %(ar)s ≤ v) (hb : v ≤ %(br)s) (hJ : FApprox J (J0 v) (235 / 100 * 𝐮))
    (hJm : |J0 v| ≤ %(Jmr)s) (hL : FApprox L (Real.log v) (%(eLcr)s * 𝐮 + 1 / 2 ^ 59))
    (hLm : |Real.log v| ≤ %(Lmr)s) :
    FApprox (hornerF (u0w.map Float.ofBits) (x * x) / hornerF (1.0 :: v0w.map Float.ofBits) (x * x) +
        Bessel.tpi * (J * L))
      (eval U0 (v ^ 2) / eval V0 (v ^ 2) + 2 / π * (J0 v * Real.log v)) (%(eresu)s) := by
''' % d)
        out.append(head % d)
        out.append(horner_steps('U0', 'V0', 'u0w', 'v0w', 'x * x', d))
        out.append(uvq % d)
        out.append('''  have hp := fapprox_mul hJ hL %(Jmr)s %(Lmr)s hJm hLm _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox (J * L) (J0 v * Real.log v) (%(epu)s) := fmono hp (by rw [hu]; norm_num)
  have hpm : |J0 v * Real.log v| ≤ %(Mpr)s := by
    rw [abs_mul]; exact (mul_le_mul hJm hLm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have ht := fapprox_mul tpi_near hp' (6367 / 10000) %(Mpr)s tpi_le hpm _ le_rfl
    (by rw [hu]; norm_num)
  have ht' : FApprox (Bessel.tpi * (J * L)) (2 / π * (J0 v * Real.log v)) (%(etu)s) :=
    fmono ht (by rw [hu]; norm_num)
  have htm : |2 / π * (J0 v * Real.log v)| ≤ %(Mtr)s := by
    rw [abs_mul]; exact (mul_le_mul tpi_le hpm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hres := fapprox_add hq' ht' %(Br)s (by
    have h1 := abs_add_le (eval U0 z / eval V0 z) (2 / π * (J0 v * Real.log v))
    have h2 : %(euvu)s + %(etu)s ≤ %(Br)s - (%(Muvr)s + %(Mtr)s) := by rw [hu]; norm_num
    linarith) (by norm_num)
  exact fmono hres (by rw [hu]; norm_num)
''' % d)
    d = fmt(lg, reals=('a', 'b', 'MH', 'mS', 'Muv', 'ap', 'bp', 'at', 'bt'),
            rats=('lo', 'hi', 'LR', 'LS', 'MH', 'mS', 'eRh', 'eSh'), errs=('eH', 'eS', 'euv'))
    d['k'] = 'log'
    d['arr'], d['brr'] = qs(lg['ar']), qs(lg['br'])
    d['ar'], d['br'] = qs(lg['a']), qs(lg['b'])
    out.append('''
/-- The main path of `y0` for `2^-27 ≤ x ≤ 1/2`, with `ℓ = |ln x|`. -/
theorem log_piece (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : %(ar)s ≤ v) (hb : v ≤ %(br)s) (ℓ : ℝ) (hℓ : |Real.log v| = ℓ) (hℓ1 : ℓ ≤ 19)
    (hJ : FApprox J (J0 v) (235 / 100 * 𝐮)) (hJm : |J0 v| ≤ 1)
    (hL : FApprox L (Real.log v) (6 / 5 * 𝐮 * ℓ + 1 / 2 ^ 59)) :
    FApprox (hornerF (u0w.map Float.ofBits) (x * x) / hornerF (1.0 :: v0w.map Float.ofBits) (x * x) +
        Bessel.tpi * (J * L))
      (eval U0 (v ^ 2) / eval V0 (v ^ 2) + 2 / π * (J0 v * Real.log v))
      (%(arr)s * 𝐮 * ℓ + %(brr)s * 𝐮) := by
  have hℓ0 : 0 ≤ ℓ := by rw [← hℓ]; exact abs_nonneg _
''' % d)
    out.append(head % d)
    out.append(horner_steps('U0', 'V0', 'u0w', 'v0w', 'x * x', d))
    out.append(uvq % d)
    out.append('''  have hp := fapprox_mul hJ hL 1 ℓ hJm (le_of_eq hℓ) _ le_rfl (by rw [hu]; nlinarith)
  have hp' : FApprox (J * L) (J0 v * Real.log v) (%(apr)s * 𝐮 * ℓ + %(bpr)s * 𝐮) :=
    fmono hp (by rw [hu]; nlinarith)
  have hpm : |J0 v * Real.log v| ≤ ℓ := by
    rw [abs_mul, hℓ]; nlinarith [abs_nonneg (J0 v)]
  have ht := fapprox_mul tpi_near hp' (6367 / 10000) ℓ tpi_le hpm _ le_rfl (by rw [hu]; nlinarith)
  have ht' : FApprox (Bessel.tpi * (J * L)) (2 / π * (J0 v * Real.log v))
      (%(atr)s * 𝐮 * ℓ + %(btr)s * 𝐮) := fmono ht (by rw [hu]; nlinarith)
  have htm : |2 / π * (J0 v * Real.log v)| ≤ 6367 / 10000 * ℓ := by
    rw [abs_mul]; exact mul_le_mul tpi_le hpm (abs_nonneg _) (by norm_num)
  have hres := fapprox_add hq' ht'
    (%(Muvr)s + 6367 / 10000 * ℓ + (%(euvu)s + (%(atr)s * 𝐮 * ℓ + %(btr)s * 𝐮))) (by
      have h1 := abs_add_le (eval U0 z / eval V0 z) (2 / π * (J0 v * Real.log v))
      linarith) (by rw [hu]; nlinarith)
  exact fmono hres (by rw [hu]; nlinarith)
''' % d)
    return ''.join(out)

def y1_words():
    t = table('j1Table')
    return t[92:97], t[97:102]

def y1_pieces():
    """`(a, b, c, r, ej, Lm)`: the piece, the check of `A₁` on it in `BesselModSmall1`, the error of
    `j1` from `BesselJ1Small.j1Err`, and the bound on `ln x`."""
    return [(F(1), F(9, 8), F(23178, 26795), F(509, 33511), F(174, 100), F(1, 8)),
            (F(9, 8), F(5, 4), F(25193, 30227), F(1296, 78247), F(174, 100), F(1, 4)),
            (F(5, 4), F(3, 2), F(64006, 82011), F(2943, 80320), F(226, 100), F(4432, 10000)),
            (F(3, 2), F(7, 4), F(70216, 99813), F(3938, 97139), F(298, 100), F(5682, 10000)),
            (F(7, 4), F(15, 8), F(46073, 71796), F(33, 1541), F(389, 100), F(6307, 10000)),
            (F(15, 8), F(31, 16), F(17848, 29281), F(39, 3557), F(389, 100), F(662, 1000)),
            (F(31, 16), F(2), F(3431, 5838), F(103, 9299), F(389, 100), F(6932, 10000))]

def y1_piece(k, a, b, c, r, ejr, Lm):
    """`x (U(z)/V(z)) + tpi (ĵ L̂ - 1/x)` for `a ≤ x ≤ b`."""
    UW, VW = y1_words()
    U1 = [wordval(w) for w in UW]; V1 = [F(1)] + [wordval(w) for w in VW]
    ez = b * b * U + ETA
    lo = a * a * (1 - F(1, 2**50)); hi = b * b * (1 + F(1, 2**50))
    d = dict(k=k, a=a, b=b, lo=lo, hi=hi, ez=ez, Lm=Lm, ia=1 / a, ib=1 / b)
    d.update(horner_data(U1, V1, lo, hi, ez))
    d['euv'] = up(divE(d['eH'], d['eS'], d['MH'], d['mS']) / U) * U
    d['Muv'] = up(d['MH'] / d['mS'], 10**6)
    exuv = up(mulE(0, d['euv'], b, d['Muv']) / U) * U; Mxuv = up(b * d['Muv'], 10**6)
    Jm = up(b / 2 * (c + r + F(1, 2**99)), 10**4)
    ej = ejr * U; eLc = F(6, 5) * Lm; eL = eLc * U + F(1, 2**59)
    ep = up(mulE(ej, eL, Jm, Lm) / U) * U; Mp = up(Jm * Lm, 10**6)
    assert Mp - 1 / b <= 1 / a
    einv = up(divE(0, 0, F(1), a) / U) * U
    Md = 1 / a
    ed = up((ep + einv + (Md + ep + einv) * U) / U) * U
    et = up(mulE(TPI_E, ed, TPI_M, Md) / U) * U; Mt = up(TPI_M * Md, 10**6)
    B = up(Mxuv + Mt + exuv + et, 10**6)
    eres = up((exuv + et + B * U) / U) * U
    d.update(exuv=exuv, Mxuv=Mxuv, Jm=Jm, ej=ej, eLc=eLc, ep=ep, Mp=Mp, einv=einv, Md=Md, ed=ed,
             et=et, Mt=Mt, B=B, eres=eres)
    return d

VL = F(3679, 10000)   # x |ln x| ≤ 1/e on (0, 1]
EJ1 = F(14, 10) * U   # BesselJ1Small.j1Err up to 1

def y1_small():
    """The main path for `2^-54 ≤ x ≤ 1`, errors as `α u/x + β u ℓ + γ u` with `ℓ = |ln x|`."""
    UW, VW = y1_words()
    U1 = [wordval(w) for w in UW]; V1 = [F(1)] + [wordval(w) for w in VW]
    b = F(1)
    ez = b * b * U + ETA
    lo = F(-1, 2**50); hi = b * b * (1 + F(1, 2**50))
    d = dict(k='small', a=F(1, 2**54), b=b, lo=lo, hi=hi, ez=ez)
    d.update(horner_data(U1, V1, lo, hi, ez))
    euv = up(divE(d['eH'], d['eS'], d['MH'], d['mS']) / U) * U
    Muv = up(d['MH'] / d['mS'], 10**6)
    d.update(euv=euv, Muv=Muv)
    # x (u/v), with |x| ≤ x ≤ 1
    cx = up((euv + (Muv + euv) * U + ETA) / U)
    # ĵ L̂ with |J₁| ≤ 0.51 x, |ln x| = ℓ, x ℓ ≤ VL
    eLa, eLb = F(6, 5) * U, F(1, 2**59)
    Jc = F(51, 100)
    pa = (EJ1 + EJ1 * eLa + EJ1 * (1 + eLa) * U) / U
    pb = (VL * (Jc * eLa + Jc * (1 + eLa) * U) + Jc * eLb * (1 + U) + EJ1 * eLb * (1 + U) + ETA) / U
    pa, pb = up(pa), up(pb)
    # 1/x within (1001/1000) u/x
    ia = F(1001, 1000)
    # ĵ L̂ - 1/x, with |J₁ ln x - 1/x| ≤ 0.51 + 1/x
    da = up(ia + (1 + ia * U))
    dl = up(pa + pa * U)
    dk = up(pb + F(51, 100) + pb * U)
    # tpi (…), with |…| ≤ 0.51 + 1/x
    te = F(36, 100); tm = TPI_M
    ta = up(te + tm * da + te * U * da + (tm + te * U) * (1 + da * U))
    tl = up(tm * dl + te * U * dl + (tm + te * U) * dl * U)
    tk = up(te * F(51, 100) + tm * dk + te * U * dk + (tm + te * U) * (F(51, 100) + dk * U) + ETA / U)
    # x (u/v) + tpi (…), with B = Muv + tm (0.51 + 1/x) + cx u + et
    ra = up(ta + tm + ta * U)
    rl = up(tl + tl * U)
    rk = up(cx + tk + Muv + tm * F(51, 100) + cx * U + tk * U)
    d.update(cx=cx, pa=pa, pb=pb, ia=ia, da=da, dl=dl, dk=dk, ta=ta, tl=tl, tk=tk, ra=ra, rl=rl, rk=rk)
    return d

def lean_y1(pieces, sm):
    UW, VW = y1_words()
    out = ['''import Library.Numerics.Float64.Bessel.BesselSmallY0

/-!
The main path of `Bessel.y1` below 2, `x (U(z)/V(z)) + tpi (ĵ L̂ - 1/x)` with `z = x x`, for
doubles `ĵ` and `L̂` within given errors of `J₁(x)` and `ln x`.  Each lemma `piece_k` follows it
through `F64Approx` on one range of `x` from 1 to 2, with the Horner bounds that the kernel checks
on that range (`facts_k`), `|J₁| ≤ Jm`, and `|ln x| ≤ Lm`; `small_piece` covers `2^-54 ≤ x ≤ 1`
with the error as `α u/x + β u ℓ + γ u` for `ℓ = |ln x|`, from `|J₁(x)| ≤ 0.51 x` and
`x ℓ ≤ 0.3679`.  `code_eq` reads the coefficients from `Bessel.j1Table`.  This file is generated
by `tools/bessel/gensmall.py`.
-/

namespace Library.Numerics.Float64.Bessel.BesselSmallY1
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS BesselSmallEval BesselSmallApprox BesselJ0Large BesselSmallJ0
  BesselCombine BesselSmallY0 Real
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

def u1w : List UInt64 := [%s]
def v1w : List UInt64 := [%s]

theorem words : (∀ w ∈ u1w, Finite w) ∧ (∀ w ∈ v1w, Finite w) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem lists : u1w.map ratOfWord = U1 ∧ 1 :: v1w.map ratOfWord = V1 := ⟨rfl, rfl⟩

/-- The table entries 92 to 101 of `j1Table` as the Horner forms of `U` and `V`. -/
theorem code_eq (z : Float) :
    Bessel.entry Bessel.j1Table 92 + z * (Bessel.entry Bessel.j1Table 93 +
        z * (Bessel.entry Bessel.j1Table 94 + z * (Bessel.entry Bessel.j1Table 95 +
        z * Bessel.entry Bessel.j1Table 96))) = hornerF (u1w.map Float.ofBits) z ∧
      1.0 + z * (Bessel.entry Bessel.j1Table 97 + z * (Bessel.entry Bessel.j1Table 98 +
        z * (Bessel.entry Bessel.j1Table 99 + z * (Bessel.entry Bessel.j1Table 100 +
        z * Bessel.entry Bessel.j1Table 101)))) = hornerF (1.0 :: v1w.map Float.ofBits) z :=
  ⟨rfl, rfl⟩

theorem uv_at (zf : Float) (hzf : Finite zf.toBits) (z δ : ℝ) (lo hi : ℚ)
    (hR : hornerOK U1 lo hi = true) (hS : hornerOK V1 lo hi = true)
    (h1 : (lo : ℝ) ≤ value zf.toBits) (h2 : value zf.toBits ≤ hi) (h3 : (lo : ℝ) ≤ z)
    (h4 : z ≤ hi) (hδ : |value zf.toBits - z| ≤ δ) :
    FApprox (hornerF (u1w.map Float.ofBits) zf) (eval U1 z)
        (hornerErr U1 lo hi + magBound (derivP U1) lo hi * δ) ∧
      FApprox (hornerF (1.0 :: v1w.map Float.ofBits) zf) (eval V1 z)
        (hornerErr V1 lo hi + magBound (derivP V1) lo hi * δ) := by
  obtain ⟨wr, ws⟩ := words
  obtain ⟨b1, b2⟩ := words_rel u1w wr
  obtain ⟨c1, c2⟩ := words_rel_one v1w ws
  exact ⟨horner_at _ _ U1 b1 b2 (by decide) lo hi hR zf hzf z δ h1 h2 h3 h4 hδ,
    horner_at _ _ V1 c1 c2 (by decide) lo hi hS zf hzf z δ h1 h2 h3 h4 hδ⟩
''' % (', '.join('0x%016X' % w for w in UW), ', '.join('0x%016X' % w for w in VW))]
    for p in pieces + [sm]:
        d = fmt(p, rats=('lo', 'hi', 'LR', 'LS', 'MH', 'mS', 'eRh', 'eSh'))
        out.append(facts_text('facts_%s' % p['k'], 'U1', 'V1', d))
    head = '''  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_%(k)s
  have hx0 : FApprox x (value x.toBits) 0 := fapprox_exact x hf
  subst hv
  set v := value x.toBits
  have hx : FApprox x v 0 := hx0
  have hz := sq_near x hf %(br)s (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : %(ar)s ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ %(br)s ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ %(loq)s %(hiq)s k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
'''
    uvq = '''  have hq := fapprox_div hH hS' %(MHr)s %(mSr)s hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval U1 z / eval V1 z) (%(euvu)s) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U1 z / eval V1 z| ≤ %(Muvr)s := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
'''
    for p in pieces:
        d = fmt(p, reals=('a', 'b', 'MH', 'mS', 'Muv', 'Mxuv', 'Jm', 'Lm', 'Mp', 'Mt', 'B', 'eLc',
                          'ia', 'ib'),
                rats=('lo', 'hi', 'LR', 'LS', 'MH', 'mS', 'eRh', 'eSh'),
                errs=('eH', 'eS', 'euv', 'exuv', 'ej', 'ep', 'einv', 'ed', 'et', 'eres'))
        d['k'] = str(p['k'])
        out.append('''
/-- The main path of `y1` for `%(a)s ≤ x ≤ %(b)s`. -/
theorem piece_%(k)s (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : %(ar)s ≤ v) (hb : v ≤ %(br)s) (hJ : FApprox J (J1 v) (%(eju)s)) (hJm : |J1 v| ≤ %(Jmr)s)
    (hL : FApprox L (Real.log v) (%(eLcr)s * 𝐮 + 1 / 2 ^ 59)) (hLm : |Real.log v| ≤ %(Lmr)s)
    (hp0 : 0 ≤ J1 v * Real.log v) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      (%(eresu)s) := by
''' % d)
        out.append(head % d)
        out.append(horner_steps('U1', 'V1', 'u1w', 'v1w', 'x * x', d))
        out.append(uvq % d)
        out.append('''  have hvb : |v| ≤ %(br)s := by rw [abs_of_nonneg (by linarith)]; exact hb
  have hxq := fapprox_mul hx hq' %(br)s %(Muvr)s hvb hqm _ le_rfl (by rw [hu]; norm_num)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) (%(exuvu)s) :=
    fmono hxq (by rw [hu]; norm_num)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ %(Mxuvr)s := by
    rw [abs_mul]; exact (mul_le_mul hvb hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hp := fapprox_mul hJ hL %(Jmr)s %(Lmr)s hJm hLm _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox (J * L) (J1 v * Real.log v) (%(epu)s) := fmono hp (by rw [hu]; norm_num)
  have hpm : |J1 v * Real.log v| ≤ %(Mpr)s := by
    rw [abs_mul]; exact (mul_le_mul hJm hLm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hinv := fapprox_div fapprox_one hx 1 %(ar)s (by norm_num)
    (by rw [abs_of_pos (by linarith)]; exact ha) (by norm_num) _ le_rfl (by norm_num)
  have hinv' : FApprox (1.0 / x) (1 / v) (%(einvu)s) := fmono hinv (by rw [hu]; norm_num)
  have hiv1 : 1 / v ≤ %(iar)s := by
    have := one_div_le_one_div_of_le (by norm_num) ha
    norm_num at this ⊢; linarith
  have hiv2 : %(ibr)s ≤ 1 / v := by
    have := one_div_le_one_div_of_le (by linarith) hb
    norm_num at this ⊢; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ %(iar)s := by
    have h1 := (abs_le.mp hpm).2
    have h2 : %(Mpr)s - %(ibr)s ≤ %(iar)s := by norm_num
    rw [abs_le]; constructor <;> linarith
  have hd := fapprox_sub hp' hinv' (%(iar)s + (%(epu)s + %(einvu)s)) (by linarith)
    (by rw [hu]; norm_num)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v) (%(edu)s) :=
    fmono hd (by rw [hu]; norm_num)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) %(iar)s tpi_le hdm _ le_rfl
    (by rw [hu]; norm_num)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      (%(etu)s) := fmono ht (by rw [hu]; norm_num)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ %(Mtr)s := by
    rw [abs_mul]; exact (mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hres := fapprox_add hxq' ht' %(Br)s (by
    have h1 := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
    have h2 : %(exuvu)s + %(etu)s ≤ %(Br)s - (%(Mxuvr)s + %(Mtr)s) := by rw [hu]; norm_num
    linarith) (by norm_num)
  exact fmono hres (by rw [hu]; norm_num)
''' % d)
    d = fmt(sm, reals=('a', 'b', 'MH', 'mS', 'Muv', 'cx', 'pa', 'pb', 'ia', 'da', 'dl', 'dk', 'ta',
                       'tl', 'tk', 'ra', 'rl', 'rk'),
            rats=('lo', 'hi', 'LR', 'LS', 'MH', 'mS', 'eRh', 'eSh'), errs=('eH', 'eS', 'euv'))
    d['k'] = 'small'
    out.append('''
/-- The main path of `y1` for `2^-54 ≤ x ≤ 1`, with `ℓ = |ln x|`. -/
theorem small_piece (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : %(ar)s ≤ v) (hb : v ≤ %(br)s) (ℓ : ℝ) (hℓ : |Real.log v| = ℓ) (hℓ1 : ℓ ≤ 38)
    (hvl : v * ℓ ≤ 3679 / 10000) (hJ : FApprox J (J1 v) (14 / 10 * 𝐮)) (hJm : |J1 v| ≤ 51 / 100 * v)
    (hL : FApprox L (Real.log v) (6 / 5 * 𝐮 * ℓ + 1 / 2 ^ 59)) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      (%(rar)s * 𝐮 * (1 / v) + %(rlr)s * 𝐮 * ℓ + %(rkr)s * 𝐮) := by
  have hℓ0 : 0 ≤ ℓ := by rw [← hℓ]; exact abs_nonneg _
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) ha
''' % d)
    out.append(head % d)
    out.append(horner_steps('U1', 'V1', 'u1w', 'v1w', 'x * x', d))
    out.append(uvq % d)
    out.append('''  have hy1 : 1 ≤ 1 / v := by rw [le_div_iff₀ hv0]; linarith
  have hy54 : 1 / v ≤ 2 ^ 54 := by rw [div_le_iff₀ hv0]; norm_num at ha ⊢; linarith
  have hvb : |v| ≤ v := le_of_eq (abs_of_pos hv0)
  have hxq := fapprox_mul hx hq' v %(Muvr)s hvb hqm _ le_rfl (by rw [hu]; linarith)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) (%(cxr)s * 𝐮) :=
    fmono hxq (by rw [hu]; linarith)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ %(Muvr)s := by
    rw [abs_mul, abs_of_pos hv0]
    calc v * |eval U1 z / eval V1 z| ≤ 1 * %(Muvr)s :=
          mul_le_mul hb hqm (abs_nonneg _) zero_le_one
      _ = %(Muvr)s := one_mul _
  have hp := fapprox_mul hJ hL (51 / 100 * v) ℓ hJm (le_of_eq hℓ) _ le_rfl (by rw [hu]; linarith)
  have hp' : FApprox (J * L) (J1 v * Real.log v) (%(par)s * 𝐮 * ℓ + %(pbr)s * 𝐮) :=
    fmono hp (by rw [hu]; linarith)
  have hpm : |J1 v * Real.log v| ≤ 51 / 100 := by
    rw [abs_mul, hℓ]
    have := mul_le_mul_of_nonneg_right hJm hℓ0
    linarith
  have hinv := fapprox_div fapprox_one hx 1 v (by norm_num) (le_abs_self v) hv0 _ le_rfl (by
      have : (1 + 0) / (v - 0) = 1 / v := by ring
      rw [this]
      linarith)
  have hinv' : FApprox (1.0 / x) (1 / v) (%(iar)s * 𝐮 * (1 / v)) := by
    refine fmono hinv ?_
    calc _ = 1 / v / 2 ^ 53 + 1 / 2 ^ 1075 := by ring
      _ ≤ %(iar)s * 𝐮 * (1 / v) := by rw [hu]; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ 51 / 100 + 1 / v := by
    have := abs_sub (J1 v * Real.log v) (1 / v)
    rw [abs_of_pos (one_div_pos.mpr hv0)] at this
    linarith
  have hd := fapprox_sub hp' hinv'
    (51 / 100 + 1 / v + (%(par)s * 𝐮 * ℓ + %(pbr)s * 𝐮 + %(iar)s * 𝐮 * (1 / v))) (by linarith)
    (by rw [hu]; linarith)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v)
      (%(dar)s * 𝐮 * (1 / v) + %(dlr)s * 𝐮 * ℓ + %(dkr)s * 𝐮) := fmono hd (by rw [hu]; linarith)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) (51 / 100 + 1 / v) tpi_le hdm _ le_rfl
    (by rw [hu]; linarith)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      (%(tar)s * 𝐮 * (1 / v) + %(tlr)s * 𝐮 * ℓ + %(tkr)s * 𝐮) := fmono ht (by rw [hu]; linarith)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ 6367 / 10000 * (51 / 100 + 1 / v) := by
    rw [abs_mul]; exact mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)
  have hres := fapprox_add hxq' ht'
    (%(Muvr)s + 6367 / 10000 * (51 / 100 + 1 / v) +
      (%(cxr)s * 𝐮 + (%(tar)s * 𝐮 * (1 / v) + %(tlr)s * 𝐮 * ℓ + %(tkr)s * 𝐮))) (by
      have := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
      linarith) (by rw [hu]; linarith)
  exact fmono hres (by rw [hu]; linarith)
''' % d)
    return ''.join(out)

def lean_j1(pieces):
    out = []
    out.append('''import Library.Numerics.Float64.Bessel.BesselSmallJ0
import LeanExe.ProofKit.F64NearestScale

/-!
`Bessel.j1 x` for `|x| < 2`: the code computes `x/2 + x z R(z)/S(z)` with `z = x x` from
`2 ^ -27` on and `x/2` below.  Each lemma `piece_k` follows the first form through `F64Approx` on
one range of `|x|`, with the Horner bounds that the kernel checks on that range (`facts_k`); this
file is generated by `tools/bessel/gensmall.py`.  `BesselJ1Small.j1_small` puts the result within
`|x| (0.005 u + 2^-99)` plus the error of the piece of `J₁(x)`, by `BesselSmallApprox.j1_approx`.
-/

namespace Library.Numerics.Float64.Bessel.BesselSmallJ1
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS BesselSmallEval BesselSmallApprox BesselJ0Large BesselSmallJ0
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

def r1w : List UInt64 := [%s]
def s1w : List UInt64 := [%s]

theorem words : (∀ w ∈ r1w, Finite w) ∧ (∀ w ∈ s1w, Finite w) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem lists : r1w.map ratOfWord = R1 ∧ 1 :: s1w.map ratOfWord = S1 := ⟨rfl, rfl⟩

theorem rs_at (zf : Float) (hzf : Finite zf.toBits) (z δ : ℝ) (lo hi : ℚ)
    (hR : hornerOK R1 lo hi = true) (hS : hornerOK S1 lo hi = true)
    (h1 : (lo : ℝ) ≤ value zf.toBits) (h2 : value zf.toBits ≤ hi) (h3 : (lo : ℝ) ≤ z)
    (h4 : z ≤ hi) (hδ : |value zf.toBits - z| ≤ δ) :
    FApprox (hornerF (r1w.map Float.ofBits) zf) (eval R1 z)
        (hornerErr R1 lo hi + magBound (derivP R1) lo hi * δ) ∧
      FApprox (hornerF (1.0 :: s1w.map Float.ofBits) zf) (eval S1 z)
        (hornerErr S1 lo hi + magBound (derivP S1) lo hi * δ) := by
  obtain ⟨wr, ws⟩ := words
  obtain ⟨b1, b2⟩ := words_rel r1w wr
  obtain ⟨c1, c2⟩ := words_rel_one s1w ws
  exact ⟨horner_at _ _ R1 b1 b2 (by decide) lo hi hR zf hzf z δ h1 h2 h3 h4 hδ,
    horner_at _ _ S1 c1 c2 (by decide) lo hi hS zf hzf z δ h1 h2 h3 h4 hδ⟩

/-- `x * 0.5` is exact when the exponent field of `x` is at least 2. -/
theorem times_half (x : Float) (hf : Finite x.toBits) (he : 2 ≤ Wasm.IEEE64.exponent x.toBits) :
    FApprox (x * 0.5) (value x.toBits / 2) 0 := by
  have h05 : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl
  have hf05 : Finite (0x3FE0000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  obtain ⟨h1, h2⟩ := F64Exact.mul_half_exact x.toBits hf he
  unfold FApprox Approx
  rw [F64Bits.toBits_mul, h05, F64NearestScale.mul_comm_finite _ _ hf hf05]
  exact ⟨h1, by rw [h2]; simp⟩
''' % (', '.join('0x%016X' % w for w in R1W), ', '.join('0x%016X' % w for w in S1W)))
    for p in pieces:
        out.append(lean_j1_piece(p))
    return ''.join(out)

def lean_j1_piece(p):
    d = dict(p)
    for key in ('a', 'b', 'Mz', 'MH', 'Mr', 'Mrx', 'Mq', 'mS', 'LR', 'LS'):
        d[key + 'r'] = qs(p[key])
    for key in ('lo', 'hi', 'LR', 'LS', 'MH', 'mS'):
        d[key + 'q'] = qq(p[key])
    for key in ('eRh', 'eSh'):
        d[key + 'q'] = qq(p[key])
    for key in ('eH', 'eS', 'er', 'erx', 'eq', 'eres'):
        d[key + 'u'] = eu(p[key] / U)
    return '''
theorem facts_%(k)d : hornerOK R1 %(loq)s %(hiq)s = true ∧ hornerOK S1 %(loq)s %(hiq)s = true ∧
    hornerErr R1 %(loq)s %(hiq)s ≤ %(eRhq)s ∧ magBound (derivP R1) %(loq)s %(hiq)s ≤ %(LRq)s ∧
    magBound R1 %(loq)s %(hiq)s ≤ %(MHq)s ∧ hornerErr S1 %(loq)s %(hiq)s ≤ %(eShq)s ∧
    magBound (derivP S1) %(loq)s %(hiq)s ≤ %(LSq)s ∧ %(mSq)s ≤ lowBound S1 %(loq)s %(hiq)s := by
  decide +kernel

/-- The first form of `j1` for `%(a)s ≤ |x| ≤ %(b)s`. -/
theorem piece_%(k)d (x : Float) (hf : Finite x.toBits) (he : 2 ≤ Wasm.IEEE64.exponent x.toBits)
    (v : ℝ) (hv : value x.toBits = v) (ha : %(ar)s ≤ |v|) (hb : |v| ≤ %(br)s) :
    FApprox (x * 0.5 + x * x * hornerF (r1w.map Float.ofBits) (x * x) * x /
        hornerF (1.0 :: s1w.map Float.ofBits) (x * x))
      (v / 2 + v * (v ^ 2 * eval R1 (v ^ 2)) / eval S1 (v ^ 2)) (%(eresu)s) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_%(k)d
  have hx : FApprox x v 0 := by rw [← hv]; exact fapprox_exact x hf
  have hh : FApprox (x * 0.5) (v / 2) 0 := by rw [← hv]; exact times_half x hf he
  subst hv
  set v := value x.toBits
  have hz := sq_near x hf %(br)s hb (by norm_num)
  set z := v ^ 2 with hzd
  have hza : %(ar)s ^ 2 ≤ z := by nlinarith [abs_nonneg v, sq_abs v]
  have hzb : z ≤ %(br)s ^ 2 := by nlinarith [abs_nonneg v, sq_abs v]
  have hzm : |z| ≤ %(Mzr)s := by
    rw [abs_of_nonneg (by rw [hzd]; positivity)]; norm_num at hzb ⊢; linarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := rs_at (x * x) hz.1 z _ %(loq)s %(hiq)s k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP R1) %(loq)s %(hiq)s := (abs_nonneg _).trans
    (magBound_sound _ %(loq)s %(hiq)s z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP S1) %(loq)s %(hiq)s := (abs_nonneg _).trans
    (magBound_sound _ %(loq)s %(hiq)s z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (r1w.map Float.ofBits) (x * x)) (eval R1 z) (%(eHu)s) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: s1w.map Float.ofBits) (x * x)) (eval S1 z) (%(eSu)s) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval R1 z| ≤ %(MHr)s := (magBound_sound R1 %(loq)s %(hiq)s z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : %(mSr)s ≤ |eval S1 z| := by
    have := (lowBound_sound S1 %(loq)s %(hiq)s z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hr := fapprox_mul hz hH %(Mzr)s %(MHr)s hzm hHm _ le_rfl (by rw [hu]; norm_num)
  have hr' : FApprox (x * x * hornerF (r1w.map Float.ofBits) (x * x)) (z * eval R1 z) (%(eru)s) :=
    fmono hr (by rw [hu]; norm_num)
  have hrm : |z * eval R1 z| ≤ %(Mrr)s := by
    rw [abs_mul]; exact (mul_le_mul hzm hHm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hrx := fapprox_mul hr' hx %(Mrr)s %(br)s hrm hb _ le_rfl (by rw [hu]; norm_num)
  have hrx' : FApprox (x * x * hornerF (r1w.map Float.ofBits) (x * x) * x) (z * eval R1 z * v)
      (%(erxu)s) := fmono hrx (by rw [hu]; norm_num)
  have hrxm : |z * eval R1 z * v| ≤ %(Mrxr)s := by
    rw [abs_mul]; exact (mul_le_mul hrm hb (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hq := fapprox_div hrx' hS' %(Mrxr)s %(mSr)s hrxm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (x * x * hornerF (r1w.map Float.ofBits) (x * x) * x /
      hornerF (1.0 :: s1w.map Float.ofBits) (x * x)) (z * eval R1 z * v / eval S1 z) (%(equ)s) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |z * eval R1 z * v / eval S1 z| ≤ %(Mqr)s := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hrxm (by norm_num) hSm).trans (by norm_num)
  have hres := fapprox_add_half hh hq' 1022 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
    rw [e, hu]
    have := abs_add_le (v / 2) (z * eval R1 z * v / eval S1 z)
    have hv2 : |v / 2| ≤ %(br)s / 2 := by rw [abs_div, abs_two]; linarith
    norm_num at hqm hv2 ⊢
    linarith)
  refine fmono (fcongr hres ?_) (by rw [hu]; norm_num)
  have : eval S1 z ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hSm; norm_num at hSm
  field_simp
''' % d

if __name__ == '__main__':
    which, outp = sys.argv[1], sys.argv[2]
    if which == 'j0':
        ps = [j0_piece(k, a, b) for k, (a, b) in enumerate(j0_pieces())]
        for p in ps:
            print('form2', p['k'], p['a'], p['b'], 'error %.3f u' % float(p['eres'] / U), file=sys.stderr)
        src = lean_j0(ps) + '''
%s
end Library.Numerics.Float64.Bessel.BesselSmallJ0Form2
''' % '\n'.join('#print axioms form2_%d' % p['k'] for p in ps)
        open(outp, 'w').write(src)
    if which == 'y0':
        ps = [y0_piece(k, a, b, J) for k, (a, b, J) in enumerate(y0_pieces())]
        lg = y0_log()
        for p in ps:
            print('y0 piece', p['k'], p['a'], p['b'], 'error %.3f u' % float(p['eres'] / U), file=sys.stderr)
        print('y0 log piece: %.3f u l + %.3f u' % (lg['ar'], lg['br']), file=sys.stderr)
        src = lean_y0(ps, lg) + '''
#print axioms tpi_le
%s
#print axioms log_piece

end Library.Numerics.Float64.Bessel.BesselSmallY0
''' % '\n'.join('#print axioms piece_%d' % p['k'] for p in ps)
        open(outp, 'w').write(src)
    if which == 'y1':
        ps = [y1_piece(k, *t) for k, t in enumerate(y1_pieces())]
        sm = y1_small()
        for p in ps:
            print('y1 piece', p['k'], p['a'], p['b'], 'error %.3f u' % float(p['eres'] / U), file=sys.stderr)
        print('y1 small piece: %.3f u/x + %.3f u l + %.3f u' % (sm['ra'], sm['rl'], sm['rk']), file=sys.stderr)
        src = lean_y1(ps, sm) + '''
%s
#print axioms small_piece

end Library.Numerics.Float64.Bessel.BesselSmallY1
''' % '\n'.join('#print axioms piece_%d' % p['k'] for p in ps)
        open(outp, 'w').write(src)
    if which == 'j1':
        ps = [j1_piece(k, a, b) for k, (a, b) in enumerate(j1_pieces())]
        for p in ps:
            print('piece', p['k'], p['a'], p['b'], 'error %.3f u' % float(p['eres'] / U), file=sys.stderr)
        src = lean_j1(ps) + '''
#print axioms times_half
%s
end Library.Numerics.Float64.Bessel.BesselSmallJ1
''' % '\n'.join('#print axioms piece_%d' % p['k'] for p in ps)
        open(outp, 'w').write(src)
