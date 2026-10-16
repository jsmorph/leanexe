# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Generate Verified/Examples/BesselPQ0.lean and BesselPQ1.lean.

Usage: uv run tools/bessel/genpq.py ORDER OUTPUT

The kernel checks every bound in the generated files; this program only chooses the pieces of the
argument z = 1/x^2, the error bounds E, and the ratio bounds, with exact rational models of
PolyBound's magBound and lowBound and of F64Horner's hornerErr.
"""
import os, re, sys, math
from fractions import Fraction as F
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

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
def table(name):
    src = open(os.path.join(ROOT, 'Verified', 'Examples', 'Bessel.lean')).read()
    return [int(m, 16) for m in re.findall(r'0x[0-9A-Fa-f]{16}', src.split('def ' + name)[1].split(']')[0])]
J0T = table('j0Table'); J1T = table('j1Table')
u = F(1, 2**53)
N = 8
def ceil_dy(q, bits): return F(math.ceil(q * 2**bits), 2**bits)
def floor_dy(q, bits): return F(math.floor(q * 2**bits), 2**bits)
def q(fr):
    fr = F(fr)
    return '(%d : ℚ)' % fr.numerator if fr.denominator == 1 else '(%d / %d : ℚ)' % (fr.numerator, fr.denominator)
def qr(fr):
    fr = F(fr)
    return '(%d : ℝ)' % fr.numerator if fr.denominator == 1 else '(%d / %d : ℝ)' % (fr.numerator, fr.denominator)
B3W, B5W = 0x4006DB6D00000000, 0x40122E8B00000000
b3 = wordval(B3W); b5 = wordval(B5W)
# range k: (lo word, hi word, lo value, hi value, suffix, Fd module)
RANGES = {3: (0x4000000000000000, B3W, F(2), b3, '2', 'a'),
          2: (B3W, B5W, b3, b5, '3', 'a'),
          1: (B5W, 0x4020000000000000, b5, F(8), '5', 'a'),
          0: (0x4020000000000000, 0x4800000100000000, F(8), F(2)**130, '8', 'b')}
APX = {(0, 'p'): {3: 1067, 2: 1662, 1: 277, 0: 261}, (0, 'q'): {3: 127, 2: 109, 1: 22, 0: 18},
       (1, 'p'): {3: 1472, 2: 2231, 1: 321, 0: 282}, (1, 'q'): {3: 171, 2: 127, 1: 29, 0: 20}}
def ratioErr(R, S, lo, hi, d):
    eR = hornerErr(R, lo, hi); eS = hornerErr(S, lo, hi)
    MA = magBound(R, lo, hi); mB = lowBound(S, lo, hi)
    mB2 = lowBound(S, lo - d, hi + d)
    D = sub(mul(deriv(R), S), mul(R, deriv(S)))
    assert mB2 > 0 and eS < mB
    return eR / (mB - eS) + MA * eS / ((mB - eS) * mB) + uQ * ((MA + eR) / (mB - eS)) + etaQ + magBound(D, lo - d, hi + d) / mB2**2 * d
def data(T, k, kind):
    lw, hw, lo, hi, suf, mod = RANGES[k]
    d = ceil_dy((2 + F(1, 2**40)) * u / lo**2, 64 + 6 * (4 - k) if k else 72)
    assert (2 + F(1, 2**40)) * u / lo**2 <= d
    a = F(-1, 2**50) if k == 0 else floor_dy(1 / hi**2 - d, 30)
    assert a <= 1 / hi**2 - d
    last = ceil_dy(1 / lo**2 + d, 40)
    pts = [a] + [floor_dy(a + (last - a) * i / N, 40) for i in range(1, N)] + [last]
    o = 11 * k if kind == 'p' else 44 + 12 * k
    nS = 5 if kind == 'p' else 6
    wr = T[o:o + 6]; ws = T[o + 6:o + 6 + nS]
    R = [wordval(w) for w in wr]; S = [F(1)] + [wordval(w) for w in ws]
    worst = max(ratioErr(R, S, pts[i], pts[i + 1], d) for i in range(N))
    E = F(math.ceil(worst / u * 1000), 1000) * u
    rho = max(magBound(R, pts[i], pts[i + 1]) / lowBound(S, pts[i], pts[i + 1]) for i in range(N))
    rho = F(math.ceil(rho * 10**5), 10**5)
    return dict(d=d, pts=pts, E=E, wr=wr, ws=ws, rho=rho, lo=lo, hi=hi)
def gen(order):
    T = J0T if order == 0 else J1T
    tab = 'Bessel.j0Table' if order == 0 else 'Bessel.j1Table'
    P = 'P0' if order == 0 else 'P1'; Qf = 'Q0' if order == 0 else 'Q1'
    pre = 'BesselFd%d' % order
    out = []
    out.append('''import Verified.Examples.BesselPQRange
import LeanExe.ProofKit.BesselFd%(o)da
import LeanExe.ProofKit.BesselFd%(o)db

/-!
`Bessel.pAsym %(tab)s` and the `Q` term of `%(fn)s` on each of fdlibm's four ranges from 2 on, as
distances from `%(P)s` and `%(Q)s` (`pq_r3`, `pq_r2`, `pq_r1`, `pq_r0`).  Each range has the words of
its coefficients, the kernel checks of `BesselRatioEval.piecesOk` on eight pieces of the computed
`ẑ = 1/(x x)` and of `BesselPQEval.boundsOk` on the same pieces, and the comparisons
`%(pre)sa` and `%(pre)sb` of fdlibm's rational functions with `%(P)s` and `%(Q)s`.  The constants are
in units of `u = 2 ^ -53`; this file is generated by `tools/bessel/genpq.py`.
-/

namespace Verified.Examples.BesselPQ%(o)d
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound F64Approx F64Horner BesselRatioEval BesselPQEval
  BesselPQRange BesselPQ BesselRatio

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000
''' % dict(o=order, tab=tab, fn='j0 and y0' if order == 0 else 'j1 and y1', P=P, Q=Qf, pre=pre))
    for k in (3, 2, 1, 0):
        lw, hw, lo, hi, suf, mod = RANGES[k]
        Fd = '%s%s' % (pre, mod)
        dp = data(T, k, 'p'); dq = data(T, k, 'q')
        names = dict(k=k, tab=tab, P=P, Q=Qf, Fd=Fd, suf=suf, lw='0x%016X' % lw, hw='0x%016X' % hw,
                     lo=q(lo), hi=q(hi), lor=qr(lo), hir=qr(hi))
        pl = ('pR%s' if order == 0 else 'pr%s') % suf; sl = ('pS%s' if order == 0 else 'ps%s') % suf
        qrl = ('qR%s' if order == 0 else 'qr%s') % suf; qsl = ('qS%s' if order == 0 else 'qs%s') % suf
        names.update(pl=pl, sl=sl, qrl=qrl, qsl=qsl)
        def lst(ws): return '[' + ', '.join('0x%016X' % w for w in ws) + ']'
        out.append('''
/-! Range %(k)d. -/

def pr%(k)d : List UInt64 := %(pr)s
def ps%(k)d : List UInt64 := %(ps)s
def qr%(k)d : List UInt64 := %(qr)s
def qs%(k)d : List UInt64 := %(qs)s
''' % dict(k=k, pr=lst(dp['wr']), ps=lst(dp['ws']), qr=lst(dq['wr']), qs=lst(dq['ws'])))
        for kind, dd in (('p', dp), ('q', dq)):
            pts = dd['pts']
            names['%s_args' % kind] = '%s %s %s %s %s [%s]' % (q(dd['d']), q(dd['E']), q(dd['rho']), q(pts[0]), q(pts[1]), ', '.join(q(p) for p in pts[2:]))
            out.append('''theorem check_%(kind)s%(k)d : piecesOk (%(kind)sr%(k)d.map ratOfWord) (1 :: %(kind)ss%(k)d.map ratOfWord)
    %(d)s %(E)s %(a)s [%(bs)s] = true := by
  decide +kernel

theorem bounds_%(kind)s%(k)d : boundsOk (%(kind)sr%(k)d.map ratOfWord) (1 :: %(kind)ss%(k)d.map ratOfWord)
    %(rho)s %(a)s [%(bs)s] = true := by
  decide +kernel
''' % dict(kind=kind, k=k, d=q(dd['d']), E=q(dd['E']), rho=q(dd['rho']), a=q(pts[0]), bs=', '.join(q(p) for p in pts[1:])))
            names['%s_d' % kind] = q(dd['d']); names['%s_E' % kind] = q(dd['E']); names['%s_rho' % kind] = q(dd['rho'])
            names['%s_a' % kind] = q(pts[0]); names['%s_b' % kind] = q(pts[1]); names['%s_rest' % kind] = ', '.join(q(p) for p in pts[2:])
            names['%s_Er' % kind] = qr(dd['E']); names['%s_rhor' % kind] = qr(dd['rho'])
        names['ap'] = APX[(order, 'p')][k]; names['aq'] = APX[(order, 'q')][k]
        # range facts
        out.append('''theorem words_%(k)d : (∀ w ∈ pr%(k)d, Finite w) ∧ (∀ w ∈ ps%(k)d, Finite w) ∧
    (∀ w ∈ qr%(k)d, Finite w) ∧ (∀ w ∈ qs%(k)d, Finite w) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem lists_%(k)d : pr%(k)d.map ratOfWord = %(Fd)s.%(pl)s ∧ ps%(k)d.map ratOfWord = %(Fd)s.%(sl)s ∧
    qr%(k)d.map ratOfWord = %(Fd)s.%(qrl)s ∧ qs%(k)d.map ratOfWord = %(Fd)s.%(qsl)s :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem range_%(k)d (x : Float) (hlo : %(lw)s ≤ x.toBits.toNat) (hhi : x.toBits.toNat < %(hw)s) :
    Bessel.rangeOf ((x.toBits >>> 32) &&& 0x7fffffff) = %(k)d := by
  have hix := TrigSinCos.high_word x.toBits
  unfold Bessel.rangeOf
  simp only [ge_iff_le, UInt64.le_iff_toNat_le, hix, UInt64.reduceToNat]
  %(rangeproof)s

theorem value_%(k)d (x : Float) (hlo : %(lw)s ≤ x.toBits.toNat) (hhi : x.toBits.toNat < %(hw)s) :
    %(lor)s ≤ value x.toBits ∧ value x.toBits ≤ %(hir)s := by
  have hlt : x.toBits.toNat < 2 ^ 63 := by omega
  have h1 := (F64PositiveOrder.value_le_iff (left := (%(lw)s : UInt64)) (right := x.toBits)
    (by decide) hlt).mpr hlo
  have h2 := F64PositiveOrder.value_strict (left := x.toBits) (right := (%(hw)s : UInt64))
    (by decide) hhi
  have e1 : value (%(lw)s : UInt64) = %(lor)s := by
    rw [← ratOfWord_cast]
    have : ratOfWord %(lw)s = %(lo)s := by decide +kernel
    rw [this]; push_cast; ring
  have e2 : value (%(hw)s : UInt64) ≤ %(hir)s := by
    rw [← ratOfWord_cast]
    have : ratOfWord %(hw)s ≤ %(hi)s := by decide +kernel
    have h := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at h
    linarith
  constructor <;> linarith

theorem pAsym_%(k)d (x : Float) (h : Bessel.rangeOf ((x.toBits >>> 32) &&& 0x7fffffff) = %(k)d) :
    Bessel.pAsym %(tab)s x = 1.0 + hornerF (pr%(k)d.map Float.ofBits) (1.0 / (x * x)) /
      hornerF (1.0 :: ps%(k)d.map Float.ofBits) (1.0 / (x * x)) := by
  unfold Bessel.pAsym
  rw [h]
  rfl

theorem qRatio_%(k)d (x : Float) (h : Bessel.rangeOf ((x.toBits >>> 32) &&& 0x7fffffff) = %(k)d) :
    Bessel.qRatio %(tab)s x = hornerF (qr%(k)d.map Float.ofBits) (1.0 / (x * x)) /
      hornerF (1.0 :: qs%(k)d.map Float.ofBits) (1.0 / (x * x)) := by
  unfold Bessel.qRatio
  rw [h]
  rfl
''' % dict(names, rangeproof=rangeproof(k)))
        # main theorem
        out.append(maintheorem(order, k, names))
    out.append('''
#print axioms pq_r3
#print axioms pq_r2
#print axioms pq_r1
#print axioms pq_r0

end Verified.Examples.BesselPQ%d
''' % order)
    return ''.join(out)
def rangeproof(k):
    # rangeOf: if ix >= 0x40200000 then 0 else if ix >= 0x40122E8B then 1 else if ix >= 0x4006DB6D then 2 else 3
    if k == 0: return 'rw [ite_eq_left (by omega)]'
    if k == 1: return 'rw [ite_eq_right (by omega), ite_eq_left (by omega)]'
    if k == 2: return 'rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]'
    return 'rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]'
def maintheorem(order, k, n):
    lw, hw, lo, hi, suf, mod = RANGES[k]
    ap = F(n['ap'], 2**68) + F(1, 2**70); aq = F(n['aq'], 2**68) + F(1, 2**70)
    n = dict(n)
    n['apr'] = '(%d / 2 ^ 68 + 1 / 2 ^ 70 : ℝ)' % n['ap']; n['aqr'] = '(%d / 2 ^ 68 + 1 / 2 ^ 70 : ℝ)' % n['aq']
    fdp = 'pzero' if order == 0 else 'pone'; fdq = 'qzero' if order == 0 else 'qone'
    if k == 0:
        n['fdcall_p'] = '%s.%s_8 v (by push_cast; linarith)' % (n['Fd'], fdp)
        n['fdcall_q'] = '%s.%s_8 v (by push_cast; linarith)' % (n['Fd'], fdq)
    else:
        lo_name = {3: '2', 2: 'BesselRatio.b3', 1: 'BesselRatio.b5'}[k]
        hi_name = {3: 'BesselRatio.b3', 2: 'BesselRatio.b5', 1: '8'}[k]
        n['fdcall_p'] = '%s.%s_%s v (by rw [hlo_q]; linarith) (by rw [hhi_q]; linarith)' % (n['Fd'], fdp, n['suf'])
        n['fdcall_q'] = '%s.%s_%s v (by rw [hlo_q]; linarith) (by rw [hhi_q]; linarith)' % (n['Fd'], fdq, n['suf'])
        n['lo_name'] = lo_name; n['hi_name'] = hi_name
    n['qfun'] = '(Bessel.qRatio %s x - 0.125) / x' % n['tab'] if order == 0 else '(0.375 + Bessel.qRatio %s y) / y' % n['tab']
    xv = 'x' if order == 0 else 'y'
    n['xv'] = xv
    # value forms
    if order == 0:
        n['Pl'] = '1 - %s - %s' % (n['p_rhor'], n['apr']); n['Ph'] = '1 + %s' % n['apr']
        n['Qh'] = '1 / 8 / %s + %s' % (n['lor'], n['aqr'])
        n['eQ'] = '(%s + 𝐮 / 8) / %s + (1 / 8 + (%s + 𝐮 / 8)) / %s / 2 ^ 53 + 1 / 2 ^ 1075 + %s' % (n['q_Er'], n['lor'], n['q_Er'], n['lor'], n['aqr'])
        n['sign_p'] = 'eval_nonpos'; n['sign_q'] = 'eval_nonneg'
        n['qlemma'] = 'q0_of_ratio'
        n['qfd'] = 'qFd (-1 / 8)'
    else:
        n['Pl'] = '1 - %s' % n['apr']; n['Ph'] = '1 + %s + %s' % (n['p_rhor'], n['apr'])
        n['Qh'] = '3 / 8 / %s + %s' % (n['lor'], n['aqr'])
        n['eQ'] = '(%s + 𝐮 / 4) / %s + (3 / 8 + (%s + 𝐮 / 4)) / %s / 2 ^ 53 + 1 / 2 ^ 1075 + %s' % (n['q_Er'], n['lor'], n['q_Er'], n['lor'], n['aqr'])
        n['sign_p'] = 'eval_nonneg'; n['sign_q'] = 'eval_nonpos'
        n['qlemma'] = 'q1_of_ratio'
        n['qfd'] = 'qFd (3 / 8)'
    n['eP'] = '%s + 𝐮 + %s' % (n['p_Er'], n['apr'])
    hq = '' if k == 0 else '''  have hlo_q : (((%(lo_name)s : ℚ)) : ℝ) = %(lor)s := by
    have : (%(lo_name)s : ℚ) = %(lo)s := by decide +kernel
    rw [this]; push_cast; ring
  have hhi_q : (((%(hi_name)s : ℚ)) : ℝ) = %(hir)s := by
    have : (%(hi_name)s : ℚ) = %(hi)s := by decide +kernel
    rw [this]; push_cast; ring
''' % n
    n['hq'] = hq
    if order == 0:
        n['ratio_sign'] = '''  have hpsg : eval (pr%(k)d.map ratOfWord) (1 / v ^ 2) / eval (1 :: ps%(k)d.map ratOfWord) (1 / v ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (eval_nonpos _ (by decide +kernel) _ (by positivity)) hSp.le
  have hqsg : 0 ≤ eval (qr%(k)d.map ratOfWord) (1 / v ^ 2) / eval (1 :: qs%(k)d.map ratOfWord) (1 / v ^ 2) :=
    div_nonneg (eval_nonneg _ (by decide +kernel) _ (by positivity)) hSq.le
''' % n
        n['qcall'] = 'q0_of_ratio hq hxf hqsg (abs_le.mp hqb).2 (by norm_num) (by norm_num) (by norm_num) hv.1'
        n['pbounds'] = '''    · have := (abs_le.mp hpb).1
      have := (abs_le.mp happ).1
      linarith
    · have := (abs_le.mp happ).2
      linarith'''
        n['qbound'] = '''    have h1 : |(ρq - 1 / 8) / v| ≤ 1 / 8 / %(lor)s := by
      rw [abs_div, abs_of_pos hv0, div_le_div_iff₀ hv0 (by norm_num)]
      have : |ρq - 1 / 8| ≤ 1 / 8 := by rw [abs_le]; constructor <;> linarith [(abs_le.mp hqb).2]
      nlinarith [hv.1]''' % n
    else:
        n['ratio_sign'] = '''  have hpsg : 0 ≤ eval (pr%(k)d.map ratOfWord) (1 / v ^ 2) / eval (1 :: ps%(k)d.map ratOfWord) (1 / v ^ 2) :=
    div_nonneg (eval_nonneg _ (by decide +kernel) _ (by positivity)) hSp.le
  have hqsg : eval (qr%(k)d.map ratOfWord) (1 / v ^ 2) / eval (1 :: qs%(k)d.map ratOfWord) (1 / v ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (eval_nonpos _ (by decide +kernel) _ (by positivity)) hSq.le
''' % n
        n['qcall'] = 'q1_of_ratio (ρ := %s) hq hxf hqsg (by have := (abs_le.mp hqb).1; push_cast at this; linarith) (by norm_num) (by norm_num) (by norm_num) hv.1' % n['q_rhor']
        n['pbounds'] = '''    · have := (abs_le.mp happ).1
      linarith
    · have := (abs_le.mp hpb).2
      have := (abs_le.mp happ).2
      linarith'''
        n['qbound'] = '''    have h1 : |(3 / 8 + ρq) / v| ≤ 3 / 8 / %(lor)s := by
      rw [abs_div, abs_of_pos hv0, div_le_div_iff₀ hv0 (by norm_num)]
      have : |3 / 8 + ρq| ≤ 3 / 8 := by rw [abs_le]; constructor <;> linarith [(abs_le.mp hqb).1]
      nlinarith [hv.1]''' % n
    n['ratio_sign'] = n['ratio_sign']
    return '''
/-- `pAsym` and the `Q` term on range %(k)d. -/
theorem pq_r%(k)d (%(xv)s : Float) (hxf : Finite %(xv)s.toBits) (hlo : %(lw)s ≤ %(xv)s.toBits.toNat)
    (hhi : %(xv)s.toBits.toNat < %(hw)s) :
    FApprox (Bessel.pAsym %(tab)s %(xv)s) (%(P)s (value %(xv)s.toBits)) (%(eP)s) ∧
      FApprox (%(qfun)s) (%(Q)s (value %(xv)s.toBits)) (%(eQ)s) ∧
      %(Pl)s ≤ %(P)s (value %(xv)s.toBits) ∧ %(P)s (value %(xv)s.toBits) ≤ %(Ph)s ∧
      |%(Q)s (value %(xv)s.toBits)| ≤ %(Qh)s := by
  obtain ⟨fpr, fps, fqr, fqs⟩ := words_%(k)d
  obtain ⟨lpr, lps, lqr, lqs⟩ := lists_%(k)d
  have hv := value_%(k)d %(xv)s hlo hhi
  set v := value %(xv)s.toBits with hvdef
  have hv0 : 0 < v := by linarith [hv.1]
  have hk := range_%(k)d %(xv)s hlo hhi
  obtain ⟨hp, hSp, hpb'⟩ := ratio_at pr%(k)d ps%(k)d fpr fps (by decide) %(xv)s hxf _ _ hv.1 hv.2 (by norm_num)
    (by norm_num) %(p_d)s %(p_E)s %(p_rho)s %(p_a)s %(p_b)s [%(p_rest)s] check_p%(k)d bounds_p%(k)d
    (by norm_num [unitRoundoff64]) (by norm_num) (by norm_num [lastD])
  obtain ⟨hq, hSq, hqb'⟩ := ratio_at qr%(k)d qs%(k)d fqr fqs (by decide) %(xv)s hxf _ _ hv.1 hv.2 (by norm_num)
    (by norm_num) %(q_d)s %(q_E)s %(q_rho)s %(q_a)s %(q_b)s [%(q_rest)s] check_q%(k)d bounds_q%(k)d
    (by norm_num [unitRoundoff64]) (by norm_num) (by norm_num [lastD])
  have hpb := ratio_abs _ _ _ _ ⟨hSp, hpb'⟩
  have hqb := ratio_abs _ _ _ _ ⟨hSq, hqb'⟩
%(ratio_sign)s%(hq)s  set ρp := eval (pr%(k)d.map ratOfWord) (1 / v ^ 2) / eval (1 :: ps%(k)d.map ratOfWord) (1 / v ^ 2)
    with hρp
  set ρq := eval (qr%(k)d.map ratOfWord) (1 / v ^ 2) / eval (1 :: qs%(k)d.map ratOfWord) (1 / v ^ 2)
    with hρq
  have hpfd : 1 + ρp = pFd %(Fd)s.%(pl)s %(Fd)s.%(sl)s v := by
    rw [hρp, ← lpr, ← lps, eval_one_cons, BesselRatio.pFd]
  have hqfd : %(qval)s = %(qfd)s %(Fd)s.%(qrl)s %(Fd)s.%(qsl)s v := by
    rw [hρq, ← lqr, ← lqs, eval_one_cons, BesselRatio.qFd]
    push_cast
    ring
  have happ := %(fdcall_p)s
  have happq := %(fdcall_q)s
  rw [← hpfd] at happ
  rw [← hqfd] at happq
  refine ⟨?_, ?_, ?_⟩
  · rw [pAsym_%(k)d %(xv)s hk]
    have h1 := p_of_ratio hp hpb (by norm_num [unitRoundoff64])
    have h2 := fshift (v' := %(P)s v) (d := %(apr)s) h1 (by rw [abs_sub_comm]; exact happ)
    exact fmono h2 (le_of_eq (by push_cast; ring))
  · rw [qRatio_%(k)d %(xv)s hk]
    have h1 := %(qcall)s
    have h2 := fshift (v' := %(Q)s v) (d := %(aqr)s) h1 (by rw [abs_sub_comm]; exact happq)
    exact fmono h2 (le_of_eq (by push_cast; ring))
  · refine ⟨?_, ?_, ?_⟩
%(pbounds)s
%(qbound)s
    have := abs_sub_abs_le_abs_sub (%(Q)s v) (%(qval)s)
    linarith
''' % dict(n, qval='(ρq - 1 / 8) / v' if order == 0 else '(3 / 8 + ρq) / v')
if __name__ == '__main__':
    order = int(sys.argv[1])
    open(sys.argv[2], 'w').write(gen(order))
