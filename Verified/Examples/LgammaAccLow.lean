import Verified.Examples.LgammaAccPoly
import Verified.Examples.LgammaLogdAcc
import Verified.Examples.SinpiTiny
import Verified.Examples.SinhWords

/-!
The two branches of `Lgamma.accurate` below `1/4`, at `x = |sx|`.  Below `2^-100` the code returns
`-log x` from `asLogdAccurate` (`tiny`), and `log |Γ sx| + log |sx|` is at most `4 |sx|`
(`GammaBasic.abs_lgamma_add_log_le`).  From `2^-100` to `1/4` it adds `sx P (sx)`, for the
polynomial at offset 0 of `accurateTable` (`LgammaAccPoly.small_ok`), to `-log x` (`low`), since
`log |Γ sx| = log Γ (1 + sx) - log |sx|`.  Both branches end with `adjust`: when `fh + 2 fl` is
exact, so that `fh + fl` may lie halfway between two doubles, and the rounding is to nearest, the
code multiplies `fl` by `1 ± 2^-52` with the sign of `fll`, which moves `fl` by at most `|fl|/2^51`.
Each branch returns a pair within `2^-70` of `log |Γ sx|`, relative, whose high part has magnitude
at least 1, so the polynomials about the negative zeros do not apply to it (`LowSpec`).
-/

namespace Verified.Examples.LgammaAccLow
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD LgammaLogAccKern

set_option exponentiation.threshold 4096

/-- The end of each branch of `Lgamma.accurate`: `fl` times `1 ± 2^-52` when `fh + 2 fl` is exact
and the rounding is to nearest. -/
def adjust (fh fl fll : Float) : Float × Float :=
  let (_, e) := fastTwoSum fh (2.0 * fl)
  let p54 := Float.ofBits 0x3C90000000000000  -- 0x1p-54
  if e == 0.0 && 1.0 + p54 == 1.0 - p54 then
    (fh, fl * (1.0 + Lgamma.copySign (Float.ofBits 0x3CB0000000000000) fl * Lgamma.copySign 1.0 fll))
  else (fh, fl)

/-- The branch below `2^-100`. -/
def tiny (logTab hTab : Array UInt64) (x : Float) : Float × Float :=
  let (lh, ll, lll) := Lgamma.asLogdAccurate logTab hTab x
  let (fh, fl) := fastTwoSum (-lh) (-ll)
  let (fl, fll) := fastTwoSum fl (-lll)
  adjust fh fl fll

/-- The branch from `2^-100` to `1/4`. -/
def low (logTab hTab accTab : Array UInt64) (sx x : Float) : Float × Float :=
  let (fh, fl) := Lgamma.polyDDDFst accTab 0 34 sx 0.0
  let (fh, fl) := mulDDD sx fh fl
  let (lh, ll, lll) := Lgamma.asLogdAccurate logTab hTab x
  let (fh, fl) := sumDD fh fl (-ll) (-lll)
  let (fh, fll) := twoSum (-lh) fh
  let (fl, fll) := twoSum fll fl
  adjust fh fl fll

/-- The bounds on the result of a branch below `1/4`. -/
def LowSpec (L : ℝ) (p : Float × Float) : Prop :=
  Finite p.1.toBits ∧ Finite p.2.toBits ∧ 1 ≤ |value p.1.toBits| ∧
    |value p.2.toBits| ≤ 1 / 2 ^ 40 ∧ |value p.1.toBits + value p.2.toBits - L| ≤ |L| / 2 ^ 70

theorem neg_float (a : Float) (ha : Finite a.toBits) :
    Finite (-a).toBits ∧ value (-a).toBits = -value a.toBits := by
  have h := fapprox_neg (fapprox_self a ha)
  exact ⟨h.1, by have := abs_nonpos_iff.mp h.2; linarith⟩

theorem sign_word (w : UInt64) :
    w &&& 0x8000000000000000 = 0 ∨ w &&& 0x8000000000000000 = 0x8000000000000000 := by
  have h := Nat.and_two_pow w.toNat 63
  rcases Bool.eq_false_or_eq_true (w.toNat.testBit 63) with hb | hb
  · right
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl, h, hb]
    rfl
  · left
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl, h, hb]
    rfl

/-- The factor `1 ± 2^-52` of `adjust`. -/
theorem factor (a b : Float) :
    Finite (1.0 + Lgamma.copySign (Float.ofBits 0x3CB0000000000000) a *
        Lgamma.copySign 1.0 b).toBits ∧
      |value (1.0 + Lgamma.copySign (Float.ofBits 0x3CB0000000000000) a *
        Lgamma.copySign 1.0 b).toBits - 1| ≤ 1 / 2 ^ 52 := by
  have hw : (1.0 + Lgamma.copySign (Float.ofBits 0x3CB0000000000000) a *
        Lgamma.copySign 1.0 b).toBits = 0x3FF0000000000001 ∨
      (1.0 + Lgamma.copySign (Float.ofBits 0x3CB0000000000000) a *
        Lgamma.copySign 1.0 b).toBits = 0x3FEFFFFFFFFFFFFE := by
    rcases sign_word a.toBits with ha | ha <;> rcases sign_word b.toBits with hb | hb <;>
    · simp only [Lgamma.copySign, F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_ofBits,
        ha, hb, show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
      first
        | exact Or.inl (by decide +kernel)
        | exact Or.inr (by decide +kernel)
  rcases hw with hw | hw <;> rw [hw]
  · refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
    rw [← PolyBound.ratOfWord_cast,
      show PolyBound.ratOfWord 0x3FF0000000000001 = 1 + 1 / 2 ^ 52 by decide +kernel]
    norm_num
  · refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
    rw [← PolyBound.ratOfWord_cast,
      show PolyBound.ratOfWord 0x3FEFFFFFFFFFFFFE = 1 - 1 / 2 ^ 52 by decide +kernel]
    norm_num

/-- **`adjust`** keeps the high part and moves the low part by at most `|fl|/2^51 + 2^-1075`. -/
theorem adjust_spec (fh fl fll : Float) (hfl : Finite fl.toBits) (hb : |value fl.toBits| ≤ 1) :
    (adjust fh fl fll).1 = fh ∧ Finite (adjust fh fl fll).2.toBits ∧
      |value (adjust fh fl fll).2.toBits - value fl.toBits| ≤
        |value fl.toBits| / 2 ^ 51 + 1 / 2 ^ 1075 := by
  unfold adjust
  generalize fastTwoSum fh (2.0 * fl) = p
  obtain ⟨a, e⟩ := p
  dsimp only
  split_ifs
  · refine ⟨rfl, ?_⟩
    obtain ⟨hFf, hFv⟩ := factor fl fll
    set F := 1.0 + Lgamma.copySign (Float.ofBits 0x3CB0000000000000) fl * Lgamma.copySign 1.0 fll
    have hF1 : |value F.toBits| ≤ 1 + 1 / 2 ^ 52 := by
      have := abs_sub_abs_le_abs_sub (value F.toBits) 1
      rw [abs_one] at this
      linarith
    have hm := fapprox_mul (fapprox_self fl hfl) (fapprox_self F hFf) |value fl.toBits|
      (1 + 1 / 2 ^ 52) le_rfl hF1 (|value fl.toBits| * (1 + 1 / 2 ^ 52)) (by simp)
      (by nlinarith [(by norm_num : (1 : ℝ) * (1 + 1 / 2 ^ 52) < 2 ^ 1022)])
    refine ⟨hm.1, ?_⟩
    have h2 := hm.2
    simp only [mul_zero, zero_mul, add_zero, zero_add] at h2
    have h3 : |value fl.toBits * value F.toBits - value fl.toBits| ≤ |value fl.toBits| / 2 ^ 52 := by
      rw [show value fl.toBits * value F.toBits - value fl.toBits =
        value fl.toBits * (value F.toBits - 1) by ring, abs_mul]
      have := mul_le_mul_of_nonneg_left hFv (abs_nonneg (value fl.toBits))
      linarith
    have h4 := abs_sub_le (value (fl * F).toBits) (value fl.toBits * value F.toBits) (value fl.toBits)
    have h5 : |value fl.toBits| * (1 + 1 / 2 ^ 52) / 2 ^ 53 + |value fl.toBits| / 2 ^ 52 ≤
        |value fl.toBits| / 2 ^ 51 := by
      have := abs_nonneg (value fl.toBits)
      nlinarith
    linarith
  · exact ⟨rfl, hfl, by simp only [sub_self, abs_zero]; positivity⟩

/-- `log x` from `2^-1074` to `1/4`. -/
theorem log_range (v : ℝ) (h1 : 1 / 2 ^ 1074 ≤ v) (h2 : v < 1 / 4) :
    -745 ≤ Real.log v ∧ Real.log v < -(1386 / 1000) := by
  have hv : 0 < v := lt_of_lt_of_le (by positivity) h1
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  constructor
  · have h := Real.log_le_log (by positivity) h1
    rw [one_div, Real.log_inv, Real.log_pow] at h
    push_cast at h
    nlinarith
  · have h := Real.log_lt_log hv h2
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    push_cast at h
    nlinarith

/-- `log x` below `2^-100`. -/
theorem log_tiny (v : ℝ) (hv : 0 < v) (h2 : v < 1 / 2 ^ 100) : Real.log v < -(6931 / 100) := by
  have l2a := Real.log_two_gt_d9
  have h := Real.log_lt_log hv h2
  rw [one_div, Real.log_inv, Real.log_pow] at h
  push_cast at h
  nlinarith

/-- `log x` from `2^-100` on. -/
theorem log_low (v : ℝ) (h1 : 1 / 2 ^ 100 ≤ v) : -(6932 / 100) ≤ Real.log v := by
  have l2b := Real.log_two_lt_d9
  have h := Real.log_le_log (by positivity) h1
  rw [one_div, Real.log_inv, Real.log_pow] at h
  push_cast at h
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The branch below `2^-100`.** -/
theorem tiny_spec (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact) (sx : Float)
    (hsx : Finite sx.toBits) (h0 : value sx.toBits ≠ 0) (hlt : |value sx.toBits| < 1 / 2 ^ 100) :
    LowSpec (GammaBasic.lgamma (value sx.toBits)) (tiny Tgamma.logdTable H sx.abs) := by
  obtain ⟨haf, hav⟩ := SinhWords.abs_float sx hsx
  set vs := value sx.toBits with hvs
  have hpos : 0 < value sx.abs.toBits := by rw [hav]; exact abs_pos.mpr h0
  have hmin := SinpiTiny.abs_ge_min sx.toBits h0
  obtain ⟨hlo, -⟩ := log_range |vs| hmin (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 < 1 / 4)])
  have hhi := log_tiny |vs| (abs_pos.mpr h0) hlt
  obtain ⟨t1f, t2f, t3f, te, t2b, t3b⟩ := LgammaLogdAcc.acc_abs hF hLA sx.abs haf hpos
  rw [hav] at te
  unfold tiny
  generalize Lgamma.asLogdAccurate Tgamma.logdTable H sx.abs = T at t1f t2f t3f te t2b t3b
  obtain ⟨lh, ll, lll⟩ := T
  dsimp only at t1f t2f t3f te t2b t3b ⊢
  set l0 := value lh.toBits
  set l1 := value ll.toBits
  set l2 := value lll.toBits
  have hl0a : |l0| ≤ 746 := by
    have h3 : |l0| ≤ 745 + 1 / 2 ^ 88 + |l1| + |l2| := by
      have := abs_add_le (l0 + l1 + l2 - Real.log |vs|) (-(l1 + l2) + Real.log |vs|)
      have h4 := abs_add_le (-(l1 + l2)) (Real.log |vs|)
      have h5 := abs_add_le l1 l2
      rw [show l0 + l1 + l2 - Real.log |vs| + (-(l1 + l2) + Real.log |vs|) = l0 by ring] at this
      rw [abs_neg, abs_of_neg (by linarith : Real.log |vs| < 0)] at h4
      linarith
    linarith
  have hl1 : |l1| ≤ 1 / 2 ^ 41 := by
    have := div_le_div_of_nonneg_right hl0a (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    linarith [(by norm_num : (746 : ℝ) / 2 ^ 51 + 1 / 2 ^ 50 ≤ 1 / 2 ^ 41)]
  have hl2 : |l2| ≤ 1 / 2 ^ 90 := by
    have := div_le_div_of_nonneg_right hl0a (by norm_num : (0 : ℝ) ≤ 2 ^ 100)
    linarith [(by norm_num : (746 : ℝ) / 2 ^ 100 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 90)]
  have hl0b : 6930 / 100 ≤ |l0| := by
    have := abs_le.mp te
    have := abs_le.mp hl1
    have := abs_le.mp hl2
    rw [abs_of_neg (by linarith : l0 < 0)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 88 + 1 / 2 ^ 41 + 1 / 2 ^ 90 ≤ 1 / 100)]
  obtain ⟨n0f, n0v⟩ := neg_float lh t1f
  obtain ⟨n1f, n1v⟩ := neg_float ll t2f
  obtain ⟨n2f, n2v⟩ := neg_float lll t3f
  obtain ⟨af, bf, hab, hbb, -⟩ := fastTwoSum_spec (-lh) (-ll) n0f n1f
    (by rw [n0v, n1v, abs_neg, abs_neg]; linarith) (by rw [n0v, abs_neg]; linarith)
  generalize fastTwoSum (-lh) (-ll) = P at af bf hab hbb
  obtain ⟨a, b⟩ := P
  dsimp only at af bf hab hbb ⊢
  rw [n0v, n1v] at hab
  rw [n1v, abs_neg] at hbb
  obtain ⟨cf, df, hcd, hcb, hdb⟩ := TgammaAcc2.fts_approx b (-lll) bf n2f (1 / 2 ^ 41)
    (1 / 2 ^ 90) (hbb.trans hl1) (by rw [n2v, abs_neg]; exact hl2) (by norm_num)
  generalize fastTwoSum b (-lll) = Q at cf df hcd hcb hdb
  obtain ⟨c, d⟩ := Q
  dsimp only at cf df hcd hcb hdb ⊢
  rw [n2v] at hcd
  have hcb' : |value c.toBits| ≤ 1 / 2 ^ 41 + 1 / 2 ^ 60 := by
    linarith [(by norm_num : (1 / 2 ^ 41 + 1 / 2 ^ 90 : ℝ) * (1 + 1 / 2 ^ 53) ≤ 1 / 2 ^ 41 + 1 / 2 ^ 60)]
  obtain ⟨hr1, hr2f, hr2⟩ := adjust_spec a c d cf (hcb'.trans (by norm_num))
  generalize adjust a c d = R at hr1 hr2f hr2
  obtain ⟨r1, r2⟩ := R
  dsimp only at hr1 hr2f hr2
  subst hr1
  -- the reference
  have hL := GammaBasic.abs_lgamma_add_log_le h0 (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 ≤ 1 / 4)])
  rw [← Real.log_abs] at hL
  set L := GammaBasic.lgamma vs
  have hc2 : |value r2.toBits - value c.toBits| ≤ 1 / 2 ^ 90 := by
    have := div_le_div_of_nonneg_right hcb' (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    linarith [(by norm_num : ((1 : ℝ) / 2 ^ 41 + 1 / 2 ^ 60) / 2 ^ 51 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 90)]
  have herr : |value r1.toBits + value r2.toBits - L| ≤ 1 / 2 ^ 87 := by
    have hdb' : |value d.toBits| ≤ 1 / 2 ^ 91 := by
      linarith [(by norm_num : (1 / 2 ^ 41 + 1 / 2 ^ 90 : ℝ) / 2 ^ 51 ≤ 1 / 2 ^ 91)]
    have hcd' : |value c.toBits + value d.toBits - (value b.toBits + -l2)| ≤ 1 / 2 ^ 140 := by
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 90 / 2 ^ 53 + (1 / 2 ^ 41 + 1 / 2 ^ 90) / 2 ^ 104 ≤
        1 / 2 ^ 140)]
    have hsx4 : 4 * |vs| ≤ 4 / 2 ^ 100 := by linarith
    have key : value r1.toBits + value r2.toBits - L =
        -(l0 + l1 + l2 - Real.log |vs|) - (L + Real.log |vs|) - value d.toBits +
          (value c.toBits + value d.toBits - (value b.toBits + -l2)) +
          (value r2.toBits - value c.toBits) := by linarith
    rw [key]
    have e1 := abs_add_le (-(l0 + l1 + l2 - Real.log |vs|) - (L + Real.log |vs|) - value d.toBits +
      (value c.toBits + value d.toBits - (value b.toBits + -l2))) (value r2.toBits - value c.toBits)
    have e2 := abs_add_le (-(l0 + l1 + l2 - Real.log |vs|) - (L + Real.log |vs|) - value d.toBits)
      (value c.toBits + value d.toBits - (value b.toBits + -l2))
    have e3 := abs_sub (-(l0 + l1 + l2 - Real.log |vs|) - (L + Real.log |vs|)) (value d.toBits)
    have e4 := abs_sub (-(l0 + l1 + l2 - Real.log |vs|)) (L + Real.log |vs|)
    rw [abs_neg] at e4
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 88 + 4 / 2 ^ 100 + 1 / 2 ^ 91 + 1 / 2 ^ 140 +
      1 / 2 ^ 90 ≤ 1 / 2 ^ 87)]
  have hLb : 69 ≤ |L| := by
    have h1 := abs_sub_abs_le_abs_sub (Real.log |vs|) (-L)
    rw [show Real.log |vs| - -L = L + Real.log |vs| by ring, abs_neg,
      abs_of_neg (by linarith : Real.log |vs| < 0)] at h1
    linarith [(by norm_num : (4 : ℝ) / 2 ^ 100 ≤ 1 / 100)]
  refine ⟨af, hr2f, ?_, ?_, ?_⟩
  · have := abs_le.mp hbb
    have h1 : |value r1.toBits| ≥ |l0 + l1| - |value b.toBits| := by
      have := abs_sub_abs_le_abs_sub (value r1.toBits + value b.toBits) (value b.toBits)
      rw [add_sub_cancel_right, hab, show -l0 + -l1 = -(l0 + l1) by ring, abs_neg] at this
      linarith
    have h2 : |l0 + l1| ≥ |l0| - |l1| := by
      have := abs_sub_abs_le_abs_sub l0 (-l1)
      rw [sub_neg_eq_add, abs_neg] at this
      linarith
    linarith [(by norm_num : (6930 : ℝ) / 100 - 1 / 2 ^ 41 - 1 / 2 ^ 41 ≥ 1)]
  · have := abs_sub_abs_le_abs_sub (value r2.toBits) (value c.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 41 + 1 / 2 ^ 60 + 1 / 2 ^ 90 ≤ 1 / 2 ^ 40)]
  · have : (1 : ℝ) / 2 ^ 87 ≤ |L| / 2 ^ 70 := by
      rw [le_div_iff₀ (by positivity)]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 87 * 2 ^ 70 ≤ 69)]
    linarith

set_option maxHeartbeats 8000000 in
/-- **The branch from `2^-100` to `1/4`.** -/
theorem low_spec (hF : FmaSpec.FmaNearest) (hLA : LgammaApprox.LogAccFact)
    (hAP : LgammaApprox.AccPolyFact) (sx : Float) (hsx : Finite sx.toBits)
    (hge : 1 / 2 ^ 100 ≤ |value sx.toBits|) (hlt : |value sx.toBits| < 1 / 4) :
    LowSpec (GammaBasic.lgamma (value sx.toBits))
      (low Tgamma.logdTable H Lgamma.accurateTable sx sx.abs) := by
  obtain ⟨haf, hav⟩ := SinhWords.abs_float sx hsx
  set vs := value sx.toBits with hvs
  have h0 : vs ≠ 0 := by
    intro h; rw [h, abs_zero] at hge; norm_num at hge
  have hvs0 : 0 < |vs| := abs_pos.mpr h0
  have hpos : 0 < value sx.abs.toBits := by rw [hav]; exact hvs0
  obtain ⟨-, hhi⟩ := log_range |vs| (le_trans (by norm_num) hge) hlt
  have hlo := log_low |vs| hge
  -- the polynomial `P (sx)`
  obtain ⟨p0f, p1f, hpe, hp1, hpm⟩ := LgammaAccPoly.acc_gen hF Lgamma.accurateTable 0 34 (1 / 4)
    (95 / 100) (83 / 100) (1 / 2 ^ 54) (1 / 2 ^ 43) (1 / 2 ^ 42) (1 / 2 ^ 89)
    LgammaAccPoly.small_ok 0 34 rfl rfl (by norm_num) sx hsx (by push_cast; linarith)
  push_cast at hpe hp1 hpm
  set ev := PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) vs with hev
  -- the reference: `log |Γ sx| = log Γ (1 + sx) - log |sx|`
  have hAP1 : |GammaBasic.lgamma (1 + vs) - vs * ev| ≤ 1 / 2 ^ 70 * |vs| :=
    hAP.1 vs (by linarith)
  have hnp : GammaBasic.NotPole vs :=
    GammaBasic.notPole_of_neg_one_lt (by linarith [abs_le.mp hlt.le]) h0
  have hrec := GammaBasic.lgamma_add_one hnp
  rw [← Real.log_abs, add_comm vs 1] at hrec
  set L := GammaBasic.lgamma vs
  set G := GammaBasic.lgamma (1 + vs)
  have hvev : |vs * ev| ≤ |vs| * (95 / 100) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hpm hvs0.le
  have hG : |G| ≤ |vs| * (95 / 100) + |vs| / 2 ^ 70 := by
    have := abs_sub_abs_le_abs_sub G (vs * ev)
    linarith
  have hLb : 114 / 100 ≤ |L| := by
    have h1 := abs_sub_abs_le_abs_sub (-Real.log |vs|) L
    rw [show -Real.log |vs| - L = -G by linarith, abs_neg, abs_neg,
      abs_of_neg (by linarith : Real.log |vs| < 0)] at h1
    linarith [(by norm_num : (1 : ℝ) / 4 * (95 / 100) + 1 / 4 / 2 ^ 70 ≤ 1386 / 1000 - 114 / 100)]
  unfold low
  generalize Lgamma.polyDDDFst Lgamma.accurateTable 0 34 sx 0.0 = P at p0f p1f hpe hp1
  obtain ⟨p0, p1⟩ := P
  dsimp only at p0f p1f hpe hp1 ⊢
  -- the product `sx P (sx)`
  have hp0 : |value p0.toBits| ≤ 96 / 100 := by
    have := abs_sub_abs_le_abs_sub (value p0.toBits + value p1.toBits) ev
    have h2 := abs_sub_abs_le_abs_sub (value p0.toBits) (-value p1.toBits)
    rw [sub_neg_eq_add, abs_neg] at h2
    linarith [(by norm_num : (95 : ℝ) / 100 + 1 / 2 ^ 89 + 1 / 2 ^ 43 + 1 / 2 ^ 43 ≤ 96 / 100)]
  obtain ⟨m0f, m1f, hme, hm1, hm0⟩ := mulDDD_spec hF sx p0 p1 hsx p0f p1f (96 / 100 * |vs|)
    (|vs| / 2 ^ 43)
    (by rw [← hvs]; have := mul_le_mul_of_nonneg_right hp0 (abs_nonneg vs); linarith)
    (by rw [← hvs]; have := mul_le_mul_of_nonneg_right hp1 (abs_nonneg vs); linarith)
    (by linarith [(by norm_num : (96 : ℝ) / 100 * (1 / 4) ≤ 2 ^ 900)])
    (by linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 43 ≤ 2 ^ 900)])
  try rw [← hvs] at hme
  generalize mulDDD sx p0 p1 = M at m0f m1f hme hm1 hm0
  obtain ⟨m0, m1⟩ := M
  dsimp only at m0f m1f hme hm1 hm0 ⊢
  have htiny : (1 : ℝ) / 2 ^ 1071 ≤ |vs| / 2 ^ 900 := by
    have := div_le_div_of_nonneg_right hge (by norm_num : (0 : ℝ) ≤ 2 ^ 900)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1071 ≤ 1 / 2 ^ 100 / 2 ^ 900)]
  have hEM : |value m0.toBits + value m1.toBits - G| ≤ |vs| / 2 ^ 69 := by
    have h1 : |vs * (value p0.toBits + value p1.toBits) - vs * ev| ≤ |vs| / 2 ^ 89 := by
      rw [← mul_sub, abs_mul]
      have := mul_le_mul_of_nonneg_left hpe hvs0.le
      linarith
    have h2 := abs_sub_le (value m0.toBits + value m1.toBits) (vs * (value p0.toBits + value p1.toBits))
      (vs * ev)
    have h3 := abs_sub_le (value m0.toBits + value m1.toBits) (vs * ev) G
    rw [abs_sub_comm (vs * ev) G] at h3
    have h4 : (3 * (|vs| / 2 ^ 43) + 96 / 100 * |vs| / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 +
        |vs| / 2 ^ 89 + 1 / 2 ^ 70 * |vs| ≤ |vs| / 2 ^ 69 := by
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1072 ≤ 1 / 2 ^ 1071)]
    linarith
  have hm1' : |value m1.toBits| ≤ 1 / 2 ^ 44 := by
    have : |vs| / 2 ^ 43 * (1 + 1 / 2 ^ 51) + 96 / 100 * |vs| / 2 ^ 52 + 1 / 2 ^ 1071 ≤
        1 / 2 ^ 44 := by
      linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 43 * (1 + 1 / 2 ^ 51) + 96 / 100 * (1 / 4) / 2 ^ 52 +
        1 / 2 ^ 1071 ≤ 1 / 2 ^ 44)]
    linarith
  have hm0' : |value m0.toBits| ≤ 1 / 4 := by
    linarith [(by norm_num : (96 : ℝ) / 100 * (1 / 4) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ 1 / 4)]
  -- the logarithm of `x = |sx|`
  obtain ⟨t1f, t2f, t3f, te, t2b, t3b⟩ := LgammaLogdAcc.acc_abs hF hLA sx.abs haf hpos
  rw [hav] at te
  generalize Lgamma.asLogdAccurate Tgamma.logdTable H sx.abs = T at t1f t2f t3f te t2b t3b
  obtain ⟨lh, ll, lll⟩ := T
  dsimp only at t1f t2f t3f te t2b t3b ⊢
  set l0 := value lh.toBits
  set l1 := value ll.toBits
  set l2 := value lll.toBits
  have hl0a : |l0| ≤ 70 := by
    have h3 : |l0| ≤ 6932 / 100 + 1 / 2 ^ 88 + |l1| + |l2| := by
      have := abs_add_le (l0 + l1 + l2 - Real.log |vs|) (-(l1 + l2) + Real.log |vs|)
      have h4 := abs_add_le (-(l1 + l2)) (Real.log |vs|)
      have h5 := abs_add_le l1 l2
      rw [show l0 + l1 + l2 - Real.log |vs| + (-(l1 + l2) + Real.log |vs|) = l0 by ring] at this
      rw [abs_neg, abs_of_neg (by linarith : Real.log |vs| < 0)] at h4
      linarith
    linarith
  have hl1 : |l1| ≤ 1 / 2 ^ 44 := by
    have := div_le_div_of_nonneg_right hl0a (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    linarith [(by norm_num : (70 : ℝ) / 2 ^ 51 + 1 / 2 ^ 50 ≤ 1 / 2 ^ 44)]
  have hl2 : |l2| ≤ 1 / 2 ^ 93 := by
    have := div_le_div_of_nonneg_right hl0a (by norm_num : (0 : ℝ) ≤ 2 ^ 100)
    linarith [(by norm_num : (70 : ℝ) / 2 ^ 100 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 93)]
  obtain ⟨n0f, n0v⟩ := neg_float lh t1f
  obtain ⟨n1f, n1v⟩ := neg_float ll t2f
  obtain ⟨n2f, n2v⟩ := neg_float lll t3f
  -- `sumDD`
  obtain ⟨s0f, s1f, hse, hs1, hs0⟩ := sumDD_spec m0 m1 (-ll) (-lll) m0f m1f n1f n2f
    (by linarith [(by norm_num : (1 : ℝ) / 4 < 2 ^ 898)])
    (by rw [n1v, abs_neg]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 44 < 2 ^ 898)])
    (1 / 2 ^ 43) (by rw [n2v, abs_neg]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 44 + 1 / 2 ^ 93 ≤
      1 / 2 ^ 43)]) (by norm_num)
  generalize sumDD m0 m1 (-ll) (-lll) = S at s0f s1f hse hs1 hs0
  obtain ⟨s0, s1⟩ := S
  dsimp only at s0f s1f hse hs1 hs0 ⊢
  rw [n1v, n2v] at hse
  rw [n1v] at hs0
  have hs0' : |value s0.toBits| ≤ 26 / 100 := by
    have := abs_add_le (value m0.toBits) (-l1)
    rw [abs_neg] at this
    nlinarith [(by norm_num : ((1 : ℝ) / 4 + 1 / 2 ^ 44) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤
      26 / 100)]
  have hse' : |value s0.toBits + value s1.toBits - (value m0.toBits + value m1.toBits + (-l1 + -l2))|
      ≤ 1 / 2 ^ 94 := by
    linarith [(by norm_num : (3 * (1 / 2 ^ 43) + 26 / 100 / 2 ^ 52 + 1 / 2 ^ 1074 : ℝ) / 2 ^ 53 ≤
      1 / 2 ^ 94)]
  have hs1' : |value s1.toBits| ≤ 1 / 2 ^ 42 := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 * (1 + 1 / 2 ^ 51) + 26 / 100 / 2 ^ 51 + 1 / 2 ^ 1073 ≤
      1 / 2 ^ 42)]
  -- `twoSum (-lh) s0`
  obtain ⟨u0f, u1f, hu, hu1⟩ := twoSum_spec (-lh) s0 n0f s0f
    (by rw [n0v, abs_neg]; linarith [(by norm_num : (70 : ℝ) < 2 ^ 900)])
    (by linarith [(by norm_num : (26 : ℝ) / 100 < 2 ^ 900)])
  generalize twoSum (-lh) s0 = U at u0f u1f hu hu1
  obtain ⟨u0, u1⟩ := U
  dsimp only at u0f u1f hu hu1 ⊢
  rw [n0v] at hu
  have hu0 : |value u0.toBits| ≤ 71 := by
    have h1 := abs_add_le (value u0.toBits + value u1.toBits) (-value u1.toBits)
    rw [add_neg_cancel_right, abs_neg, hu] at h1
    have h2 := abs_add_le (-l0) (value s0.toBits)
    rw [abs_neg] at h2
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 100)]
  have hu1' : |value u1.toBits| ≤ 1 / 2 ^ 45 := by
    have := div_le_div_of_nonneg_right hu0 (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
    linarith [(by norm_num : (71 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 45)]
  -- `twoSum u1 s1`
  obtain ⟨v0f, v1f, hv, hv1⟩ := twoSum_spec u1 s1 u1f s1f
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 45 < 2 ^ 900)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 42 < 2 ^ 900)])
  generalize twoSum u1 s1 = V at v0f v1f hv hv1
  obtain ⟨v0, v1⟩ := V
  dsimp only at v0f v1f hv hv1 ⊢
  have hv0 : |value v0.toBits| ≤ 1 / 2 ^ 41 := by
    have h1 := abs_add_le (value v0.toBits + value v1.toBits) (-value v1.toBits)
    rw [add_neg_cancel_right, abs_neg, hv] at h1
    have h2 := abs_add_le (value u1.toBits) (value s1.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 45 + 1 / 2 ^ 42 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 41 * (1 - 1 / 2 ^ 52))]
  have hv1' : |value v1.toBits| ≤ 1 / 2 ^ 92 := by
    have := div_le_div_of_nonneg_right hv0 (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 41 / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 92)]
  -- `adjust`
  obtain ⟨hr1, hr2f, hr2⟩ := adjust_spec u0 v0 v1 v0f (hv0.trans (by norm_num))
  generalize adjust u0 v0 v1 = R at hr1 hr2f hr2
  obtain ⟨r1, r2⟩ := R
  dsimp only at hr1 hr2f hr2
  subst hr1
  have hw : |value r2.toBits - value v0.toBits| ≤ 1 / 2 ^ 91 := by
    have := div_le_div_of_nonneg_right hv0 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 41 / 2 ^ 51 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 91)]
  have herr : |value r1.toBits + value r2.toBits - L| ≤ 1 / 2 ^ 71 + 1 / 2 ^ 86 := by
    have key : value r1.toBits + value r2.toBits - L =
        (value m0.toBits + value m1.toBits - G) - (l0 + l1 + l2 - Real.log |vs|) +
          (value s0.toBits + value s1.toBits - (value m0.toBits + value m1.toBits + (-l1 + -l2))) -
          value v1.toBits + (value r2.toBits - value v0.toBits) := by linarith
    rw [key]
    have e1 := abs_add_le ((value m0.toBits + value m1.toBits - G) - (l0 + l1 + l2 - Real.log |vs|) +
      (value s0.toBits + value s1.toBits - (value m0.toBits + value m1.toBits + (-l1 + -l2))) -
      value v1.toBits) (value r2.toBits - value v0.toBits)
    have e2 := abs_sub ((value m0.toBits + value m1.toBits - G) - (l0 + l1 + l2 - Real.log |vs|) +
      (value s0.toBits + value s1.toBits - (value m0.toBits + value m1.toBits + (-l1 + -l2))))
      (value v1.toBits)
    have e3 := abs_add_le ((value m0.toBits + value m1.toBits - G) - (l0 + l1 + l2 - Real.log |vs|))
      (value s0.toBits + value s1.toBits - (value m0.toBits + value m1.toBits + (-l1 + -l2)))
    have e4 := abs_sub (value m0.toBits + value m1.toBits - G) (l0 + l1 + l2 - Real.log |vs|)
    have hEM' : |vs| / 2 ^ 69 ≤ 1 / 2 ^ 71 := by
      have := div_le_div_of_nonneg_right hlt.le (by norm_num : (0 : ℝ) ≤ 2 ^ 69)
      linarith [(by norm_num : (1 : ℝ) / 4 / 2 ^ 69 = 1 / 2 ^ 71)]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 88 + 1 / 2 ^ 94 + 1 / 2 ^ 92 + 1 / 2 ^ 91 ≤ 1 / 2 ^ 86)]
  have hr2b := abs_sub_abs_le_abs_sub (value r2.toBits) (value v0.toBits)
  refine ⟨u0f, hr2f, ?_, ?_, ?_⟩
  · have h1 := abs_sub_abs_le_abs_sub L (L - (value r1.toBits + value r2.toBits))
    rw [sub_sub_cancel, abs_sub_comm] at h1
    have h2 := abs_add_le (value r1.toBits) (value r2.toBits)
    linarith [(by norm_num : (114 : ℝ) / 100 - (1 / 2 ^ 71 + 1 / 2 ^ 86) - (1 / 2 ^ 41 + 1 / 2 ^ 91) ≥ 1)]
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 41 + 1 / 2 ^ 91 ≤ 1 / 2 ^ 40)]
  · have : (1 : ℝ) / 2 ^ 71 + 1 / 2 ^ 86 ≤ |L| / 2 ^ 70 := by
      rw [le_div_iff₀ (by positivity)]
      linarith [(by norm_num : ((1 : ℝ) / 2 ^ 71 + 1 / 2 ^ 86) * 2 ^ 70 ≤ 114 / 100)]
    linarith

#print axioms adjust_spec
#print axioms tiny_spec
#print axioms low_spec

end Verified.Examples.LgammaAccLow
