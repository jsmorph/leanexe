import Verified.Examples.TgammaExpRed
import Verified.Examples.TgammaExpr
import Verified.Examples.TgammaPolyDDD
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
The kernel of **`Tgamma.asExpd`**, toward the specification for `1 ≤ x + l ≤ 1000` and
`|l| ≤ 2 ^ -14` in `TgammaExpdSpec`.  With `K = 1024 E + 32 i0 + i1` the nearest integer to `(x + l) 1024/ln 2` and
`X = q1 + q2` the remainder (`TgammaExpRed`), `exp (x + l) = 2 ^ E exp (i0 ln 2/32)
exp (i1 ln 2/1024) exp (X ln 2/1024)`.  The tables give the middle factors to `2 ^ -80`
(`ExpFact`), the kernel `1 + q1 expPoly q1` gives the last factor at `q1` to `2 ^ -74`, and the
code's evaluation of that kernel lies within `2 ^ -61` of it (`exp_poly`).
-/

namespace Verified.Examples.TgammaExpd
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaExpr TgammaWords
  TgammaMainRed TgammaFloor TgammaRecip TgammaExpRed TgammaPolyDDD

set_option exponentiation.threshold 4096

def ew (i : ℕ) : UInt64 := expdTable[i]!

theorem ew_finite : ∀ k < 138, Wasm.IEEE64.isFinite expdTable[k]! = true := by decide +kernel

/-- `y (c130 + y (c132 + y (c134 + y c136)))`, the tail of the kernel. -/
def pE : FE :=
  .mul .var (.add (.const (ew 130)) (.mul .var (.add (.const (ew 132))
    (.mul .var (.add (.const (ew 134)) (.mul .var (.const (ew 136))))))))

def Xq : ℚ := 5 / 8

theorem pE_ok : ok pE Xq = true := by decide +kernel

theorem pE_err : (bnd pE Xq).2 ≤ 1 / 2 ^ 74 := by decide +kernel

theorem pE_mag : (bnd pE Xq).1 ≤ 1 / 2 ^ 22 := by decide +kernel

theorem pfl_eq (y : Float) :
    evalF pE y = y * (entry expdTable 130 + y * (entry expdTable 132 +
      y * (entry expdTable 134 + y * entry expdTable 136))) := by
  simp only [evalF, pE]
  rfl

theorem expPoly_eq (y : ℝ) :
    TgammaApprox.expPoly y =
      ((TgammaApprox.q expdTable 128 + TgammaApprox.q expdTable 129 : ℚ) : ℝ) + evalR pE y := by
  rw [TgammaApprox.expPoly, PolyBound.eval, eval_coeffs]
  simp only [evalR, pE, ew, TgammaApprox.q, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.reduceMul, Nat.reduceAdd, zero_add, pow_zero, pow_one, mul_one]
  ring

theorem wv (k : ℕ) (hk : k < 138) :
    value (Float.ofBits expdTable[k]!).toBits = (PolyBound.ratOfWord expdTable[k]! : ℝ) :=
  ofBits_value _ (ew_finite k hk)

theorem wf (k : ℕ) (hk : k < 138) : Finite (Float.ofBits expdTable[k]!).toBits :=
  ofBits_finite _ (ew_finite k hk)

theorem ev (i : UInt64) (k : ℕ) (h : i.toNat = k) (hk : k < 138) :
    value (entry expdTable i).toBits = (PolyBound.ratOfWord expdTable[k]! : ℝ) := by
  rw [entry_eq _ _ k h]; exact wv k hk

theorem ef (i : UInt64) (k : ℕ) (h : i.toNat = k) (hk : k < 138) :
    Finite (entry expdTable i).toBits := by
  rw [entry_eq _ _ k h]; exact wf k hk

theorem c128_lo : (1 : ℚ) / 1480 ≤ PolyBound.ratOfWord expdTable[128]! := by decide +kernel
theorem c128_hi : PolyBound.ratOfWord expdTable[128]! ≤ 1 / 1470 := by decide +kernel
theorem c129_le : PolyBound.qabs (PolyBound.ratOfWord expdTable[129]!) ≤ 1 / 2 ^ 65 := by
  decide +kernel

/-- **The kernel** `1 + q1 expPoly q1` as the code evaluates it. -/
theorem exp_poly (hF : FmaSpec.FmaNearest) (q1 q2 : Float) (hq1f : Finite q1.toBits)
    (hq2f : Finite q2.toBits) (hq1 : |value q1.toBits| ≤ 5 / 8)
    (hq2 : |value q2.toBits| ≤ 1 / 2 ^ 52) :
    Finite (fastTwoSum 1.0 (mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).1).1.toBits ∧
      Finite ((mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).2 +
        (fastTwoSum 1.0 (mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).1).2).toBits ∧
      |value (fastTwoSum 1.0 (mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
          ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).1).1.toBits +
        value ((mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
          ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).2 +
          (fastTwoSum 1.0 (mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
          ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).1).2).toBits -
        (1 + value q1.toBits * TgammaApprox.expPoly (value q1.toBits))| ≤ 1 / 2 ^ 61 ∧
      |value (fastTwoSum 1.0 (mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).1).1.toBits| ≤ 2 ∧
      |value ((mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).2 +
        (fastTwoSum 1.0 (mulDD q1 q2 (fastTwoSum (entry expdTable 128) (evalF pE q1)).1
        ((fastTwoSum (entry expdTable 128) (evalF pE q1)).2 + entry expdTable 129)).1).2).toBits| ≤
        1 / 2 ^ 49 := by
  -- the tail in double arithmetic
  have hq1' : |value q1.toBits| ≤ (Xq : ℝ) := by rw [Xq]; push_cast; exact hq1
  obtain ⟨hfl, hflm⟩ := evalF_approx pE Xq q1 hq1f hq1' pE_ok
  have hfle : |value (evalF pE q1).toBits - evalR pE (value q1.toBits)| ≤ 1 / 2 ^ 74 := by
    have h := hfl.2
    have : ((bnd pE Xq).2 : ℝ) ≤ ((1 / 2 ^ 74 : ℚ) : ℝ) := by exact_mod_cast pE_err
    push_cast at this
    linarith
  have hPm : |evalR pE (value q1.toBits)| ≤ 1 / 2 ^ 22 := by
    have : ((bnd pE Xq).1 : ℝ) ≤ ((1 / 2 ^ 22 : ℚ) : ℝ) := by exact_mod_cast pE_mag
    push_cast at this
    linarith
  have hflb : |value (evalF pE q1).toBits| ≤ 1 / 2 ^ 21 := by
    have := abs_sub_abs_le_abs_sub (value (evalF pE q1).toBits) (evalR pE (value q1.toBits))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 22 + 1 / 2 ^ 74 ≤ 1 / 2 ^ 21)]
  -- the constants
  have h128v := ev 128 128 rfl (by norm_num)
  have h129v := ev 129 129 rfl (by norm_num)
  have h128f := ef 128 128 rfl (by norm_num)
  have h129f := ef 129 129 rfl (by norm_num)
  set c128 := (PolyBound.ratOfWord expdTable[128]! : ℝ) with hc128
  set c129 := (PolyBound.ratOfWord expdTable[129]! : ℝ) with hc129
  have hc128lo : 1 / 1480 ≤ c128 := by
    have : ((1 / 1480 : ℚ) : ℝ) ≤ c128 := by rw [hc128]; exact_mod_cast c128_lo
    push_cast at this; exact this
  have hc128hi : c128 ≤ 1 / 1470 := by
    have : c128 ≤ ((1 / 1470 : ℚ) : ℝ) := by rw [hc128]; exact_mod_cast c128_hi
    push_cast at this; exact this
  have hc129b : |c129| ≤ 1 / 2 ^ 65 := by
    have := TgammaSmall.abs_rat_le _ _ c129_le
    push_cast at this; exact this
  -- `a = fastTwoSum c128 fl`
  obtain ⟨ha1f, ha2f, hasum, -, ha2b⟩ := fastTwoSum_spec (entry expdTable 128) (evalF pE q1) h128f
    hfl.1 (by rw [h128v, abs_of_pos (show (0 : ℝ) < c128 by linarith)]
              linarith [(by norm_num : (1 : ℝ) / 2 ^ 21 ≤ 1 / 1480)])
    (by rw [h128v, abs_of_pos (show (0 : ℝ) < c128 by linarith)]
        linarith [(by norm_num : (1 : ℝ) / 1470 < 2 ^ 900)])
  rw [h128v] at hasum
  set a := fastTwoSum (entry expdTable 128) (evalF pE q1) with hadef
  have ha1b : |value a.1.toBits| ≤ 1 / 2 ^ 10 := by
    have h1 := abs_add_le (value a.1.toBits + value a.2.toBits) (-value a.2.toBits)
    rw [add_neg_cancel_right, abs_neg, hasum] at h1
    have h2 := abs_add_le c128 (value (evalF pE q1).toBits)
    rw [abs_of_pos (by linarith : (0 : ℝ) < c128)] at h2
    linarith [(by norm_num : (1 : ℝ) / 1470 + 1 / 2 ^ 21 + (1 / 2 ^ 10 / 2 ^ 52 + 1 / 2 ^ 1074) ≤
      1 / 2 ^ 10)]
  have ha2 : |value a.2.toBits| ≤ 1 / 2 ^ 61 := by
    have : |value a.1.toBits| / 2 ^ 52 ≤ 1 / 2 ^ 10 / 2 ^ 52 :=
      div_le_div_of_nonneg_right ha1b (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 10 / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 61)]
  -- `a2' = a.2 + c129`
  have ha2' := fapprox_add (fapprox_self a.2 ha2f) (fapprox_self _ h129f) (1 / 2 ^ 60)
    (by rw [h129v, add_zero, add_zero]; linarith [abs_add_le (value a.2.toBits) c129,
      (by norm_num : (1 : ℝ) / 2 ^ 61 + 1 / 2 ^ 65 ≤ 1 / 2 ^ 60)])
    (by norm_num)
  rw [h129v] at ha2'
  set a2' := a.2 + entry expdTable 129 with ha2'def
  have ha2'e : |value a2'.toBits - (value a.2.toBits + c129)| ≤ 1 / 2 ^ 113 := by
    have := ha2'.2; linarith [(by norm_num : (0 : ℝ) + 0 + 1 / 2 ^ 60 / 2 ^ 53 = 1 / 2 ^ 113)]
  have ha2'b : |value a2'.toBits| ≤ 1 / 2 ^ 60 := by
    have := abs_sub_abs_le_abs_sub (value a2'.toBits) (value a.2.toBits + c129)
    linarith [abs_add_le (value a.2.toBits) c129, (by norm_num : (1 : ℝ) / 2 ^ 61 + 1 / 2 ^ 65 +
      1 / 2 ^ 113 ≤ 1 / 2 ^ 60)]
  -- `b = mulDD q1 q2 a.1 a2'`
  have hq10 := abs_nonneg (value q1.toBits)
  have hq20 := abs_nonneg (value q2.toBits)
  obtain ⟨hb1f, hb2f, hbe, hb2b, hb1b⟩ := mulDD_spec hF q1 q2 a.1 a2' hq1f hq2f ha1f ha2'.1
    (1 / 2 ^ 10 * 1) (1 / 2 ^ 10 * (1 / 2 ^ 52)) (1 / 2 ^ 60 * 1) (1 / 2 ^ 60 * (1 / 2 ^ 52))
    (mul_le_mul ha1b (by linarith) hq10 (by norm_num))
    (mul_le_mul ha1b hq2 hq20 (by norm_num))
    (mul_le_mul ha2'b (by linarith) hq10 (by norm_num))
    (mul_le_mul ha2'b hq2 hq20 (by norm_num)) (by norm_num) (by norm_num)
  set b := mulDD q1 q2 a.1 a2' with hbdef
  -- `c = fastTwoSum 1 b.1`
  obtain ⟨hc1f, hc2f, hcsum, -, hc2b⟩ := fastTwoSum_spec 1.0 b.1 one_finite hb1f
    (by rw [one_value, abs_one]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 10 * 1 * (1 + 1 / 2 ^ 53) +
      1 / 2 ^ 1075 ≤ 1)])
    (by rw [one_value, abs_one]; norm_num)
  rw [one_value] at hcsum
  set c := fastTwoSum 1.0 b.1 with hcdef
  have hc1b : |value c.1.toBits| ≤ 2 := by
    have h1 := abs_add_le (value c.1.toBits + value c.2.toBits) (-value c.2.toBits)
    rw [add_neg_cancel_right, abs_neg, hcsum] at h1
    have h2 := abs_add_le (1 : ℝ) (value b.1.toBits)
    rw [abs_one] at h2
    linarith [(by norm_num : (1 : ℝ) + (1 / 2 ^ 10 * 1 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075) +
      (2 / 2 ^ 52 + 1 / 2 ^ 1074) ≤ 2)]
  have hc2 : |value c.2.toBits| ≤ 1 / 2 ^ 50 := by
    have : |value c.1.toBits| / 2 ^ 52 ≤ 2 / 2 ^ 52 := div_le_div_of_nonneg_right hc1b (by norm_num)
    linarith [(by norm_num : (2 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 50)]
  -- `e = b.2 + c.2`
  have hb2 : |value b.2.toBits| ≤ 1 / 2 ^ 59 := by
    refine hb2b.trans ?_
    norm_num
  have he := fapprox_add (fapprox_self b.2 hb2f) (fapprox_self c.2 hc2f) (1 / 2 ^ 49)
    (by rw [add_zero, add_zero]; linarith [abs_add_le (value b.2.toBits) (value c.2.toBits),
      (by norm_num : (1 : ℝ) / 2 ^ 59 + 1 / 2 ^ 50 ≤ 1 / 2 ^ 49)])
    (by norm_num)
  have hee : |value (b.2 + c.2).toBits - (value b.2.toBits + value c.2.toBits)| ≤ 1 / 2 ^ 102 := by
    have := he.2; linarith [(by norm_num : (0 : ℝ) + 0 + 1 / 2 ^ 49 / 2 ^ 53 = 1 / 2 ^ 102)]
  refine ⟨hc1f, he.1, ?_, hc1b, ?_⟩
  · -- the error
    rw [expPoly_eq]
    simp only [TgammaApprox.q]
    push_cast
    rw [← hc128, ← hc129]
    set X := value q1.toBits
    set Y := value q2.toBits
    set P := evalR pE X
    set fl := value (evalF pE q1).toBits
    have hbe' : |value b.1.toBits + value b.2.toBits - (X + Y) * (value a.1.toBits + value a2'.toBits)| ≤
        1 / 2 ^ 110 := by
      refine hbe.trans ?_
      norm_num
    have hsplit : value c.1.toBits + value (b.2 + c.2).toBits - (1 + X * (c128 + c129 + P)) =
        (value c.1.toBits + value c.2.toBits - (1 + value b.1.toBits)) +
        (value (b.2 + c.2).toBits - (value b.2.toBits + value c.2.toBits)) +
        (value b.1.toBits + value b.2.toBits - (X + Y) * (value a.1.toBits + value a2'.toBits)) +
        (X + Y) * (value a2'.toBits - (value a.2.toBits + c129)) +
        X * (fl - P) + Y * (c128 + fl + c129) := by
      linear_combination (X + Y) * hasum
    rw [hsplit, hcsum, sub_self, zero_add]
    have e1 := abs_add_le ((value (b.2 + c.2).toBits - (value b.2.toBits + value c.2.toBits)) +
        (value b.1.toBits + value b.2.toBits - (X + Y) * (value a.1.toBits + value a2'.toBits)) +
        (X + Y) * (value a2'.toBits - (value a.2.toBits + c129)) + X * (fl - P))
      (Y * (c128 + fl + c129))
    have e2 := abs_add_le ((value (b.2 + c.2).toBits - (value b.2.toBits + value c.2.toBits)) +
        (value b.1.toBits + value b.2.toBits - (X + Y) * (value a.1.toBits + value a2'.toBits)) +
        (X + Y) * (value a2'.toBits - (value a.2.toBits + c129))) (X * (fl - P))
    have e3 := abs_add_le ((value (b.2 + c.2).toBits - (value b.2.toBits + value c.2.toBits)) +
        (value b.1.toBits + value b.2.toBits - (X + Y) * (value a.1.toBits + value a2'.toBits)))
      ((X + Y) * (value a2'.toBits - (value a.2.toBits + c129)))
    have e4 := abs_add_le (value (b.2 + c.2).toBits - (value b.2.toBits + value c.2.toBits))
      (value b.1.toBits + value b.2.toBits - (X + Y) * (value a.1.toBits + value a2'.toBits))
    have hXY : |X + Y| ≤ 1 := by
      linarith [abs_add_le X Y, (by norm_num : (5 : ℝ) / 8 + 1 / 2 ^ 52 ≤ 1)]
    have f1 : |(X + Y) * (value a2'.toBits - (value a.2.toBits + c129))| ≤ 1 / 2 ^ 113 := by
      rw [abs_mul]
      calc |X + Y| * |value a2'.toBits - (value a.2.toBits + c129)| ≤ 1 * (1 / 2 ^ 113) :=
            mul_le_mul hXY ha2'e (abs_nonneg _) (by norm_num)
        _ = 1 / 2 ^ 113 := by ring
    have f2 : |X * (fl - P)| ≤ 1 / 2 ^ 74 := by
      rw [abs_mul]
      calc |X| * |fl - P| ≤ 1 * (1 / 2 ^ 74) :=
            mul_le_mul (by linarith [(by norm_num : (5 : ℝ) / 8 ≤ 1)]) hfle
              (abs_nonneg _) (by norm_num)
        _ = 1 / 2 ^ 74 := by ring
    have f3 : |Y * (c128 + fl + c129)| ≤ 1 / 2 ^ 62 := by
      rw [abs_mul]
      have : |c128 + fl + c129| ≤ 1 / 2 ^ 10 := by
        have h1 := abs_add_le (c128 + fl) c129
        have h2 := abs_add_le c128 fl
        rw [abs_of_pos (by linarith : (0 : ℝ) < c128)] at h2
        linarith [(by norm_num : (1 : ℝ) / 1470 + 1 / 2 ^ 21 + 1 / 2 ^ 65 ≤ 1 / 2 ^ 10)]
      calc |Y| * |c128 + fl + c129| ≤ 1 / 2 ^ 52 * (1 / 2 ^ 10) :=
            mul_le_mul hq2 this (abs_nonneg _) (by norm_num)
        _ = 1 / 2 ^ 62 := by norm_num
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 102 + 1 / 2 ^ 110 + 1 / 2 ^ 113 + 1 / 2 ^ 74 + 1 / 2 ^ 62 ≤
      1 / 2 ^ 61)]
  · have := abs_sub_abs_le_abs_sub (value (b.2 + c.2).toBits) (value b.2.toBits + value c.2.toBits)
    linarith [abs_add_le (value b.2.toBits) (value c.2.toBits), (by norm_num : (1 : ℝ) / 2 ^ 59 +
      1 / 2 ^ 50 + 1 / 2 ^ 102 ≤ 1 / 2 ^ 49)]

#print axioms exp_poly

end Verified.Examples.TgammaExpd
