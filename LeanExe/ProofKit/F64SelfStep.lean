import LeanExe.ProofKit.F64RelativeStep
import LeanExe.ProofKit.F64SignedNearestSum

/-!
A finite word within `2 ^ -54` of a number, relative to the word, lies within one step of the
number's nearest-even reference, and a zero word lies within one step of zero.  The ports of
`sin` and `tan` return `x` itself for tiny `x`, where `|sin x - x| ≤ |x| ^ 3 / 6` and
`|tan x - x| ≤ |x| ^ 3` meet the first bound.
-/

namespace LeanExe.ProofKit.F64SelfStep

open CodeLib.IEEE64

set_option exponentiation.threshold 1200

theorem pow_div (n : Nat) :
    (2 : ℝ) ^ (n + 54) / 2 ^ 1074 / 2 ^ 54 = (2 : ℝ) ^ n / 2 ^ 1074 := by
  rw [pow_add]
  field_simp

/-- `self_step` for a positive word. -/
theorem self_step_pos (c : UInt64) (y : ℝ) (hcf : Finite c) (hc0 : 0 < value c)
    (hc1 : value c ≤ 1) (hy : |value c - y| ≤ value c / 2 ^ 54) :
    F64SignedRounding.WithinSteps 1 y c := by
  set a := Wasm.IEEE64.exponent c with ha
  have hlt : a < 2048 := Nat.mod_lt _ (by norm_num)
  have hcb := F64SignedNearestSum.grid_bound c
  rw [abs_of_pos hc0] at hcb
  have ha1023 : a ≤ 1023 := by
    by_contra h
    have hl := F64SignedNearestSum.grid_lower c (by omega)
    rw [abs_of_pos hc0] at hl
    have : (2 : ℝ) ≤ 2 ^ (52 + (a - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), ← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hy' := abs_le.mp hy
  have hyl : value c - value c / 2 ^ 54 ≤ y := by linarith
  have hyu : y ≤ value c + value c / 2 ^ 54 := by linarith
  have hc63 := F64PositiveOrder.positive_finite_encoding c hcf hc0
  have hlim : F64NearestNonnegative.limit = 0x7FF0000000000000 := rfl
  have hU := F64PositiveSpacing.boundary_value (a + 3) (by omega) (by omega)
  -- The upper boundary `2 ^ (a + 54)` lies above twice `c`.
  have hcU : value c ≤ 2 ^ (a + 3 + 51) / 2 ^ 1074 / 2 := by
    have : (2 : ℝ) ^ (53 + (a - 1)) / 2 ^ 1074 ≤ 2 ^ (a + 3 + 51) / 2 ^ 1074 / 2 := by
      rw [div_div, show (2 : ℝ) ^ 1074 * 2 = 2 ^ 1075 by rw [← pow_succ],
        div_le_div_iff₀ (by positivity) (by positivity), ← pow_add, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hpos : (0 : ℝ) < 2 ^ (a + 3 + 51) / 2 ^ 1074 := by positivity
  rcases Nat.lt_or_ge a 2 with hsmall | hbig
  · -- `c` below `2 ^ -1021`: the spacing is `2 ^ -1074`.
    have h0 : value (UInt64.ofNat (0 * 2 ^ 52)) = 0 := by
      have hs : Wasm.IEEE64.scaledValue (UInt64.ofNat (0 * 2 ^ 52)) = 0 := by decide
      show (Wasm.IEEE64.scaledValue (UInt64.ofNat (0 * 2 ^ 52)) : ℝ) / 2 ^ 1074 = 0
      rw [hs]
      simp
    have hcs : value c / 2 ^ 54 < 1 / 2 ^ 1074 := by
      have : (2 : ℝ) ^ (53 + (a - 1)) / 2 ^ 1074 ≤ 2 ^ 53 / 2 ^ 1074 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
      rw [div_lt_iff₀ (by positivity)]
      have h54 : (1 : ℝ) / 2 ^ 1074 * 2 ^ 54 = 2 ^ 54 / 2 ^ 1074 := by ring
      rw [h54]
      have : (2 : ℝ) ^ 53 / 2 ^ 1074 < 2 ^ 54 / 2 ^ 1074 :=
        div_lt_div_of_pos_right (pow_lt_pow_right₀ (by norm_num) (by norm_num)) (by positivity)
      linarith
    have hhalf : value c / 2 ^ 54 ≤ value c / 2 :=
      div_le_div_of_nonneg_left hc0.le (by norm_num) (by norm_num)
    have hself : value c / 2 ^ 54 ≤ value c := div_le_self hc0.le (by norm_num)
    have hy0 : 0 ≤ y := by linarith
    have h := F64FullStep.one_step_binades y c 0 (a + 3) (by omega) (by omega)
      (by rw [h0]; exact hy0) (fun _ => by rw [hU]; linarith)
      (lt_trans hc63 (by decide)) (by rw [h0]; exact hc0.le) (by rw [hU]; linarith)
      (by
        norm_num
        rw [abs_lt]
        rw [abs_le] at hy
        constructor <;> linarith)
    exact F64SignedRounding.within_of_nonneg 1 y hy0 c (by rw [hlim] at hc63; omega) h.1 h.2
  · -- `c` in binade `a ≥ 2`: binade `a - 1` lies below `c / 2`.
    have hl := F64SignedNearestSum.grid_lower c (by omega)
    rw [abs_of_pos hc0] at hl
    have hL := F64PositiveSpacing.boundary_value (a - 1) (by omega) (by omega)
    have hLc : 2 ^ (a - 1 + 51) / 2 ^ 1074 ≤ value c / 2 := by
      have : (2 : ℝ) ^ (a - 1 + 51) / 2 ^ 1074 * 2 = 2 ^ (52 + (a - 1)) / 2 ^ 1074 := by
        rw [div_mul_eq_mul_div, ← pow_succ]
        congr 2
        omega
      linarith
    have hsp : value c / 2 ^ 54 < (2 : ℝ) ^ (a - 1 - 1) / 2 ^ 1074 := by
      have h1 : (2 : ℝ) ^ (53 + (a - 1)) = 2 ^ (a - 1 - 1 + 54) := by congr 1; omega
      rw [h1] at hcb
      have := div_lt_div_of_pos_right hcb (show (0 : ℝ) < 2 ^ 54 by positivity)
      rwa [pow_div] at this
    have hhalf : value c / 2 ^ 54 ≤ value c / 2 :=
      div_le_div_of_nonneg_left hc0.le (by norm_num) (by norm_num)
    have hself : value c / 2 ^ 54 ≤ value c := div_le_self hc0.le (by norm_num)
    have hy0 : 0 ≤ y := by linarith
    have hsp0 : (0 : ℝ) < 2 ^ (a - 1 - 1) / 2 ^ 1074 := by positivity
    have h := F64FullStep.one_step_binades y c (a - 1) (a + 3) (by omega) (by omega)
      (by rw [hL]; linarith) (fun _ => by rw [hU]; linarith)
      (lt_trans hc63 (by decide)) (by rw [hL]; linarith) (by rw [hU]; linarith)
      (by
        rw [abs_lt]
        rw [abs_le] at hy
        constructor <;> linarith)
    exact F64SignedRounding.within_of_nonneg 1 y hy0 c (by rw [hlim] at hc63; omega) h.1 h.2

/-- A finite nonzero word of magnitude at most 1 within `|c| / 2 ^ 54` of `y` lies within one
step of the nearest-even reference of `y`. -/
theorem self_step (c : UInt64) (y : ℝ) (hcf : Finite c) (hc0 : value c ≠ 0)
    (hc1 : |value c| ≤ 1) (hy : |value c - y| ≤ |value c| / 2 ^ 54) :
    F64SignedRounding.WithinSteps 1 y c := by
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value c hcf
    rw [abs_of_neg hneg] at hc1 hy
    have h := self_step_pos (Wasm.IEEE64.negate c) (-y) hnf (by rw [hnv]; linarith)
      (by rw [hnv]; exact hc1)
      (by rw [hnv, show -value c - -y = -(value c - y) by ring, abs_neg]; exact hy)
    exact (F64SignedRounding.within_negate 1 y c).mp h
  · rw [abs_of_pos hpos] at hc1 hy
    exact self_step_pos c y hcf hpos hc1 hy

/-- A zero word lies within one step of the reference of zero. -/
theorem zero_step (c : UInt64) (hc : c.toNat % 2 ^ 63 = 0) :
    F64SignedRounding.WithinSteps 1 0 c := by
  refine ⟨by omega, ?_⟩
  have hr : F64SignedRounding.position (F64SignedRounding.roundNearestEven 0) = 0 := by
    simp only [F64SignedRounding.roundNearestEven, le_refl, ite_true,
      F64SignedRounding.positive_reference_zero]
    rfl
  rw [hr]
  have hc' := c.toNat_lt
  have hp : F64SignedRounding.position c = 0 := by
    unfold F64SignedRounding.position Wasm.IEEE64.sign
    by_cases hs : 2 ^ 63 ≤ c.toNat
    · simp only [hs, decide_true, ite_true]
      omega
    · simp only [hs, decide_false, Bool.false_eq_true, ite_false]
      omega
  rw [hp]
  norm_num

#print axioms self_step
#print axioms zero_step

end LeanExe.ProofKit.F64SelfStep
