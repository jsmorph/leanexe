import LeanExe.ProofKit.F64RelativeStep

/-!
One step near 1: a finite word within one and a half spacings of `[1/2, 1)` of a number from
`1/2` to `2` in magnitude lies within one step of the number's nearest-even reference
(`unit_step_pos`, and `unit_step` for either sign), by `F64FullStep.one_step_binades` over the
binades of `[1/2, 1)` and `[1, 2)`.
-/

namespace LeanExe.ProofKit.F64UnitStep

open CodeLib.IEEE64

set_option exponentiation.threshold 1200

/-- A word from `1/2` to `2` within one and a half spacings of `[1/2, 1)` of a number from `1/2`
to `2` lies within one step of its nearest-even reference. -/
theorem unit_step_pos (y : ℝ) (c : UInt64) (hcf : Finite c) (hy1 : 1 / 2 ≤ y) (hy2 : y ≤ 2)
    (hc1 : 1 / 2 ≤ value c) (hc2 : value c ≤ 2) (he : |value c - y| < 3 / 2 * (1 / 2 ^ 53)) :
    F64SignedRounding.WithinSteps 1 y c := by
  have b1 : value (UInt64.ofNat (1022 * 2 ^ 52)) = 1 / 2 := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    norm_num
  have b2 : value (UInt64.ofNat (1024 * 2 ^ 52)) = 2 := by
    rw [F64PositiveSpacing.boundary_value 1024 (by norm_num) (by norm_num)]
    norm_num
  have hcp : 0 < value c := by linarith
  have hc63 := F64PositiveOrder.positive_finite_encoding c hcf hcp
  have hlim : F64NearestNonnegative.limit = 0x7FF0000000000000 := rfl
  have h := F64FullStep.one_step_binades y c 1022 1024 (by norm_num) (by norm_num)
    (by rw [b1]; exact hy1) (fun _ => by rw [b2]; exact hy2)
    (lt_trans hc63 (by decide)) (by rw [b1]; exact hc1) (by rw [b2]; exact hc2)
    (by norm_num; norm_num at he; linarith)
  exact F64SignedRounding.within_of_nonneg 1 y (by linarith) c (by rw [hlim] at hc63; omega)
    h.1 h.2

/-- `unit_step_pos` for numbers of either sign. -/
theorem unit_step (y : ℝ) (c : UInt64) (hcf : Finite c) (hy1 : 1 / 2 + 1 / 2 ^ 50 ≤ |y|)
    (hy2 : |y| ≤ 1)
    (he : |value c - y| < 3 / 2 * (1 / 2 ^ 53)) :
    F64SignedRounding.WithinSteps 1 y c := by
  have he' := abs_lt.mp he
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy] at hy1 hy2
    exact unit_step_pos y c hcf (by linarith) (by linarith) (by norm_num at he' hy1; linarith)
      (by norm_num at he'; linarith) he
  · rw [abs_of_neg hy] at hy1 hy2
    obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value c hcf
    have h := unit_step_pos (-y) (Wasm.IEEE64.negate c) hnf (by linarith) (by linarith)
      (by rw [hnv]; norm_num at he' hy1; linarith) (by rw [hnv]; norm_num at he'; linarith)
      (by rw [hnv, show -value c - -y = -(value c - y) by ring, abs_neg]; exact he)
    exact (F64SignedRounding.within_negate 1 y c).mp h

#print axioms unit_step_pos
#print axioms unit_step

end LeanExe.ProofKit.F64UnitStep
