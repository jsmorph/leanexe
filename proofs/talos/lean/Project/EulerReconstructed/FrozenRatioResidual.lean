import Project.ProofKit.F64OutwardError
import Project.ProofKit.RealQuotientError
import Project.EulerRiemann.FrozenOutwardMeshSpec

namespace Project.EulerReconstructed.Frozen.Conservation
open CodeLib.IEEE64
open Project.ProofKit
open Project.ProofKit.F64Outward (enclosureWidth)
open Project.EulerRiemann.Frozen.OutwardCfl

theorem grid_ratio_parts (n : Nat) (dt alpha : UInt64)
    (hs : (gridRatioChecked n dt alpha).status = 0) :
    2 ≤ n ∧ n ≤ 800 ∧ (spacingLower n).status = 0 ∧
      F64Order.positiveBits dt = true ∧ F64Order.positiveBits (spacingLower n).value = true ∧
      (F64Outward.div true dt (spacingLower n).value).status = 0 ∧
      gridRatioChecked n dt alpha = F64Outward.div true dt (spacingLower n).value := by
  unfold gridRatioChecked ratioChecked at hs ⊢
  dsimp only at hs ⊢
  split_ifs at hs ⊢ with hn hh hp hr hc
  · have hp : (F64Order.positiveBits dt = true ∧
        F64Order.positiveBits (spacingLower n).value = true) ∧
        F64Order.positiveBits alpha = true := by simpa only [Bool.and_eq_true] using hp
    exact ⟨hn.1, hn.2, by simpa only [beq_iff_eq] using hh,
      hp.1.1, hp.1.2, by simpa only [beq_iff_eq] using hr, rfl⟩
  all_goals exact False.elim ((by decide : (1 : UInt64) ≠ 0) hs)

noncomputable def spacingErrorBound (n : Nat) : ℝ :=
  enclosureWidth (Wasm.IEEE64.div 0x3FF0000000000000 (Project.EulerRiemann.Frozen.Time.smallNaturalBits n))

theorem spacing_error (n : Nat) (hn : n ≤ 800) (hs : (spacingLower n).status = 0) :
    |value (spacingLower n).value - 1 / (n : ℝ)| ≤ spacingErrorBound n := by
  have he := F64Outward.div_error false 0x3FF0000000000000
    (Project.EulerRiemann.Frozen.Time.smallNaturalBits n) hs
  have hword : Project.EulerRiemann.Frozen.Time.smallNaturalBits 1 = 0x3FF0000000000000 := by decide +kernel
  have hone : value 0x3FF0000000000000 = (1 : ℝ) := by
    simpa only [hword, Nat.cast_one] using Project.EulerRiemann.Frozen.Time.smallNaturalBits_value 1 (by decide)
  simpa only [spacingLower, spacingErrorBound, hone,
    Project.EulerRiemann.Frozen.Time.smallNaturalBits_value n hn] using he

noncomputable def ratioErrorBound (n : Nat) (dt : UInt64) : ℝ :=
  enclosureWidth (Wasm.IEEE64.div dt (spacingLower n).value) +
    |value dt| * spacingErrorBound n / (value (spacingLower n).value * (1 / (n : ℝ)))

theorem ratio_error (n : Nat) (dt alpha : UInt64)
    (hs : (gridRatioChecked n dt alpha).status = 0) :
    |value (gridRatioChecked n dt alpha).value - value dt * (n : ℝ)| ≤ ratioErrorBound n dt := by
  obtain ⟨hn0, hn1, hh, _, hp, hd, he⟩ := grid_ratio_parts n dt alpha hs
  rw [he]
  have hsPos := (F64Order.positiveBits_spec _ hp).2
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdiv := F64Outward.div_error true dt (spacingLower n).value hd
  have hden := RealQuotientError.denominator_error (value dt) (value (spacingLower n).value)
    (1 / (n : ℝ)) (spacingErrorBound n) hsPos.ne' (by positivity) (spacing_error n hn1 hh)
  have hid : value dt / (1 / (n : ℝ)) = value dt * (n : ℝ) := by field_simp
  rw [hid, abs_of_pos hsPos, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)] at hden
  exact (abs_sub_le _ _ _).trans (add_le_add hdiv hden)

#print axioms grid_ratio_parts
#print axioms spacing_error
#print axioms ratio_error
end Project.EulerReconstructed.Frozen.Conservation
