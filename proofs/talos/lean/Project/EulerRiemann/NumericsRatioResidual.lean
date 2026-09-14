import Project.EulerRiemann.NumericsSpacingResidual
import Project.EulerRiemann.NumericsStepBalance
import Project.ProofKit.RealQuotientError

namespace Project.EulerRiemann.Conservation
open CodeLib.IEEE64
open Project.ProofKit
open Project.Euler2DCellStep.Sweep

noncomputable def ratioErrorBound (n : Nat) (dt : UInt64) : ℝ :=
  F64RoundingResidual.radius (Wasm.IEEE64.div dt (Time.spacing n)) +
    |value dt| * F64RoundingResidual.radius (Time.spacing n) /
      (value (Time.spacing n) * (1 / (n : ℝ)))

theorem ratio_error (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (dt : UInt64)
    (hdt : Finite dt) (hr : Finite (Wasm.IEEE64.div dt (Time.spacing n))) :
    |value (Wasm.IEEE64.div dt (Time.spacing n)) - value dt * (n : ℝ)| ≤ ratioErrorBound n dt := by
  have hs := F64Order.positiveBits_spec _ (spacing_positive n hn)
  have hs0 := (F64PositiveArithmetic.positive_input _ (spacing_positive n hn)).2.2
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he := F64RoundingResidual.div_error dt (Time.spacing n) hdt hs.1 hs0 hr
  have hi := RealQuotientError.denominator_error (value dt) (value (Time.spacing n))
    (1 / (n : ℝ)) (F64RoundingResidual.radius (Time.spacing n)) hs.2.ne'
    (by positivity) (spacing_error n hn)
  have hd : value dt / (1 / (n : ℝ)) = value dt * (n : ℝ) := by field_simp
  rw [hd, abs_of_pos hs.2, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)] at hi
  exact le_trans (abs_sub_le _ _ _) (add_le_add he hi)

theorem step_ratio_positive {n : Nat} (hn : 0 < n) (ratio : UInt64) (grid next : Grid n n)
    (h : Numerics.step ratio grid = some next) : F64Order.positiveBits ratio = true := by
  have hx := (accepted_step_parts ratio grid next h).1
  have hc := hx ⟨0, hn⟩ ⟨0, hn⟩
  change (Numerics.evaluate ratio (inputs false grid ⟨0, hn⟩ ⟨0, hn⟩)).status = 0 at hc
  unfold Numerics.evaluate Numerics.cellCheckedBits at hc
  split at hc
  · assumption
  · simp [Project.Euler2DCellStep.Model.rejectedCell] at hc

theorem accepted_ratio_error {n : Nat} (hn : 2 ≤ n ∧ n ≤ 800) (time dt : UInt64)
    (grid next : Grid n n) (ht : Time.validAdvance time dt = true)
    (hs : Numerics.step (Wasm.IEEE64.div dt (Time.spacing n)) grid = some next) :
    |value (Wasm.IEEE64.div dt (Time.spacing n)) - value dt * (n : ℝ)| ≤ ratioErrorBound n dt := by
  simp only [Time.validAdvance, Bool.and_eq_true] at ht
  exact ratio_error n hn dt (F64Order.positiveBits_spec dt ht.1.1).1
    (F64Order.positiveBits_spec _ (step_ratio_positive (by omega) _ grid next hs)).1

#print axioms ratio_error
#print axioms step_ratio_positive
#print axioms accepted_ratio_error
end Project.EulerRiemann.Conservation
