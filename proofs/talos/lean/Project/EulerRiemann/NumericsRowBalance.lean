import Project.EulerRiemann.NumericsUpdateResidual
import Project.ProofKit.RealFiniteVolumeBalance

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open scoped BigOperators
open Project.EulerCellStep.Model (updateCheckedBits)
open Project.ProofKit.F64ConservativeUpdate
open Project.ProofKit.F64RoundingResidual (radius)

noncomputable def rowResidual (ratio : UInt64) (state flux : Nat → UInt64) (i : Nat) : ℝ :=
  residual ratio (state i) (flux i) (flux (i+1))
    (updateCheckedBits ratio (state i) (flux i) (flux (i+1))).value

noncomputable def rowErrorBound (ratio : UInt64) (state flux : Nat → UInt64) (i : Nat) : ℝ :=
  |value ratio| * radius (Wasm.IEEE64.sub (flux (i+1)) (flux i)) +
    radius (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub (flux (i+1)) (flux i))) +
    radius (updateCheckedBits ratio (state i) (flux i) (flux (i+1))).value

theorem row_balance (count : Nat) (ratio : UInt64) (state flux : Nat → UInt64) :
    (∑ i ∈ Finset.range count, value (updateCheckedBits ratio (state i) (flux i) (flux (i+1))).value) -
      (∑ i ∈ Finset.range count, value (state i)) =
      value ratio * (value (flux 0) - value (flux count)) +
        ∑ i ∈ Finset.range count, rowResidual ratio state flux i := by
  have h := Project.ProofKit.RealFiniteVolumeBalance.sweep_balance count (value ratio)
    (fun i => value (state i))
    (fun i => value (updateCheckedBits ratio (state i) (flux i) (flux (i+1))).value)
    (fun i => value (flux i)) (rowResidual ratio state flux) (fun i _ => by
      unfold rowResidual Project.ProofKit.F64ConservativeUpdate.residual
      ring)
  convert h using 1 <;> ring

theorem accepted_row_residual_bound (count : Nat) (ratio : UInt64) (state flux : Nat → UInt64)
    (h : ∀ i < count, (updateCheckedBits ratio (state i) (flux i) (flux (i+1))).status = 0) :
    |∑ i ∈ Finset.range count, rowResidual ratio state flux i| ≤
      ∑ i ∈ Finset.range count, rowErrorBound ratio state flux i := by
  calc
    _ ≤ ∑ i ∈ Finset.range count, |rowResidual ratio state flux i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun i hi =>
      accepted_update_residual_bound ratio (state i) (flux i) (flux (i+1))
        (h i (Finset.mem_range.mp hi)))

#print axioms row_balance
#print axioms accepted_row_residual_bound

end Project.EulerRiemann.Numerics
