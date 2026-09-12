import Project.EulerRiemann.ControlTime

namespace Project.EulerRiemann.Control

theorem retry_initial_valid (fuel n : Nat) (time dt : UInt64) (grid : Array Traversal.Cell)
    (h : (retry fuel n time dt grid).status = 0) : Time.validAdvance time dt = true := by
  cases fuel with
  | zero => simp [retry] at h
  | succ fuel =>
    cases hValid : Time.validAdvance time dt with
    | false => simp [retry, hValid] at h
    | true => rfl

theorem retry_fuel_encoding (n : Nat) (time dt : UInt64) (grid : Array Traversal.Cell)
    (h : (retry (dt.toNat + 1) n time dt grid).status = 0) :
    (dt + 1).toNat = dt.toNat + 1 ∧ ¬ dt + 1 < dt := by
  have hValid := retry_initial_valid _ n time dt grid h
  simp only [Time.validAdvance, Project.Euler2DConservative.Model.positiveBits,
    Bool.and_eq_true, decide_eq_true_eq] at hValid
  have hUpper := hValid.1.1.2
  change dt.toNat < 9218868437227405312 at hUpper
  have hNat : (dt + 1).toNat = dt.toNat + 1 := by
    rw [UInt64.toNat_add]
    change (dt.toNat + 1) % 18446744073709551616 = dt.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨hNat, by simp only [UInt64.lt_iff_toNat_lt, hNat]; omega⟩

theorem advance_success_step (fuel n : Nat) (time : UInt64) (grid : Array Traversal.Cell)
    (hTime : time ≠ Time.endTime) (h : (advance (fuel + 1) n time grid).status = 0) :
    let stats := Traversal.scan grid
    let dt := Time.proposal n time stats.alpha
    let trial := retry (dt.toNat + 1) n time dt grid
    stats.status = 0 ∧ trial.status = 0 ∧
      advance fuel n (Wasm.IEEE64.add time trial.dt) trial.grid = advance (fuel + 1) n time grid := by
  dsimp only
  have hScan : (Traversal.scan grid).status = 0 := by
    by_contra hScan
    simp [advance, hTime, hScan] at h
  have hTrial : (retry ((Time.proposal n time (Traversal.scan grid).alpha).toNat + 1)
      n time (Time.proposal n time (Traversal.scan grid).alpha) grid).status = 0 := by
    by_contra hTrial
    simp [advance, hTime, hScan, hTrial] at h
  exact ⟨hScan, hTrial, by simp [advance, hTime, hScan, hTrial]⟩

#print axioms retry_initial_valid
#print axioms retry_fuel_encoding
#print axioms advance_success_step

end Project.EulerRiemann.Control
