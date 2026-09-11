import Project.EulerRiemann.Time
import CodeLib.IEEE64.Roundoff

namespace Project.EulerRiemann.Time

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem smallNaturalBits_spec : ∀ n : Fin 801,
    Wasm.IEEE64.isFinite (smallNaturalBits n.val) = true ∧
      Wasm.IEEE64.scaledValue (smallNaturalBits n.val) = (n.val : Int) * 2 ^ 1074 := by
  decide +kernel

theorem smallNaturalBits_value (n : Nat) (hn : n ≤ 800) :
    CodeLib.IEEE64.value (smallNaturalBits n) = (n : ℝ) := by
  unfold CodeLib.IEEE64.value
  rw [(smallNaturalBits_spec ⟨n, by omega⟩).2]
  norm_num

theorem smallNaturalBits_finite (n : Nat) (hn : n ≤ 800) :
    CodeLib.IEEE64.Finite (smallNaturalBits n) :=
  (smallNaturalBits_spec ⟨n, by omega⟩).1

theorem validAdvance_bounds (time dt : UInt64) (h : validAdvance time dt = true) :
    time < Wasm.IEEE64.add time dt ∧ Wasm.IEEE64.add time dt ≤ endTime := by
  simp only [validAdvance, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem remaining_decreases (time dt : UInt64) (h : validAdvance time dt = true) :
    endTime.toNat - (Wasm.IEEE64.add time dt).toNat < endTime.toNat - time.toNat := by
  obtain ⟨hlt, hle⟩ := validAdvance_bounds time dt h
  change time.toNat < (Wasm.IEEE64.add time dt).toNat at hlt
  change (Wasm.IEEE64.add time dt).toNat ≤ endTime.toNat at hle
  omega

#print axioms smallNaturalBits_spec
#print axioms smallNaturalBits_value
#print axioms smallNaturalBits_finite
#print axioms remaining_decreases

end Project.EulerRiemann.Time
