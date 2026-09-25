import Project.EulerRiemann.FrozenTime
import Project.ProofKit.F64ResultBound

namespace Project.EulerRiemann.Frozen.Time

theorem proposal_fuel_encoding (n : Nat) (time alpha : UInt64) :
    let dt := proposal n time alpha
    (dt + 1).toNat = dt.toNat + 1 ∧ ¬ dt + 1 < dt := by
  dsimp only
  have hMin : proposal n time alpha ≤
      Wasm.IEEE64.div (Wasm.IEEE64.mul 0x3FD999999999999A (spacing n)) alpha := by
    simp only [proposal, Min.min]
    split <;> simp_all only [UInt64.le_iff_toNat_le] <;> omega
  have hDiv := Project.ProofKit.F64ResultBound.div_bound
    (Wasm.IEEE64.mul 0x3FD999999999999A (spacing n)) alpha
  rw [UInt64.le_iff_toNat_le] at hMin
  have hEncoding : (proposal n time alpha + 1).toNat = (proposal n time alpha).toNat + 1 := by
    rw [UInt64.toNat_add]
    change ((proposal n time alpha).toNat + 1) % 18446744073709551616 = _
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨hEncoding, by simp only [UInt64.lt_iff_toNat_lt, hEncoding]; omega⟩

#print axioms proposal_fuel_encoding

end Project.EulerRiemann.Frozen.Time
