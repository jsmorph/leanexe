import Project.ProofKit.Control

namespace Project.ProofKit.CheckedNatMul

theorem guard_of_fits (left right : UInt64)
    (hFit : left.toNat * right.toNat < UInt64.size) (hRight : right ≠ 0) :
    ¬ (-1 : UInt64) / right < left := by
  have hPositive : 0 < right.toNat := by
    by_contra h
    apply hRight
    apply UInt64.toNat.inj
    change right.toNat = 0
    omega
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]
  change ¬ 18446744073709551615 / right.toNat < left.toNat
  apply Nat.not_lt.mpr
  apply (Nat.le_div_iff_mul_le hPositive).mpr
  change left.toNat * right.toNat < 18446744073709551616 at hFit
  omega

#print axioms guard_of_fits

theorem guard_of_nat_fits (left right : Nat)
    (hFit : left * right < UInt64.size) (hRight : UInt64.ofNat right ≠ 0) :
    ¬ (-1 : UInt64) / UInt64.ofNat right < UInt64.ofNat left := by
  apply guard_of_fits _ _ _ hRight
  apply lt_of_le_of_lt _ hFit
  simp only [UInt64.toNat_ofNat']
  exact Nat.mul_le_mul (Nat.mod_le ..) (Nat.mod_le ..)

#print axioms guard_of_nat_fits

end Project.ProofKit.CheckedNatMul
