import Project.ProofKit.FixedArrayCapacity

namespace Project.ProofKit.FixedArrayCapacity

theorem wordCapacity_toNat (length : UInt64) (hLength : length.toNat ≤ 4294967296) :
    (normalizedCapacity length 1).toNat = 8 * (length.toNat + 1) := by
  have hRaw : (unnormalizedCapacity length 1).toNat = 8 * (length.toNat + 1) := by
    have h8 : (8 : UInt64).toNat = 8 := rfl
    have h7 : (7 : UInt64).toNat = 7 := rfl
    unfold unnormalizedCapacity
    simp only [UInt64.mul_one, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, h8, h7]
    norm_num
    omega
  have hNotSmall : ¬unnormalizedCapacity length 1 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hRaw]
    change ¬8 * (length.toNat + 1) < 8
    omega
  simp only [normalizedCapacity, ite_eq_right hNotSmall, hRaw]

theorem wordCapacity_eq (length : UInt64) (hLength : length.toNat ≤ 4294967296) :
    normalizedCapacity length 1 = UInt64.ofNat (8 * (length.toNat + 1)) := by
  apply UInt64.toNat_inj.mp
  rw [wordCapacity_toNat length hLength, UInt64.toNat_ofNat_of_lt']
  change 8 * (length.toNat + 1) < 18446744073709551616
  omega

theorem wordCapacity_ofNat (length : Nat) (hLength : length ≤ 4294967296) :
    normalizedCapacity (UInt64.ofNat length) 1 = UInt64.ofNat (8 * (length + 1)) := by
  have hFit : length < UInt64.size := by
    change length < 18446744073709551616
    omega
  simpa only [UInt64.toNat_ofNat_of_lt' hFit] using
    wordCapacity_eq (UInt64.ofNat length)
      (by simpa only [UInt64.toNat_ofNat_of_lt' hFit] using hLength)

#print axioms wordCapacity_toNat
#print axioms wordCapacity_eq
#print axioms wordCapacity_ofNat
end Project.ProofKit.FixedArrayCapacity
