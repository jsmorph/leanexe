import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.Array

namespace Project.ProofKit.FixedArrayCapacity

theorem normalizedCapacity_toNat_of_fits (length stride : UInt64)
    (hFit : 8 + length.toNat * stride.toNat * 8 + 7 < UInt64.size) :
    (normalizedCapacity length stride).toNat = 8 + length.toNat * stride.toNat * 8 := by
  let payload := length.toNat * stride.toNat
  have hProduct : payload < UInt64.size := by omega
  have hBytes : payload * 8 < UInt64.size := by omega
  have hStart : 8 + payload * 8 < UInt64.size := by omega
  have hRound : 8 + payload * 8 + 7 < UInt64.size := hFit
  have hQuotient : (8 + payload * 8 + 7) / 8 * 8 = 8 + payload * 8 := by omega
  have hRaw : (unnormalizedCapacity length stride).toNat = 8 + payload * 8 := by
    simp only [unnormalizedCapacity, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add]
    change (((8 + (payload % UInt64.size * 8) % UInt64.size) % UInt64.size + 7) %
      UInt64.size / 8 * 8) % UInt64.size = 8 + payload * 8
    rw [Nat.mod_eq_of_lt hProduct, Nat.mod_eq_of_lt hBytes,
      Nat.mod_eq_of_lt hStart, Nat.mod_eq_of_lt hRound, hQuotient, Nat.mod_eq_of_lt hStart]
  have hNotSmall : ¬unnormalizedCapacity length stride < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hRaw]
    change ¬8 + payload * 8 < 8
    omega
  simp only [normalizedCapacity, ite_eq_right hNotSmall, hRaw, payload]

#print axioms normalizedCapacity_toNat_of_fits

end Project.ProofKit.FixedArrayCapacity
