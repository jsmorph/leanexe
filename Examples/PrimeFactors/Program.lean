/-!
The number of prime factors of a word, counted with
multiplicity, with 0 for 0 and 1.  `countFactors` divides out each divisor in increasing order while
`divisor ≤ remaining / divisor`, and then counts what remains, which is 1 or a prime.
-/

namespace Examples.PrimeFactors

def countFactors (remaining divisor count : UInt64) : UInt64 :=
  if remaining ≤ 1 ∨ divisor ≤ 1 then count
  else if divisor > remaining / divisor then count + 1
  else if remaining % divisor = 0 then countFactors (remaining / divisor) divisor (count + 1)
  else countFactors remaining (divisor + 1) count
termination_by remaining.toNat * 2 ^ 64 + (remaining.toNat - divisor.toNat)
decreasing_by
  all_goals
    rename_i h1 h2 _
    have hr := remaining.toNat_lt
    have hone : (1 : UInt64).toNat = 1 := rfl
    have hd : 2 ≤ divisor.toNat := Nat.le_of_not_lt fun hlt =>
      h1 (Or.inr (UInt64.le_iff_toNat_le.mpr (by rw [hone]; omega)))
    have hr2 : 2 ≤ remaining.toNat := Nat.le_of_not_lt fun hlt =>
      h1 (Or.inl (UInt64.le_iff_toNat_le.mpr (by rw [hone]; omega)))
    have hle : divisor.toNat ≤ remaining.toNat / divisor.toNat := by
      have h : ¬ remaining / divisor < divisor := h2
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] at h
      omega
    have hq : remaining.toNat / divisor.toNat ≤ remaining.toNat / 2 :=
      Nat.div_le_div_left hd (by decide)
  · rw [UInt64.toNat_div]
    have hm : remaining.toNat / divisor.toNat * 2 ^ 64 + 2 ^ 64 ≤ remaining.toNat * 2 ^ 64 := by
      have := Nat.mul_le_mul_right (2 ^ 64)
        (show remaining.toNat / divisor.toNat + 1 ≤ remaining.toNat by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      exact this
    omega
  · rw [UInt64.toNat_add, hone, Nat.mod_eq_of_lt (by omega)]
    omega

def compute (n : UInt64) : UInt64 := countFactors n 2 0

end Examples.PrimeFactors
