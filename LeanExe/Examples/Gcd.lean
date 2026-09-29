namespace LeanExe.Examples.Gcd

/-- Euclid's algorithm on 64-bit words: `gcd a 0 = a`, and otherwise
`gcd a b = gcd b (a % b)`. -/
def gcd (a b : UInt64) : UInt64 :=
  if b = 0 then a else gcd b (a % b)
termination_by b.toNat
decreasing_by
  rename_i hNonzero
  rw [UInt64.toNat_mod]
  apply Nat.mod_lt
  apply Nat.pos_of_ne_zero
  intro hZero
  exact hNonzero (UInt64.toNat_inj.mp (by simpa using hZero))

end LeanExe.Examples.Gcd
