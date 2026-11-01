/-! The binary GCD, Algorithm B of TAOCP §4.5.2.  Knuth's algorithm takes positive integers, and
`binaryGcd` returns the other argument when one argument is 0.  Step B1 divides both arguments by 2
while both are even and counts the divisions in `k` (`commonTwos`).  At least one quotient is then
odd, and steps B2 to B5, on their first pass, remove the factors of 2 from the other, which
`binaryGcd` does by applying `removeTwos` to both.  Steps B6 and B3 to B5 then replace the larger of
two odd numbers by their difference with its factors of 2 removed until the two are equal
(`oddGcd`), and the result is the common value shifted left by `k`.  Knuth holds the difference in
one signed variable `t`, and the program keeps the two odd numbers instead, which needs no signed
word. -/

namespace Library.Numerics.Arithmetic.BinaryGcd

/-- Steps B3 and B4: `x` with its factors of 2 removed, or 0 when `x` is 0.  The test `x ≠ 0` makes
the definition terminate at 0, which is even. -/
def removeTwos (x : UInt64) : UInt64 :=
  if x &&& 1 = 0 ∧ x ≠ 0 then removeTwos (x >>> 1) else x
termination_by x.toNat
decreasing_by
  have h : x &&& 1 = 0 ∧ x ≠ 0 := by assumption
  have h0 : x.toNat ≠ 0 := fun h' => h.2 (UInt64.toNat_inj.mp (by simpa using h'))
  simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow,
    Nat.reduceMod, Nat.reducePow]
  omega

theorem removeTwos_le (x : UInt64) : (removeTwos x).toNat ≤ x.toNat := by
  rw [removeTwos.eq_def]
  split
  · rename_i h
    have h0 : x.toNat ≠ 0 := fun h' => h.2 (UInt64.toNat_inj.mp (by simpa using h'))
    have := removeTwos_le (x >>> 1)
    simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow,
      Nat.reduceMod, Nat.reducePow] at this
    omega
  · exact Nat.le_refl _
termination_by x.toNat
decreasing_by
  have h : x &&& 1 = 0 ∧ x ≠ 0 := by assumption
  have h0 : x.toNat ≠ 0 := fun h' => h.2 (UInt64.toNat_inj.mp (by simpa using h'))
  simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow,
    Nat.reduceMod, Nat.reducePow]
  omega

/-- Step B1: for nonzero `u`, `(u / 2^j, v / 2^j, k + j)`, with `2^j` the largest power of 2 that
divides both `u` and `v`.  `k` counts the halvings, and `binaryGcd` starts it at 0.  The test
`u ≠ 0` makes the definition terminate when `u` is 0, which stays even under halving. -/
def commonTwos (u v k : UInt64) : UInt64 × UInt64 × UInt64 :=
  if u &&& 1 = 0 ∧ v &&& 1 = 0 ∧ u ≠ 0 then commonTwos (u >>> 1) (v >>> 1) (k + 1) else (u, v, k)
termination_by u.toNat
decreasing_by
  have h : u &&& 1 = 0 ∧ v &&& 1 = 0 ∧ u ≠ 0 := by assumption
  have h0 : u.toNat ≠ 0 := fun h' => h.2.2 (UInt64.toNat_inj.mp (by simpa using h'))
  simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow,
    Nat.reduceMod, Nat.reducePow]
  omega

/-- Steps B3 to B6 on two odd numbers: while the two differ, replace the larger by their difference
with its factors of 2 removed, and return the common value, their greatest common divisor.  Knuth
stops when `t = u - v` is 0, and the program tests `u = v`.  The tests for 0 make the definition
terminate on every pair of words, and `binaryGcd` calls it only with odd numbers. -/
def oddGcd (u v : UInt64) : UInt64 :=
  if u = 0 then v
  else if v = 0 then u
  else if u = v then u
  else if u < v then oddGcd u (removeTwos (v - u))
  else oddGcd (removeTwos (u - v)) v
termination_by u.toNat + v.toNat
decreasing_by
  all_goals
    have h1 := removeTwos_le (v - u)
    have h2 := removeTwos_le (u - v)
    have hu : u ≠ 0 := by assumption
    have hv : v ≠ 0 := by assumption
    have hne : u ≠ v := by assumption
    have hu' : u.toNat ≠ 0 := fun h' => hu (UInt64.toNat_inj.mp (by simpa using h'))
    have hv' : v.toNat ≠ 0 := fun h' => hv (UInt64.toNat_inj.mp (by simpa using h'))
    have hne' : u.toNat ≠ v.toNat := fun h' => hne (UInt64.toNat_inj.mp h')
    have := UInt64.toNat_lt u
    have := UInt64.toNat_lt v
    simp only [UInt64.toNat_sub] at h1 h2
  · have hlt : u < v := by assumption
    rw [UInt64.lt_iff_toNat_lt] at hlt
    omega
  · have hlt : ¬ u < v := by assumption
    rw [UInt64.lt_iff_toNat_lt] at hlt
    omega

/-- The greatest common divisor of `u` and `v` by Algorithm B: the other argument when one is 0,
and otherwise `oddGcd` of the quotients of step B1 with their factors of 2 removed, shifted left by
the count `k` of that step.  The shift does not wrap, because the result is at most `u`. -/
def binaryGcd (u v : UInt64) : UInt64 :=
  if u = 0 then v
  else if v = 0 then u
  else
    match commonTwos u v 0 with
    | (u1, v1, k) => oddGcd (removeTwos u1) (removeTwos v1) <<< k

end Library.Numerics.Arithmetic.BinaryGcd
