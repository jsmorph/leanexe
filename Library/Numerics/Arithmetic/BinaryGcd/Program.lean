/-! The binary GCD, Algorithm B of TAOCP §4.5.2.  Step B1 divides both arguments by 2 while both
are even and counts the divisions in `k` (`commonTwos`).  Steps B2 to B6 then keep two odd numbers
and replace the larger by their difference with its factors of 2 removed (`removeTwos`), until the
two are equal (`oddGcd`).  The result is the common odd value shifted left by `k`.  Knuth's steps
B2 to B6 hold the difference in one signed variable `t`; the program keeps the two odd numbers
instead, which needs no signed word. -/

namespace Library.Numerics.Arithmetic.BinaryGcd

/-- `x` with its factors of 2 removed, or 0 when `x` is 0. -/
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

/-- Step B1: `(u / 2^j, v / 2^j, k + j)`, with `j` the number of times that both are even, for
nonzero `u`. -/
def commonTwos (u v k : UInt64) : UInt64 × UInt64 × UInt64 :=
  if u &&& 1 = 0 ∧ v &&& 1 = 0 ∧ u ≠ 0 then commonTwos (u >>> 1) (v >>> 1) (k + 1) else (u, v, k)
termination_by u.toNat
decreasing_by
  have h : u &&& 1 = 0 ∧ v &&& 1 = 0 ∧ u ≠ 0 := by assumption
  have h0 : u.toNat ≠ 0 := fun h' => h.2.2 (UInt64.toNat_inj.mp (by simpa using h'))
  simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow,
    Nat.reduceMod, Nat.reducePow]
  omega

/-- Steps B2 to B6 on two odd numbers: replace the larger by the difference with its factors of 2
removed, until the two are equal.  The tests for 0 make the definition terminate on every pair of
words, and `binaryGcd` calls it only with odd numbers. -/
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

/-- The greatest common divisor of `u` and `v` by Algorithm B. -/
def binaryGcd (u v : UInt64) : UInt64 :=
  if u = 0 then v
  else if v = 0 then u
  else
    match commonTwos u v 0 with
    | (u1, v1, k) => oddGcd (removeTwos u1) (removeTwos v1) <<< k

end Library.Numerics.Arithmetic.BinaryGcd
