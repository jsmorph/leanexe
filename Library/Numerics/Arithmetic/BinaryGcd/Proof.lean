import Library.Numerics.Arithmetic.BinaryGcd.Program
import Library.Numerics.Arithmetic.BinaryGcd.Spec
import Mathlib.Data.Nat.Prime.Basic

/-! The proof that the binary GCD computes `Nat.gcd`.  `removeTwos_spec` and `commonTwos_spec`
state what the two shifting loops compute in terms of powers of 2.  `oddGcd_spec` follows from
`gcd u v = gcd u (v - u)` and from the fact that a power of 2 shares no factor with an odd number.
`binaryGcd_eq` combines them with `gcd (2^j * a) (2^j * b) = 2^j * gcd a b`. -/

namespace Library.Numerics.Arithmetic.BinaryGcd

theorem and_one_eq_zero (x : UInt64) : x &&& 1 = 0 ↔ x.toNat % 2 = 0 := by
  rw [← UInt64.toNat_inj, UInt64.toNat_and]
  simp [Nat.and_one_is_mod]

theorem shiftRight_one (x : UInt64) : (x >>> 1).toNat = x.toNat / 2 := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_ne_zero {x : UInt64} (h : x ≠ 0) : x.toNat ≠ 0 :=
  fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))

/-- `removeTwos x` is `x` divided by a power of 2, and it is odd when `x` is not 0. -/
theorem removeTwos_spec (x : UInt64) :
    ∃ j, x.toNat = 2 ^ j * (removeTwos x).toNat ∧ (x ≠ 0 → (removeTwos x).toNat % 2 = 1) := by
  rw [removeTwos.eq_def]
  split
  · rename_i h
    have h0 := toNat_ne_zero h.2
    have he := (and_one_eq_zero x).mp h.1
    have hs := shiftRight_one x
    obtain ⟨j, hj, hodd⟩ := removeTwos_spec (x >>> 1)
    refine ⟨j + 1, ?_, fun _ => hodd fun h' => ?_⟩
    · rw [pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]; omega
    · rw [← UInt64.toNat_inj] at h'
      simp only [hs, UInt64.toNat_zero] at h'
      omega
  · rename_i h
    refine ⟨0, by simp, fun hx => ?_⟩
    have h0 := toNat_ne_zero hx
    by_contra hodd
    exact h ⟨(and_one_eq_zero x).mpr (by omega), hx⟩
termination_by x.toNat
decreasing_by
  have h : x &&& 1 = 0 ∧ x ≠ 0 := by assumption
  have h0 := toNat_ne_zero h.2
  rw [shiftRight_one]
  omega

/-- Step B1: `commonTwos u v k` divides `u` and `v` by one power `2^j` and adds `j` to `k`, and
for nonzero `u` the quotients are not both even and the first is not 0. -/
theorem commonTwos_spec (u v k : UInt64) :
    ∃ j, u.toNat = 2 ^ j * (commonTwos u v k).1.toNat ∧
      v.toNat = 2 ^ j * (commonTwos u v k).2.1.toNat ∧
      (commonTwos u v k).2.2 = k + UInt64.ofNat j ∧
      (u ≠ 0 → (commonTwos u v k).1 ≠ 0 ∧
        ((commonTwos u v k).1.toNat % 2 = 1 ∨ (commonTwos u v k).2.1.toNat % 2 = 1)) := by
  rw [commonTwos.eq_def]
  split
  · rename_i h
    have h0 := toNat_ne_zero h.2.2
    have hu := (and_one_eq_zero u).mp h.1
    have hv := (and_one_eq_zero v).mp h.2.1
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ := commonTwos_spec (u >>> 1) (v >>> 1) (k + 1)
    rw [shiftRight_one] at hj1
    rw [shiftRight_one] at hj2
    refine ⟨j + 1, ?_, ?_, ?_, fun _ => hj4 fun h' => ?_⟩
    · rw [pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]; omega
    · rw [pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]; omega
    · rw [hj3]
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    · rw [← UInt64.toNat_inj] at h'
      simp only [shiftRight_one, UInt64.toNat_zero] at h'
      omega
  · rename_i h
    refine ⟨0, by simp, by simp, by simp, fun hu => ⟨hu, ?_⟩⟩
    by_contra hodd
    have hodd' : ¬(u.toNat % 2 = 1 ∨ v.toNat % 2 = 1) := hodd
    exact h ⟨(and_one_eq_zero u).mpr (by omega), (and_one_eq_zero v).mpr (by omega), hu⟩
termination_by u.toNat
decreasing_by
  have h : u &&& 1 = 0 ∧ v &&& 1 = 0 ∧ u ≠ 0 := by assumption
  have h0 := toNat_ne_zero h.2.2
  rw [shiftRight_one]
  omega

theorem coprime_pow_two {n : Nat} (j : Nat) (h : n % 2 = 1) : Nat.Coprime (2 ^ j) n :=
  Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr h))

theorem gcd_pow_two_right {a b : Nat} (j : Nat) (h : a % 2 = 1) :
    Nat.gcd a (2 ^ j * b) = Nat.gcd a b :=
  Nat.Coprime.gcd_mul_left_cancel_right b (coprime_pow_two j h)

theorem gcd_pow_two_left {a b : Nat} (j : Nat) (h : b % 2 = 1) :
    Nat.gcd (2 ^ j * a) b = Nat.gcd a b :=
  Nat.Coprime.gcd_mul_left_cancel a (coprime_pow_two j h)

/-- Steps B2 to B6: on two odd numbers, `oddGcd` computes their greatest common divisor. -/
theorem oddGcd_spec (u v : UInt64) (hu : u.toNat % 2 = 1) (hv : v.toNat % 2 = 1) :
    (oddGcd u v).toNat = Nat.gcd u.toNat v.toNat := by
  have hu0 : u ≠ 0 := fun h => by subst h; simp at hu
  have hv0 : v ≠ 0 := fun h => by subst h; simp at hv
  rw [oddGcd.eq_def]
  simp only [hu0, hv0, ↓reduceIte]
  by_cases he : u = v
  · subst he; simp
  · simp only [he, ↓reduceIte]
    by_cases hlt : u < v
    · simp only [hlt, ↓reduceIte]
      have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
      have hsub : (v - u).toNat = v.toNat - u.toNat :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt hlt'))
      obtain ⟨j, hj, hodd⟩ := removeTwos_spec (v - u)
      have hne : v - u ≠ 0 := fun h => by
        have := congrArg UInt64.toNat h; rw [hsub] at this; simp at this; omega
      rw [oddGcd_spec u (removeTwos (v - u)) hu (hodd hne), ← gcd_pow_two_right j hu, ← hj, hsub,
        Nat.gcd_sub_self_right (Nat.le_of_lt hlt')]
    · simp only [hlt, ↓reduceIte]
      have hlt' : v.toNat < u.toNat := by
        have h1 : ¬ u.toNat < v.toNat := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
        have h2 : u.toNat ≠ v.toNat := fun h => he (UInt64.toNat_inj.mp h)
        omega
      have hsub : (u - v).toNat = u.toNat - v.toNat :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt hlt'))
      obtain ⟨j, hj, hodd⟩ := removeTwos_spec (u - v)
      have hne : u - v ≠ 0 := fun h => by
        have := congrArg UInt64.toNat h; rw [hsub] at this; simp at this; omega
      rw [oddGcd_spec (removeTwos (u - v)) v (hodd hne) hv, ← gcd_pow_two_left j hv, ← hj, hsub,
        Nat.gcd_sub_self_left (Nat.le_of_lt hlt')]
termination_by u.toNat + v.toNat
decreasing_by
  all_goals
    have h1 := removeTwos_le (v - u)
    have h2 := removeTwos_le (u - v)
    have := UInt64.toNat_lt u
    have := UInt64.toNat_lt v
    simp only [UInt64.toNat_sub] at h1 h2
    omega

/-- The binary GCD computes the specification on every pair of words. -/
theorem binaryGcd_eq (u v : UInt64) : binaryGcd u v = expected (u, v) := by
  unfold binaryGcd expected
  by_cases hu : u = 0
  · subst hu; simp
  by_cases hv : v = 0
  · subst hv; simp [hu]
  simp only [hu, hv, ↓reduceIte]
  obtain ⟨j, hj1, hj2, hj3, hj4⟩ := commonTwos_spec u v 0
  obtain ⟨hne, hodd⟩ := hj4 hu
  generalize commonTwos u v 0 = c at hj1 hj2 hj3 hne hodd
  obtain ⟨u1, v1, k⟩ := c
  simp only at hj1 hj2 hj3 hne hodd ⊢
  have hv1 : v1 ≠ 0 := fun h => by subst h; simp at hj2; exact toNat_ne_zero hv hj2
  obtain ⟨p, hp, hpodd⟩ := removeTwos_spec u1
  obtain ⟨q, hq, hqodd⟩ := removeTwos_spec v1
  have hg : Nat.gcd u1.toNat v1.toNat =
      Nat.gcd (removeTwos u1).toNat (removeTwos v1).toNat := by
    rcases hodd with h | h
    · rw [hq, gcd_pow_two_right q h]
      have hp0 : p = 0 := by
        rcases p with _ | p
        · rfl
        · rw [hp, pow_succ, Nat.mul_comm (2 ^ p) 2, Nat.mul_assoc, Nat.mul_mod_right] at h
          omega
      rw [hp0, pow_zero, one_mul] at hp
      rw [← hp]
    · rw [hp, gcd_pow_two_left p h]
      have hq0 : q = 0 := by
        rcases q with _ | q
        · rfl
        · rw [hq, pow_succ, Nat.mul_comm (2 ^ q) 2, Nat.mul_assoc, Nat.mul_mod_right] at h
          omega
      rw [hq0, pow_zero, one_mul] at hq
      rw [← hq]
  have hgcd : Nat.gcd u.toNat v.toNat = 2 ^ j * Nat.gcd u1.toNat v1.toNat := by
    rw [hj1, hj2, Nat.gcd_mul_left]
  have hj64 : j < 64 := by
    have hpos : 0 < u1.toNat := Nat.pos_of_ne_zero (toNat_ne_zero hne)
    have hlt := UInt64.toNat_lt u
    by_contra hge
    have : 2 ^ 64 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    have : 2 ^ j ≤ 2 ^ j * u1.toNat := Nat.le_mul_of_pos_right _ hpos
    omega
  have hk : k.toNat = j := by
    rw [hj3]
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have hle : Nat.gcd u.toNat v.toNat ≤ u.toNat :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (toNat_ne_zero hu)) (Nat.gcd_dvd_left _ _)
  have hlt := UInt64.toNat_lt u
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, oddGcd_spec _ _ (hpodd hne) (hqodd hv1), ← hg, hk,
    Nat.mod_eq_of_lt hj64, Nat.shiftLeft_eq, UInt64.toNat_ofNat', Nat.mul_comm, ← hgcd]

end Library.Numerics.Arithmetic.BinaryGcd
