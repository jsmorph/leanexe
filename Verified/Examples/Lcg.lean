import Verified.Examples.Orbit
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.UInt
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! A linear congruential generator modulo `2^64`: each step replaces the state `x` with
`a * x + c`, with arithmetic that wraps modulo `2^64`.  `step` uses the multiplier
`6364136223846793005` of Knuth's *The Art of Computer Programming*, Volume 2, Section 3.3.4, and the
increment `1442695040888963407`, the default increment of O'Neill's PCG generators.  The general
theorems hold for every multiplier and increment.  From any word, `affine a c` returns to that word
after `2^64` steps and not before if and only if `a % 4 = 1` and `c % 2 = 1`, which are Hull and
Dobell's conditions for the modulus `2^64`.  Under these conditions, `2^k` steps complement bit `k`
of the state, so the periods of bit `k` are the multiples of `2^(k+1)`.  The programs are `affine`,
`step`, and `advance`.  The definitions after them, which use `Nat`, appear only in proofs. -/

namespace Verified.Examples.Lcg

/-- `a * x + c`, modulo `2^64`. -/
def affine (a c x : UInt64) : UInt64 := a * x + c

/-- One step of the generator: `6364136223846793005 * x + 1442695040888963407`, modulo `2^64`. -/
def step (x : UInt64) : UInt64 := affine 6364136223846793005 1442695040888963407 x

/-- The state after `n` steps from `x`. -/
def advance (n x : UInt64) : UInt64 := LeanExe.loop n x fun _ s => step s

open Function
open scoped UInt64.CommRing

theorem advance_eq_iterate (n x : UInt64) : advance n x = step^[n.toNat] x :=
  Orbit.loop_eq_iterate step n x

theorem mod_add_mul_div (a m : UInt64) : a % m + m * (a / m) = a := by
  apply UInt64.toNat_inj.mp
  have h1 := Nat.mul_div_le a.toNat m.toNat
  have h2 := a.toNat_lt_size
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod, UInt64.toNat_div]
  rw [Nat.mod_eq_of_lt (a := m.toNat * (a.toNat / m.toNat)) (by simp [UInt64.size] at *; omega),
    Nat.mod_add_div, Nat.mod_eq_of_lt h2]

theorem two_pow_64 : (2 : UInt64) ^ 64 = 0 := by decide +kernel

theorem two_pow_63_ne : (2 : UInt64) ^ 63 ≠ 0 := by decide +kernel

/-! ### Iterates of an affine map -/

section Iterates

variable (a c : UInt64)

/-- The coefficients `(b, d)` of the map `x ↦ b * x + d` that equals `2^k` steps of
`affine a c`. -/
def doubled : ℕ → UInt64 × UInt64
  | 0 => (a, c)
  | k + 1 => ((doubled k).1 * (doubled k).1, ((doubled k).1 + 1) * (doubled k).2)

theorem iterate_two_pow (k : ℕ) (x : UInt64) :
    (affine a c)^[2 ^ k] x = (doubled a c k).1 * x + (doubled a c k).2 := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, mul_two, iterate_add_apply, ih, ih]
    simp only [doubled]
    ring

variable {a c}

theorem doubled_form (ha : a % 4 = 1) (hc : c % 2 = 1) (k : ℕ) :
    ∃ t s : UInt64, (doubled a c k).1 = 1 + 2 ^ (k + 2) * t ∧
      (doubled a c k).2 = 2 ^ k * (2 * s + 1) := by
  induction k with
  | zero =>
    have h4 := mod_add_mul_div a 4
    have h2 := mod_add_mul_div c 2
    rw [ha] at h4
    rw [hc] at h2
    exact ⟨a / 4, c / 2, by simp only [doubled]; linear_combination -h4,
      by simp only [doubled]; linear_combination -h2⟩
  | succ k ih =>
    obtain ⟨t, s, ht, hs⟩ := ih
    refine ⟨t + 2 ^ (k + 1) * t * t, s + 2 ^ k * t * (2 * s + 1), ?_, ?_⟩
    · simp only [doubled, ht]
      ring
    · simp only [doubled, ht, hs]
      ring

theorem iterate_two_pow_64 (ha : a % 4 = 1) (hc : c % 2 = 1) (x : UInt64) :
    (affine a c)^[2 ^ 64] x = x := by
  obtain ⟨t, s, ht, hs⟩ := doubled_form ha hc 64
  rw [iterate_two_pow, ht, hs]
  linear_combination (4 * t * x + 2 * s + 1) * two_pow_64

theorem iterate_two_pow_63 (ha : a % 4 = 1) (hc : c % 2 = 1) (x : UInt64) :
    (affine a c)^[2 ^ 63] x = x + 2 ^ 63 := by
  obtain ⟨t, s, ht, hs⟩ := doubled_form ha hc 63
  rw [iterate_two_pow, ht, hs]
  linear_combination (2 * t * x + s) * two_pow_64

/-- Under the Hull–Dobell conditions, `2^k` steps add `2^k` to the state, modulo `2^(k+1)`. -/
theorem iterate_two_pow_eq (ha : a % 4 = 1) (hc : c % 2 = 1) (k : ℕ) (x : UInt64) :
    ∃ m, (affine a c)^[2 ^ k] x = x + 2 ^ k + 2 ^ (k + 1) * m := by
  obtain ⟨t, s, ht, hs⟩ := doubled_form ha hc k
  exact ⟨s + 2 * t * x, by rw [iterate_two_pow, ht, hs]; ring⟩

end Iterates

/-! ### Period -/

theorem minimalPeriod_eq_of_conditions {a c : UInt64} (ha : a % 4 = 1) (hc : c % 2 = 1)
    (x : UInt64) : minimalPeriod (affine a c) x = 2 ^ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply minimalPeriod_eq_prime_pow (k := 63)
  · intro h
    have h' : x + 2 ^ 63 = x := (iterate_two_pow_63 ha hc x).symm.trans h
    exact two_pow_63_ne (by simpa using h')
  · exact iterate_two_pow_64 ha hc x

/-- A map on words with a point of minimal period `2^64` reaches every word from that point, at
exactly one count of steps below `2^64`. -/
theorem existsUnique_iterate {f : UInt64 → UInt64} {x : UInt64}
    (h : minimalPeriod f x = 2 ^ 64) (y : UInt64) : ∃! n, n < 2 ^ 64 ∧ f^[n] x = y := by
  rw [← h]
  exact Orbit.existsUnique_iterate (S := Set.univ)
    (by rw [Nat.card_univ, Orbit.natCard_uint64, h]) (fun _ => trivial) trivial

/-! ### Reduction modulo a divisor of `2^64` -/

theorem cast_mod_size {N : ℕ} (hN : N ∣ 2 ^ 64) (n : ℕ) :
    ((n % 2 ^ 64 : ℕ) : ZMod N) = n := by
  rw [← ZMod.natCast_mod (n % 2 ^ 64) N, Nat.mod_mod_of_dvd _ hN, ZMod.natCast_mod]

/-- A word modulo a divisor `N` of `2^64`, as a ring homomorphism to `ZMod N`. -/
def reduce {N : ℕ} (hN : N ∣ 2 ^ 64) : UInt64 →+* ZMod N where
  toFun u := u.toNat
  map_one' := by simp
  map_mul' u v := by simp only [UInt64.toNat_mul, cast_mod_size hN, Nat.cast_mul]
  map_zero' := by simp
  map_add' u v := by simp only [UInt64.toNat_add, cast_mod_size hN, Nat.cast_add]

theorem reduce_apply {N : ℕ} (hN : N ∣ 2 ^ 64) (u : UInt64) : reduce hN u = u.toNat := rfl

theorem reduce_two {N : ℕ} (hN : N ∣ 2 ^ 64) : reduce hN 2 = 2 := by
  rw [reduce_apply]
  exact Nat.cast_ofNat

theorem reduce_surjective {N : ℕ} (hN : N ∣ 2 ^ 64) [NeZero N] : Surjective (reduce hN) := by
  intro z
  refine ⟨UInt64.ofNat z.val, ?_⟩
  rw [reduce_apply, UInt64.toNat_ofNat', cast_mod_size hN, ZMod.natCast_zmod_val]

/-! ### Bits -/

/-- Adding `2^k` and a multiple of `2^(k+1)` to a word complements its bit `k`. -/
theorem testBit_add_two_pow {k : ℕ} (hk : k < 64) {x y m : UInt64}
    (h : y = x + 2 ^ k + 2 ^ (k + 1) * m) : y.toNat.testBit k = !x.toNat.testBit k := by
  have hN : 2 ^ (k + 1) ∣ 2 ^ 64 := pow_dvd_pow 2 hk
  have hzero : (2 : ZMod (2 ^ (k + 1))) ^ (k + 1) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 ^ (k + 1))
  have hcast : (y.toNat : ZMod (2 ^ (k + 1))) = ((x.toNat + 2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
    have := congrArg (reduce hN) h
    simp only [map_add, map_mul, map_pow, reduce_two, hzero, zero_mul, add_zero] at this
    rw [← reduce_apply hN, this, reduce_apply, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
  have low : ∀ n : ℕ, (n % 2 ^ (k + 1)).testBit k = n.testBit k := by
    intro n
    simp [Nat.testBit_mod_two_pow]
  rw [← low, hmod, low, Nat.add_comm, Nat.testBit_two_pow_add_eq]

section Bits

variable {a c : UInt64} (ha : a % 4 = 1) (hc : c % 2 = 1) {k : ℕ} (hk : k < 64) (x : UInt64)
include ha hc hk

theorem testBit_iterate_add_two_pow (n : ℕ) :
    ((affine a c)^[n + 2 ^ k] x).toNat.testBit k = !((affine a c)^[n] x).toNat.testBit k := by
  obtain ⟨m, hm⟩ := iterate_two_pow_eq ha hc k ((affine a c)^[n] x)
  rw [add_comm, iterate_add_apply]
  exact testBit_add_two_pow hk hm

theorem periodic_testBit :
    Periodic (fun n => ((affine a c)^[n] x).toNat.testBit k) (2 ^ (k + 1)) := by
  intro n
  simp only
  rw [pow_succ, mul_two, ← add_assoc, testBit_iterate_add_two_pow ha hc hk,
    testBit_iterate_add_two_pow ha hc hk, Bool.not_not]

/-- Bit `k` of the state repeats after `p` steps exactly when `2^(k+1)` divides `p`. -/
theorem periodic_testBit_iff (p : ℕ) :
    Periodic (fun n => ((affine a c)^[n] x).toNat.testBit k) p ↔ 2 ^ (k + 1) ∣ p := by
  have hper := periodic_testBit ha hc hk x
  constructor
  · intro hp
    by_contra hnd
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero _)
    obtain ⟨j, o, ⟨i, rfl⟩, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hp0
    have hjk : j ≤ k := by
      by_contra hjk
      exact hnd (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _)
    have hodd : Periodic (fun n => ((affine a c)^[n] x).toNat.testBit k) (2 ^ k * (2 * i + 1)) := by
      have := hp.nat_mul (2 ^ (k - j))
      rwa [Nat.cast_id, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hjk] at this
    have h1 : ((affine a c)^[i * 2 ^ (k + 1) + 2 ^ k] x).toNat.testBit k =
        !((affine a c)^[0] x).toNat.testBit k := by
      have := hper.nat_mul i 0
      simp only [Nat.cast_id, zero_add] at this
      rw [testBit_iterate_add_two_pow ha hc hk, this]
    have h2 := hodd 0
    simp only [zero_add] at h2
    rw [show 2 ^ k * (2 * i + 1) = i * 2 ^ (k + 1) + 2 ^ k by ring, h1] at h2
    simp at h2
  · rintro ⟨q, rfl⟩
    rw [mul_comm]
    exact hper.nat_mul q

end Bits

/-! ### Necessity of the conditions -/

theorem reduce_iterate {N : ℕ} (hN : N ∣ 2 ^ 64) (a c x : UInt64) (n : ℕ) :
    reduce hN ((affine a c)^[n] x) =
      (fun r => reduce hN a * r + reduce hN c)^[n] (reduce hN x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih, affine, map_add, map_mul]

/-- Every iterate of a map is among the first four iterates when the fourth is. -/
theorem iterate_mem_first_four {α : Type} (F : α → α) (r : α)
    (h : ∃ i < 4, F^[4] r = F^[i] r) (n : ℕ) : ∃ i < 4, F^[n] r = F^[i] r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 4
    · exact ⟨n, hn, rfl⟩
    · obtain ⟨i, hi, hfi⟩ := h
      have : F^[n] r = F^[n - 4 + i] r := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
        rw [iterate_add_apply, hfi, ← iterate_add_apply, Nat.add_sub_cancel]
      rw [this]
      exact ih _ (by omega)

/-- An affine map on `ZMod 4` that fails the conditions misses a residue from every start. -/
theorem affine_mod_four_misses :
    ∀ A C r : ZMod 4, ¬(A = 1 ∧ (C = 1 ∨ C = 3)) →
      ∃ z : ZMod 4, (∀ i : Fin 4, (fun s => A * s + C)^[i] r ≠ z) ∧
        ∃ i : Fin 4, (fun s => A * s + C)^[4] r = (fun s => A * s + C)^[i] r := by
  decide

theorem conditions_of_minimalPeriod {a c x : UInt64}
    (h : minimalPeriod (affine a c) x = 2 ^ 64) : a % 4 = 1 ∧ c % 2 = 1 := by
  have hN : 4 ∣ 2 ^ 64 := ⟨2 ^ 62, by norm_num⟩
  have hA : reduce hN a = 1 ∧ (reduce hN c = 1 ∨ reduce hN c = 3) := by
    by_contra hbad
    obtain ⟨z, hz, i, hi⟩ := affine_mod_four_misses _ _ (reduce hN x) hbad
    obtain ⟨u, rfl⟩ := reduce_surjective hN z
    obtain ⟨n, ⟨-, hn⟩, -⟩ := existsUnique_iterate h u
    obtain ⟨i', hi', he⟩ := iterate_mem_first_four _ _ ⟨i, i.isLt, hi⟩ n
    exact hz ⟨i', hi'⟩ (by dsimp only; rw [← he, ← reduce_iterate, hn])
  have hmod : ∀ (u : UInt64) (v : ℕ), reduce hN u = v → u.toNat % 4 = v % 4 := fun u v h =>
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp (by rw [← reduce_apply hN, h])
  obtain ⟨ha, hc⟩ := hA
  have ha' := hmod a 1 (by rw [ha, Nat.cast_one])
  have hc' : c.toNat % 4 = 1 ∨ c.toNat % 4 = 3 := by
    rcases hc with hc | hc
    · exact Or.inl (hmod c 1 (by rw [hc, Nat.cast_one]))
    · exact Or.inr (hmod c 3 (by rw [hc, Nat.cast_ofNat]))
  constructor
  · apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod] using ha'
  · apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod]
    simp
    omega

/-! ### The generator -/

/-- Hull and Dobell's theorem for the modulus `2^64`: `affine a c` cycles through all `2^64` words
from `x` if and only if `a % 4 = 1` and `c % 2 = 1`. -/
theorem minimalPeriod_affine_iff (a c x : UInt64) :
    minimalPeriod (affine a c) x = 2 ^ 64 ↔ a % 4 = 1 ∧ c % 2 = 1 :=
  ⟨conditions_of_minimalPeriod, fun ⟨ha, hc⟩ => minimalPeriod_eq_of_conditions ha hc x⟩

theorem step_conditions : (6364136223846793005 : UInt64) % 4 = 1 ∧
    (1442695040888963407 : UInt64) % 2 = 1 := by decide

/-- From every state, `step` returns to the state after `2^64` steps and not before. -/
theorem step_minimalPeriod (x : UInt64) : minimalPeriod step x = 2 ^ 64 :=
  minimalPeriod_eq_of_conditions step_conditions.1 step_conditions.2 x

/-- `step` is a bijection on words. -/
theorem step_bijective : Bijective step := by
  have hid : ∀ x, step^[2 ^ 64] x = x := fun x =>
    iterate_two_pow_64 step_conditions.1 step_conditions.2 x
  have h1 : 2 ^ 64 - 1 + 1 = 2 ^ 64 := by norm_num
  refine bijective_iff_has_inverse.mpr ⟨step^[2 ^ 64 - 1], fun x => ?_, fun x => ?_⟩
  · have := iterate_add_apply step (2 ^ 64 - 1) 1 x
    rw [h1, hid, iterate_one] at this
    exact this.symm
  · have := iterate_add_apply step 1 (2 ^ 64 - 1) x
    rw [Nat.add_comm 1, h1, hid, iterate_one] at this
    exact this.symm

/-- From every state `x`, `advance n x` takes each word `y` at exactly one count `n`. -/
theorem advance_existsUnique (x y : UInt64) : ∃! n, advance n x = y := by
  obtain ⟨n, ⟨hn, hny⟩, huniq⟩ := existsUnique_iterate (step_minimalPeriod x) y
  have hsize : n % 2 ^ 64 = n := Nat.mod_eq_of_lt hn
  refine ⟨UInt64.ofNat n, ?_, fun m (hm : advance m x = y) => ?_⟩
  · show advance _ x = y
    rw [advance_eq_iterate, UInt64.toNat_ofNat', hsize, hny]
  rw [advance_eq_iterate] at hm
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', hsize]
  exact huniq _ ⟨m.toNat_lt_size, hm⟩

/-- No positive count of steps below `2^64` returns `advance` to its starting state. -/
theorem advance_ne_self (x n : UInt64) (hn : n ≠ 0) : advance n x ≠ x := by
  intro h
  obtain ⟨_, _, huniq⟩ := advance_existsUnique x x
  have h0 : advance 0 x = x := rfl
  exact hn ((huniq n h).trans (huniq 0 h0).symm)

/-- Bit `k` of the state of `step` repeats after `p` steps exactly when `2^(k+1)` divides `p`. -/
theorem step_periodic_testBit_iff {k : ℕ} (hk : k < 64) (x : UInt64) (p : ℕ) :
    Periodic (fun n => (step^[n] x).toNat.testBit k) p ↔ 2 ^ (k + 1) ∣ p :=
  periodic_testBit_iff step_conditions.1 step_conditions.2 hk x p

end Verified.Examples.Lcg
