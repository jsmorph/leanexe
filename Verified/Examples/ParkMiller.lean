import Verified.Examples.Orbit
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-! The minimal standard generator of Park and Miller: each step replaces the state `x` with
`16807 * x % 2147483647`, where `2147483647 = 2^31 - 1`.  The state lies in `[1, 2^31 - 2]`, so the
product is below `2^46` and the program computes it with word arithmetic without overflow.  The
modulus is prime, by Lucas's test with the witness 16807, and 16807 has order `2^31 - 2` modulo
it, so from every state in the range the generator returns after `2^31 - 2` steps and not before,
and it reaches each state in the range once per period.  The finite checks are eight powers of
16807 modulo `2^31 - 1`, which Mathlib's `reduce_mod_char` evaluates by repeated squaring.  The
programs are `step` and `advance`. -/

namespace Verified.Examples.ParkMiller

/-- One step of the generator: `16807 * x % 2147483647`. -/
def step (x : UInt64) : UInt64 := 16807 * x % 2147483647

/-- The state after `n` steps from `x`. -/
def advance (n x : UInt64) : UInt64 := LeanExe.loop n x fun _ s => step s

open Function

theorem advance_eq_iterate (n x : UInt64) : advance n x = step^[n.toNat] x :=
  Orbit.loop_eq_iterate step n x

/-! ### The modulus and the multiplier -/

/-- The prime factors of `2147483646 = 2 · 3^2 · 7 · 11 · 31 · 151 · 331`. -/
theorem prime_dvd_order {q : ℕ} (hq : q.Prime) (h : q ∣ 2147483646) :
    q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 11 ∨ q = 31 ∨ q = 151 ∨ q = 331 := by
  rw [show (2147483646 : ℕ) = 2 * 3 ^ 2 * 7 * 11 * 31 * 151 * 331 by norm_num] at h
  simp only [hq.dvd_mul, or_assoc] at h
  have e : ∀ r, r.Prime → q ∣ r → q = r := fun r hr h => (Nat.prime_dvd_prime_iff_eq hq hr).mp h
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (e 2 (by norm_num) h)
  · exact Or.inr (Or.inl (e 3 (by norm_num) (hq.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr (Or.inl (e 7 (by norm_num) h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (e 11 (by norm_num) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e 31 (by norm_num) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e 151 (by norm_num) h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e 331 (by norm_num) h))))))

theorem pow_eq_one_iff {p : ℕ} (hp : 1 < p) (a e : ℕ) :
    (a : ZMod p) ^ e = 1 ↔ a ^ e % p = 1 := by
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp]

theorem pow_order : (16807 : ZMod 2147483647) ^ 2147483646 = 1 := by
  reduce_mod_char

theorem pow_div_prime_ne_one (q : ℕ) (hq : q.Prime) (h : q ∣ 2147483646) :
    (16807 : ZMod 2147483647) ^ (2147483646 / q) ≠ 1 := by
  rcases prime_dvd_order hq h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (simp only [Nat.reduceDiv]; reduce_mod_char; decide +kernel)

/-- `2^31 - 1` is prime, by Lucas's test with the witness 16807. -/
theorem prime_modulus : Nat.Prime 2147483647 :=
  lucas_primality 2147483647 16807 pow_order pow_div_prime_ne_one

instance : Fact (Nat.Prime 2147483647) := ⟨prime_modulus⟩

/-- 16807 is a primitive root modulo `2^31 - 1`. -/
theorem orderOf_multiplier : orderOf (16807 : ZMod 2147483647) = 2147483646 :=
  orderOf_eq_of_pow_and_pow_div_prime (by norm_num) pow_order pow_div_prime_ne_one

/-! ### Iterates -/

/-- The words in `[1, 2^31 - 2]`. -/
def Range : Set UInt64 := {y | 0 < y.toNat ∧ y.toNat < 2147483647}

theorem mem_range_iff (y : UInt64) : y ∈ Range ↔ 0 < y ∧ y < 2147483647 := by
  simp [Range, UInt64.lt_iff_toNat_lt]

theorem toNat_step {x : UInt64} (hx : x.toNat < 2147483647) :
    (step x).toNat = 16807 * x.toNat % 2147483647 := by
  simp only [step, UInt64.toNat_mod, UInt64.toNat_mul, UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt (show 16807 * x.toNat < 2 ^ 64 by omega)]

theorem toNat_iterate {x : UInt64} (hx : x.toNat < 2147483647) (n : ℕ) :
    (step^[n] x).toNat = 16807 ^ n * x.toNat % 2147483647 := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt hx]
  | succ n ih =>
    have hlt : (step^[n] x).toNat < 2147483647 := by
      rw [ih]
      exact Nat.mod_lt _ (by norm_num)
    rw [iterate_succ_apply', toNat_step hlt, ih, Nat.mul_mod_mod, pow_succ]
    congr 1
    ring

theorem step_mem {x : UInt64} (hx : x ∈ Range) : step x ∈ Range := by
  obtain ⟨h0, h1⟩ := hx
  refine ⟨?_, by rw [toNat_step h1]; exact Nat.mod_lt _ (by norm_num)⟩
  rw [toNat_step h1, Nat.pos_iff_ne_zero, Ne, ← Nat.dvd_iff_mod_eq_zero, prime_modulus.dvd_mul]
  rintro (h | h)
  · exact absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num)
  · exact absurd (Nat.le_of_dvd h0 h) (by omega)

theorem iterate_mem {x : UInt64} (hx : x ∈ Range) (n : ℕ) : step^[n] x ∈ Range := by
  induction n with
  | zero => exact hx
  | succ n ih => rw [iterate_succ_apply']; exact step_mem ih

theorem isPeriodicPt_iff {x : UInt64} (hx : x ∈ Range) (n : ℕ) :
    IsPeriodicPt step n x ↔ 2147483646 ∣ n := by
  obtain ⟨h0, h1⟩ := hx
  rw [← orderOf_multiplier, orderOf_dvd_iff_pow_eq_one]
  have hX : (x.toNat : ZMod 2147483647) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt h0 h1
  constructor
  · intro h
    have hc := congrArg (fun u : UInt64 => (u.toNat : ZMod 2147483647)) h.eq
    simp only [toNat_iterate h1, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
    exact mul_right_cancel₀ hX (hc.trans (one_mul _).symm)
  · intro h
    show step^[n] x = x
    apply UInt64.toNat_inj.mp
    have h' := (pow_eq_one_iff (p := 2147483647) (by norm_num) 16807 n).mp (by rw [Nat.cast_ofNat]; exact h)
    rw [toNat_iterate h1, Nat.mul_mod, h', one_mul, Nat.mod_mod, Nat.mod_eq_of_lt h1]

/-! ### Period -/

/-- From every state in `[1, 2^31 - 2]`, `step` returns after `2^31 - 2` steps and not before. -/
theorem step_minimalPeriod {x : UInt64} (hx : x ∈ Range) : minimalPeriod step x = 2147483646 :=
  Orbit.minimalPeriod_eq_of_isPeriodicPt_iff (isPeriodicPt_iff hx)

/-- The words in `[1, 2^31 - 2]`, numbered from 0. -/
def rangeEquiv : Range ≃ Fin 2147483646 where
  toFun y := ⟨y.1.toNat - 1, by have := y.2.2; omega⟩
  invFun i := ⟨UInt64.ofNat (i.1 + 1), by
    have := i.isLt
    show 0 < (UInt64.ofNat (i.1 + 1)).toNat ∧ (UInt64.ofNat (i.1 + 1)).toNat < 2147483647
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega⟩
  left_inv y := by
    have := y.2.1
    apply Subtype.ext
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_ofNat']
    rw [Nat.sub_add_cancel this, Nat.mod_eq_of_lt y.1.toNat_lt_size]
  right_inv i := by
    have := i.isLt
    apply Fin.ext
    simp only [UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- From every state `x` in `[1, 2^31 - 2]`, `step` reaches each state `y` in the range at exactly
one count of steps below `2^31 - 2`. -/
theorem existsUnique_iterate {x y : UInt64} (hx : x ∈ Range) (hy : y ∈ Range) :
    ∃! n, n < 2147483646 ∧ step^[n] x = y := by
  rw [← step_minimalPeriod hx]
  exact Orbit.existsUnique_iterate (by rw [Nat.card_congr rangeEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fin, step_minimalPeriod hx]) (iterate_mem hx) hy

/-- `advance` keeps a state in `[1, 2^31 - 2]` in the range, and from every state `x` in the range
it reaches each state `y` in the range at exactly one count `n` below `2^31 - 2`. -/
theorem advance_existsUnique {x y : UInt64} (hx : 0 < x ∧ x < 2147483647)
    (hy : 0 < y ∧ y < 2147483647) : ∃! n : UInt64, n < 2147483646 ∧ advance n x = y := by
  rw [← mem_range_iff] at hx hy
  obtain ⟨n, ⟨hn, hny⟩, huniq⟩ := existsUnique_iterate hx hy
  have hsize : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  refine ⟨UInt64.ofNat n, ⟨?_, ?_⟩, fun m ⟨hm, hmy⟩ => ?_⟩
  · rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', hsize]
    exact hn
  · rw [advance_eq_iterate, UInt64.toNat_ofNat', hsize, hny]
  · rw [advance_eq_iterate] at hmy
    rw [UInt64.lt_iff_toNat_lt] at hm
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat', hsize]
    exact huniq _ ⟨hm, hmy⟩

theorem advance_mem {x : UInt64} (hx : 0 < x ∧ x < 2147483647) (n : UInt64) :
    0 < advance n x ∧ advance n x < 2147483647 := by
  rw [← mem_range_iff] at hx ⊢
  rw [advance_eq_iterate]
  exact iterate_mem hx _

/-- The state 0 is a fixed point, which is why the seed must lie in `[1, 2^31 - 2]`. -/
theorem step_zero : step 0 = 0 := rfl

end Verified.Examples.ParkMiller
