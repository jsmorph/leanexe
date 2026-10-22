import Library.Random.Lcg.Period
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fin.VecNotation

/-! These lemmas describe the lattice structure of the LCG of `Examples/Lcg/Program.lean`.  An
integer vector `s` of length `t` lies in `Dual t` when `∑ s_k a^k ≡ 0 (mod 2^64)`, for `a` the
multiplier.  Since `k` steps from `x` give `a^k x` plus `k` steps from 0, `∑ s_k y_k` at the tuple
`y` of `t` successive states from any word is congruent modulo `2^64` to its value `d` at the tuple
from 0, and the tuples lie on the parallel hyperplanes `∑ s_k y_k = d + j 2^64` for integers `j`.
Over the cube `[0, 2^64)^t`, `∑ s_k y_k` takes values in an interval of length
`∑ |s_k| (2^64 - 1)`, so for a nonzero `s` at most `∑ |s_k|` of these hyperplanes hold tuples,
which `hyperplanes` states, and `hyperplanes_two` to `hyperplanes_six` apply it with fixed vectors
for two to six successive states. -/

namespace Library.Random.Lcg

open Function
open scoped UInt64.CommRing

/-- `k` steps of `affine a c` from `x` are `a^k x` plus `k` steps from 0. -/
theorem iterate_affine_eq (a c x : UInt64) (k : Nat) :
    (affine a c)^[k] x = a ^ k * x + (affine a c)^[k] 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply', affine, affine]
    ring

/-- The integer vectors `s` with `∑ s_k a^k ≡ 0 (mod 2^64)`, for `a` the multiplier and
`k = 0, …, t - 1`: the dual lattice, in Knuth's normalization, of the lattice of the tuples of `t`
successive states. -/
def Dual (t : Nat) (s : Fin t → ℤ) : Prop :=
  (∑ k, s k * (multiplier.toNat : ℤ) ^ (k : Nat)) % 2 ^ 64 = 0

instance (t : Nat) (s : Fin t → ℤ) : Decidable (Dual t s) := inferInstanceAs (Decidable (_ = _))

/-- `∑ s_k y_k` at the tuple `y` of `t` successive states from `x`. -/
def dotStates (t : Nat) (s : Fin t → ℤ) (x : UInt64) : ℤ :=
  ∑ k, s k * ((step^[k] x).toNat : ℤ)

/-- For `s` in `Dual t`, `∑ s_k y_k` at the tuple of successive states from any word is congruent
modulo `2^64` to its value at the tuple from 0. -/
theorem dotStates_modEq {t : Nat} {s : Fin t → ℤ} (hs : Dual t s) (x : UInt64) :
    dotStates t s x ≡ dotStates t s 0 [ZMOD 2 ^ 64] := by
  have hN : (2 ^ 64 : ℕ) ∣ 2 ^ 64 := dvd_rfl
  have hcast : ∀ u : UInt64, ((u.toNat : ℤ) : ZMod (2 ^ 64)) = reduce hN u := fun u => by
    rw [reduce_apply]; push_cast; rfl
  have hdual : (∑ k, (s k : ZMod (2 ^ 64)) * reduce hN multiplier ^ (k : Nat)) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (∑ k, s k * (multiplier.toNat : ℤ) ^ (k : Nat)) (2 ^ 64)).mpr (by
        have := Int.dvd_of_emod_eq_zero hs
        exact_mod_cast this)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, hcast] at h
    exact h
  have hstep : ∀ k : ℕ, reduce hN (step^[k] x) =
      reduce hN multiplier ^ k * reduce hN x + reduce hN (step^[k] 0) := fun k => by
    rw [show step^[k] = (affine multiplier increment)^[k] from rfl, iterate_affine_eq, map_add,
      map_mul, map_pow]
  have key : ((dotStates t s x : ℤ) : ZMod (2 ^ 64)) = ((dotStates t s 0 : ℤ) : ZMod (2 ^ 64)) := by
    simp only [dotStates, Int.cast_sum, Int.cast_mul, hcast, hstep, mul_add,
      Finset.sum_add_distrib]
    have : ∑ k, (s k : ZMod (2 ^ 64)) * (reduce hN multiplier ^ (k : Nat) * reduce hN x) =
        (∑ k, (s k : ZMod (2 ^ 64)) * reduce hN multiplier ^ (k : Nat)) * reduce hN x := by
      rw [Finset.sum_mul]; congr 1; funext k; ring
    rw [this, hdual, zero_mul, zero_add]
  have := (ZMod.intCast_eq_intCast_iff _ _ (2 ^ 64)).mp key
  exact_mod_cast this

/-- For `0 ≤ y ≤ 2^64 - 1`, `c y` lies between `min c 0 · (2^64 - 1)` and
`(min c 0 + |c|) · (2^64 - 1)`. -/
theorem term_bounds (c y : ℤ) (hy0 : 0 ≤ y) (hy1 : y ≤ 2 ^ 64 - 1) :
    min c 0 * (2 ^ 64 - 1) ≤ c * y ∧ c * y ≤ (min c 0 + |c|) * (2 ^ 64 - 1) := by
  rcases le_or_gt 0 c with h | h
  · rw [min_eq_right h, abs_of_nonneg h]
    constructor <;> nlinarith
  · rw [min_eq_left h.le, abs_of_neg h]
    constructor <;> nlinarith

/-- For a nonzero `s` in `Dual t`, the tuples of `t` successive states from every word lie on at
most `∑ |s_k|` parallel hyperplanes: `∑ s_k y_k` takes at most `∑ |s_k|` values. -/
theorem hyperplanes {t : Nat} {s : Fin t → ℤ} (hs : Dual t s) (h0 : s ≠ 0) :
    ∃ P : Finset ℤ, (P.card : ℤ) ≤ ∑ k, |s k| ∧ ∀ x : UInt64, dotStates t s x ∈ P := by
  set S := ∑ k, |s k| with hSdef
  set L := ∑ k, min (s k) 0 * (2 ^ 64 - 1) with hLdef
  have hS : 1 ≤ S := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h0
    have h1 : |s k| ≤ S := Finset.single_le_sum (fun i _ => abs_nonneg (s i)) (Finset.mem_univ k)
    have h2 : 1 ≤ |s k| := Int.one_le_abs hk
    omega
  have hrange : ∀ x : UInt64, L ≤ dotStates t s x ∧ dotStates t s x ≤ L + S * (2 ^ 64 - 1) := by
    intro x
    have hb := fun k => term_bounds (s k) ((step^[k] x).toNat : ℤ) (Int.natCast_nonneg _)
      (by have := (step^[k] x).toNat_lt; omega)
    constructor
    · exact Finset.sum_le_sum fun k _ => (hb k).1
    · calc dotStates t s x ≤ ∑ k, (min (s k) 0 + |s k|) * (2 ^ 64 - 1) :=
            Finset.sum_le_sum fun k _ => (hb k).2
        _ = L + S * (2 ^ 64 - 1) := by
          rw [hLdef, hSdef, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
  set d := dotStates t s 0
  set d' := L + (d - L) % 2 ^ 64 with hd'
  refine ⟨(Finset.Ico (0 : ℤ) S).image fun j => d' + j * 2 ^ 64, ?_, fun x => ?_⟩
  · have hc : ((Finset.Ico (0 : ℤ) S).image fun j => d' + j * 2 ^ 64).card ≤ (S - 0).toNat :=
      Finset.card_image_le.trans_eq (Int.card_Ico 0 S)
    have hS' : ((S - 0).toNat : ℤ) = S := by rw [sub_zero]; exact Int.toNat_of_nonneg (by omega)
    calc (((Finset.Ico (0 : ℤ) S).image fun j => d' + j * 2 ^ 64).card : ℤ)
        ≤ ((S - 0).toNat : ℤ) := by exact_mod_cast hc
      _ = S := hS'
  · obtain ⟨hL, hU⟩ := hrange x
    have hmod := dotStates_modEq hs x
    rw [Int.ModEq] at hmod
    rw [Finset.mem_image]
    refine ⟨(dotStates t s x - d') / 2 ^ 64, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      constructor <;> omega
    · omega

/-! ### Two to six successive states

`shortest2` to `shortest6` are the shortest vectors of `Dual t`, which `Examples/Lcg/Spectral.lean`
proves, and by computation `shortest2` to `shortest5` also have the smallest sums of magnitudes.
`plane6` has the sum of magnitudes 2,296, smaller than the 2,818 of `shortest6`. -/

/-- The shortest vector of `Dual 2`. -/
def shortest2 : Fin 2 → ℤ := ![1381628436, 2627121436]
/-- The shortest vector of `Dual 3`. -/
def shortest3 : Fin 3 → ℤ := ![-2498093, -397201, 8218]
/-- The shortest vector of `Dual 4`. -/
def shortest4 : Fin 4 → ℤ := ![28729, 22523, -11836, 51380]
/-- The shortest vector of `Dual 5`. -/
def shortest5 : Fin 5 → ℤ := ![1079, -547, 5024, -4057, 1581]
/-- The shortest vector of `Dual 6`. -/
def shortest6 : Fin 6 → ℤ := ![801, -177, 290, 952, 345, 253]

/-- A vector of `Dual 6` with a smaller sum of magnitudes than `shortest6`. -/
def plane6 : Fin 6 → ℤ := ![1502, 30, 36, -6, -264, -458]

/-- The pairs of successive states lie on at most 4,008,749,872 parallel lines. -/
theorem hyperplanes_two : ∃ P : Finset ℤ, P.card ≤ 4008749872 ∧ ∀ x, dotStates 2 shortest2 x ∈ P := by
  obtain ⟨P, hP, hx⟩ := hyperplanes (s := shortest2) (by decide +kernel) (by decide +kernel)
  have : ∑ k, |shortest2 k| = 4008749872 := by decide +kernel
  exact ⟨P, by omega, hx⟩

/-- The triples of successive states lie on at most 2,903,512 parallel planes. -/
theorem hyperplanes_three : ∃ P : Finset ℤ, P.card ≤ 2903512 ∧ ∀ x, dotStates 3 shortest3 x ∈ P := by
  obtain ⟨P, hP, hx⟩ := hyperplanes (s := shortest3) (by decide +kernel) (by decide +kernel)
  have : ∑ k, |shortest3 k| = 2903512 := by decide +kernel
  exact ⟨P, by omega, hx⟩

/-- The 4-tuples of successive states lie on at most 114,468 parallel hyperplanes. -/
theorem hyperplanes_four : ∃ P : Finset ℤ, P.card ≤ 114468 ∧ ∀ x, dotStates 4 shortest4 x ∈ P := by
  obtain ⟨P, hP, hx⟩ := hyperplanes (s := shortest4) (by decide +kernel) (by decide +kernel)
  have : ∑ k, |shortest4 k| = 114468 := by decide +kernel
  exact ⟨P, by omega, hx⟩

/-- The 5-tuples of successive states lie on at most 12,288 parallel hyperplanes. -/
theorem hyperplanes_five : ∃ P : Finset ℤ, P.card ≤ 12288 ∧ ∀ x, dotStates 5 shortest5 x ∈ P := by
  obtain ⟨P, hP, hx⟩ := hyperplanes (s := shortest5) (by decide +kernel) (by decide +kernel)
  have : ∑ k, |shortest5 k| = 12288 := by decide +kernel
  exact ⟨P, by omega, hx⟩

/-- The 6-tuples of successive states lie on at most 2,296 parallel hyperplanes. -/
theorem hyperplanes_six : ∃ P : Finset ℤ, P.card ≤ 2296 ∧ ∀ x, dotStates 6 plane6 x ∈ P := by
  obtain ⟨P, hP, hx⟩ := hyperplanes (s := plane6) (by decide +kernel) (by decide +kernel)
  have : ∑ k, |plane6 k| = 2296 := by decide +kernel
  exact ⟨P, by omega, hx⟩

end Library.Random.Lcg
