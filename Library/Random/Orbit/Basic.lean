import LeanExe.Dialect.Loop
import Mathlib.Data.FinEnum
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Nat

/-! Facts about iterates and orbits that the generator examples share: `LeanExe.loop` with an unused
index computes an iterate, the minimal period of a point is the `N` whose multiples are its periods,
an orbit that stays in a set with as many elements as the period reaches each element once per
period, and a point that returns after `N` steps and after no `N / q` steps, for the primes `q`
that divide `N`, has the minimal period `N`.  The last lemmas state the programs' test of a bit of
a word as `Nat.testBit`, the value of `1 <<< i`, and the count of the words with given top bits. -/

namespace Library.Random.Orbit

open Function

theorem loop_eq_iterate {α : Type} (f : α → α) (n : UInt64) (x : α) :
    LeanExe.loop n x (fun _ s => f s) = f^[n.toNat] x := by
  unfold LeanExe.loop
  induction n.toNat with
  | zero => rfl
  | succ m ih => rw [Nat.fold_succ, ih, iterate_succ_apply']

theorem minimalPeriod_eq_of_isPeriodicPt_iff {α : Type} {f : α → α} {x : α} {N : ℕ}
    (h : ∀ n, IsPeriodicPt f n x ↔ N ∣ n) : minimalPeriod f x = N :=
  Nat.dvd_antisymm (isPeriodicPt_iff_minimalPeriod_dvd.mp ((h N).mpr dvd_rfl))
    ((h _).mp (isPeriodicPt_minimalPeriod f x))

/-- When the orbit of `x` stays in a finite set `S` with as many elements as the minimal period of
`x`, `f` reaches each element of `S` from `x` at exactly one count below the period. -/
theorem existsUnique_iterate {α : Type} {f : α → α} {x : α} {S : Set α} [Finite S]
    (hS : Nat.card S = minimalPeriod f x) (hmem : ∀ n, f^[n] x ∈ S) {y : α} (hy : y ∈ S) :
    ∃! n, n < minimalPeriod f x ∧ f^[n] x = y := by
  let g : Fin (minimalPeriod f x) → S := fun n => ⟨f^[n] x, hmem n⟩
  have ginj : Injective g := fun m n hmn =>
    Fin.ext (iterate_injOn_Iio_minimalPeriod m.isLt n.isLt (congrArg Subtype.val hmn))
  obtain ⟨n, hn⟩ := (ginj.bijective_of_nat_card_le (by rw [hS, Nat.card_eq_fintype_card,
    Fintype.card_fin])).2 ⟨y, hy⟩
  have hn' : f^[n] x = y := congrArg Subtype.val hn
  exact ⟨n, ⟨n.isLt, hn'⟩, fun m hm =>
    iterate_injOn_Iio_minimalPeriod hm.1 n.isLt (hm.2.trans hn'.symm)⟩

theorem natCard_uint64 : Nat.card UInt64 = 2 ^ 64 := by
  rw [Nat.card_eq_fintype_card, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt64]

/-- A point that returns after `N` steps, and after no `N / q` steps for any prime `q` that divides
`N`, has the minimal period `N`.  The hypotheses follow `orderOf_eq_of_pow_and_pow_div_prime`, which
Mathlib states for the order of an element of a monoid and not for `minimalPeriod`. -/
theorem minimalPeriod_eq_of_primes {α : Type} {f : α → α} {x : α} {N : Nat} (hx : f^[N] x = x)
    (hne : ∀ q, q.Prime → q ∣ N → f^[N / q] x ≠ x) : minimalPeriod f x = N := by
  have hper : IsPeriodicPt f N x := hx
  obtain ⟨c, hc⟩ := hper.minimalPeriod_dvd
  by_contra hneq
  have hc1 : c ≠ 1 := fun h => hneq (by rw [hc, h, Nat.mul_one])
  obtain ⟨q, hq, e, he⟩ := Nat.exists_prime_and_dvd hc1
  have hqN : q ∣ N := ⟨minimalPeriod f x * e, by rw [hc, he]; ring⟩
  apply hne q hq hqN
  rw [show N / q = minimalPeriod f x * e by
    rw [hc, he, show minimalPeriod f x * (q * e) = q * (minimalPeriod f x * e) by ring,
      Nat.mul_div_cancel_left _ hq.pos]]
  exact (isPeriodicPt_minimalPeriod f x).mul_const e

/-- The programs' test of bit `k` of `n`, `(n >>> k) &&& 1 != 0`, is bit `k` of `n.toNat`. -/
theorem shift_and_one_ne_zero (n : UInt64) {k : Nat} (hk : k < 64) :
    ((n >>> UInt64.ofNat k) &&& 1 != 0) = n.toNat.testBit k := by
  have h : ((n >>> UInt64.ofNat k) &&& 1).toNat = n.toNat / 2 ^ k % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [UInt64.toNat_ofNat', UInt64.toNat_one]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk,
      Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff, bne_iff_ne, ne_eq,
    ← UInt64.toNat_inj, h, UInt64.toNat_zero, decide_eq_true_iff]
  omega

/-- `(1 <<< i).toNat = 2^i` for `i < 64`. -/
theorem toNat_one_shiftLeft {i : Nat} (hi : i < 64) :
    ((1 : UInt64) <<< UInt64.ofNat i).toNat = 2 ^ i := by
  rw [UInt64.toNat_shiftLeft]
  simp only [UInt64.toNat_ofNat', UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt hi, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hi)]

/-- Exactly `2^(64 - j)` words have the top `j` bits `v`. -/
theorem card_topBits {j v : Nat} (hj : j ≤ 64) (hv : v < 2 ^ j) :
    ((Finset.univ : Finset UInt64).filter fun y => y.toNat / 2 ^ (64 - j) = v).card =
      2 ^ (64 - j) := by
  have hm : 2 ^ (64 - j) * 2 ^ j = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  rw [← Finset.card_map ⟨UInt64.toNat, fun a b h => UInt64.toNat_inj.mp h⟩]
  have : Finset.map ⟨UInt64.toNat, fun a b h => UInt64.toNat_inj.mp h⟩
      ((Finset.univ : Finset UInt64).filter fun y => y.toNat / 2 ^ (64 - j) = v) =
      Finset.Ico (v * 2 ^ (64 - j)) ((v + 1) * 2 ^ (64 - j)) := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hy]
      constructor
      · exact Nat.div_mul_le_self _ _
      · rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add (Nat.two_pow_pos _)
    · rintro ⟨h1, h2⟩
      have hn : n < 2 ^ 64 := by
        calc n < (v + 1) * 2 ^ (64 - j) := h2
          _ ≤ 2 ^ j * 2 ^ (64 - j) := Nat.mul_le_mul_right _ hv
          _ = 2 ^ 64 := by rw [Nat.mul_comm, hm]
      have hto : (UInt64.ofNat n).toNat = n := by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]
      refine ⟨UInt64.ofNat n, ?_, hto⟩
      rw [hto]
      exact Nat.div_eq_of_lt_le h1 h2
  rw [this, Nat.card_Ico, Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]

end Library.Random.Orbit
