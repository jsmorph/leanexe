import LeanExe.Dialect.Loop
import Mathlib.Data.FinEnum
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-! Facts about iterates and orbits that the generator examples share: `LeanExe.loop` with an unused
index computes an iterate, the minimal period of a point is the `N` whose multiples are its periods,
an orbit that stays in a set with as many elements as the period reaches each element once per
period, and a point that returns after `N` steps and after no `N / q` steps, for the primes `q`
that divide `N`, has the minimal period `N`. -/

namespace Examples.Orbit

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

end Examples.Orbit
