import LeanExe.Examples.Drone
import Mathlib.Tactic.Linarith
import Project.IR.Combinators

/-! `ceilSqrt` is the exact ceiling square root for inputs up to `2^32`. -/

namespace Project.Drone

open LeanExe.Examples.Drone
open Project.IR (loop_induction)

/-- One halving of `ceilSqrt`'s bracket. -/
def sqrtStep (n : UInt64) (_ : UInt64) (bracket : UInt64 × UInt64) : UInt64 × UInt64 :=
  let mid := (bracket.1 + bracket.2) / 2
  (if bracket.1 < bracket.2 && mid * mid < n then mid + 1 else bracket.1,
    if bracket.1 < bracket.2 && n ≤ mid * mid then mid else bracket.2)

theorem ceilSqrt_loop (n : UInt64) :
    ceilSqrt n = (LeanExe.loop 17 ((0 : UInt64), (65536 : UInt64)) (sqrtStep n)).1 := by
  unfold ceilSqrt sqrtStep
  rfl

namespace Sqrt

/-- The bracket after `k` halvings: `lo ≤ hi ≤ 65536`, `n ≤ hi²`, every `j < lo` has `j² < n`,
and the width is below `2^(17 - k)`. -/
def Bracket (n : UInt64) (k : Nat) (b : UInt64 × UInt64) : Prop :=
  b.1.toNat ≤ b.2.toNat ∧ b.2.toNat ≤ 65536 ∧ n.toNat ≤ b.2.toNat * b.2.toNat ∧
    (∀ j, j < b.1.toNat → j * j < n.toNat) ∧ b.2.toNat - b.1.toNat < 2 ^ (17 - k)

theorem bracket_step (n : UInt64) (k : Nat) (hk : k < 17) (i : UInt64) (b : UInt64 × UInt64)
    (h : Bracket n k b) : Bracket n (k + 1) (sqrtStep n i b) := by
  obtain ⟨lo, hi⟩ := b
  obtain ⟨hlh, hhi, hup, hlow, hwidth⟩ := h
  simp only at hlh hhi hup hlow hwidth
  have hpow : 2 ^ (17 - k) = 2 * 2 ^ (17 - (k + 1)) := by
    rw [show 17 - k = (17 - (k + 1)) + 1 by omega, pow_succ, Nat.mul_comm]
  rw [hpow] at hwidth
  have hsum : (lo + hi).toNat = lo.toNat + hi.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hmid : ((lo + hi) / 2).toNat = (lo.toNat + hi.toNat) / 2 := by
    rw [UInt64.toNat_div, hsum]; rfl
  have hsq : ((lo + hi) / 2 * ((lo + hi) / 2)).toNat =
      (lo.toNat + hi.toNat) / 2 * ((lo.toNat + hi.toNat) / 2) := by
    rw [UInt64.toNat_mul, hmid]
    apply Nat.mod_eq_of_lt
    have : (lo.toNat + hi.toNat) / 2 ≤ 65536 := by omega
    have := Nat.mul_le_mul this this
    exact lt_of_le_of_lt this (by decide)
  have hinc : ((lo + hi) / 2 + 1).toNat = (lo.toNat + hi.toNat) / 2 + 1 := by
    rw [UInt64.toNat_add, hmid]; exact Nat.mod_eq_of_lt (by simp; omega)
  unfold sqrtStep Bracket
  by_cases hlt : lo < hi
  · have hltN : lo.toNat < hi.toNat := UInt64.lt_iff_toNat_lt.mp hlt
    by_cases htest : (lo + hi) / 2 * ((lo + hi) / 2) < n
    · have htestN := UInt64.lt_iff_toNat_lt.mp htest
      rw [hsq] at htestN
      have hne : ¬n ≤ (lo + hi) / 2 * ((lo + hi) / 2) := by
        rw [UInt64.le_iff_toNat_le, hsq]; omega
      simp only [hlt, htest, hne, decide_true, decide_false, Bool.and_true, Bool.and_false,
        ite_true, ite_false, Bool.false_eq_true]
      rw [hinc]
      refine ⟨by omega, hhi, hup, fun j hj => ?_, by omega⟩
      have hjm : j ≤ (lo.toNat + hi.toNat) / 2 := by omega
      exact lt_of_le_of_lt (Nat.mul_self_le_mul_self hjm) htestN
    · have hle : n ≤ (lo + hi) / 2 * ((lo + hi) / 2) := by
        rw [UInt64.le_iff_toNat_le]; rw [UInt64.lt_iff_toNat_lt] at htest; omega
      have hleN := UInt64.le_iff_toNat_le.mp hle
      rw [hsq] at hleN
      simp only [hlt, htest, hle, decide_true, decide_false, Bool.and_true, Bool.and_false,
        ite_true, ite_false, Bool.false_eq_true]
      rw [hmid]
      exact ⟨by omega, by omega, hleN, hlow, by omega⟩
  · have heq : lo.toNat = hi.toNat := by
      rw [UInt64.lt_iff_toNat_lt] at hlt; omega
    simp only [hlt, decide_false, Bool.false_and, ite_false, Bool.false_eq_true]
    exact ⟨hlh, hhi, hup, hlow, by omega⟩

/-- `ceilSqrt` is the exact ceiling square root up to `2^32`. -/
theorem ceilSqrt_correct (n : UInt64) (hn : n.toNat ≤ 4294967296) :
    (ceilSqrt n).toNat ≤ 65536 ∧
    n.toNat ≤ (ceilSqrt n).toNat * (ceilSqrt n).toNat ∧
    ∀ j, j < (ceilSqrt n).toNat → j * j < n.toNat := by
  have h := loop_induction (n := 17) (init := ((0 : UInt64), (65536 : UInt64)))
    (f := sqrtStep n) (Bracket n) ⟨by decide, by decide, by simpa using hn,
      fun j hj => by simp at hj, by decide⟩
    fun k s hk hs => bracket_step n k hk _ s hs
  obtain ⟨hlh, hhi, hup, hlow, hwidth⟩ := h
  rw [ceilSqrt_loop]
  have heq : (LeanExe.loop 17 ((0 : UInt64), (65536 : UInt64)) (sqrtStep n)).1.toNat =
      (LeanExe.loop 17 ((0 : UInt64), (65536 : UInt64)) (sqrtStep n)).2.toNat := by
    simp at hwidth; omega
  exact ⟨by omega, by rw [heq]; exact hup, hlow⟩

end Sqrt

end Project.Drone
