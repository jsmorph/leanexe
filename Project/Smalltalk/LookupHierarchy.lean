import Project.Smalltalk.LookupCorrect

namespace Project.Smalltalk.LookupHierarchy
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime
open Project.Smalltalk.LookupSpec

def ancestor (p : Array UInt64) (owner : UInt64) : Nat → UInt64
  | 0 => owner
  | fuel + 1 => if owner == 0 then 0 else ancestor p (classAt p owner 0) fuel

theorem ancestor_zero {p : Array UInt64} (valid : programValid p = true) (owner : UInt64)
    (within : owner.toNat ≤ (read p 0).toNat) (fuel : Nat) (enough : owner.toNat ≤ fuel) :
    ancestor p owner fuel = 0 := by
  induction fuel generalizing owner with
  | zero =>
    have zero : owner = 0 := UInt64.toNat_inj.mp (show owner.toNat = (0 : UInt64).toNat by change owner.toNat = 0; omega)
    exact zero
  | succ fuel ih =>
    by_cases zero : owner = 0
    · simp only [ancestor, zero, BEq.rfl, ite_true]
    · have positive : 0 < owner.toNat := by
        have nonzero : owner.toNat ≠ 0 := by intro eq; exact zero (UInt64.toNat_inj.mp eq)
        omega
      have parent := (ProgramBounds.class_bounds valid positive within).parent
      simp only [ancestor, show (owner == 0) = false from beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ite_false]
      exact ih _ (by omega) (by omega)

theorem search_after_end (p : Array UInt64) (owner selector : UInt64) (fuel extra : Nat)
    (ended : ancestor p owner fuel = 0) : search p owner selector (fuel + extra) = search p owner selector fuel := by
  induction fuel generalizing owner with
  | zero =>
    change owner = 0 at ended
    rw [ended, search_zero, search_zero]
  | succ fuel ih =>
    by_cases zero : owner = 0
    · rw [zero, search_zero, search_zero]
    · have ownerTest : (owner == 0) = false := beq_eq_false_iff_ne.mpr zero
      simp only [ancestor, ownerTest, Bool.false_eq_true, ite_false] at ended
      rw [Nat.succ_add]
      simp only [search, ownerTest, Bool.false_eq_true, ite_false]
      by_cases selected : own p owner selector 0 (read p 1).toNat ≠ 0
      · simp only [show (own p owner selector 0 (read p 1).toNat != 0) = true from bne_iff_ne.mpr selected, ite_true]
      · simp only [show own p owner selector 0 (read p 1).toNat = 0 from Classical.not_not.mp selected,
          bne_self_eq_false, Bool.false_eq_true, ite_false]
        exact ih _ ended

theorem class_budget_sufficient {p : Array UInt64} (valid : programValid p = true) (owner selector : UInt64)
    (within : owner.toNat ≤ (read p 0).toNat) (extra : Nat) :
    search p owner selector ((read p 0).toNat + extra) = search p owner selector (read p 0).toNat :=
  search_after_end p owner selector _ extra (ancestor_zero valid owner within _ within)

end Project.Smalltalk.LookupHierarchy
