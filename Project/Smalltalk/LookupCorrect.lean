import Project.Smalltalk.LookupRound

namespace Project.Smalltalk.LookupCorrect
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.LookupStep Project.Smalltalk.LookupSpec

theorem rounds {p : Array UInt64} (bound : (read p 1).toNat ≤ 1048576) (owner selector : UInt64) (fuel : Nat) :
    (Loops.applyN (next p selector) (fuel * ((read p 1).toNat + 1)) (owner, 0, 0)).2.2 = search p owner selector fuel := by
  induction fuel generalizing owner with
  | zero => simp only [Nat.zero_mul, Loops.applyN, search]
  | succ fuel ih =>
    rw [Nat.succ_mul, Nat.add_comm (fuel * ((read p 1).toNat + 1)) ((read p 1).toNat + 1),
      Loops.applyN_add, LookupRound.round bound]
    by_cases zero : owner = 0
    · rw [zero, own_zero]
      simp only [bne_self_eq_false, BEq.rfl, Bool.or_true, ite_true]
      rw [search_zero]
      exact LookupScan.iterations_zero p selector 0 _
    · have ownerTest : (owner == 0) = false := beq_eq_false_iff_ne.mpr zero
      by_cases selected : own p owner selector 0 (read p 1).toNat ≠ 0
      · have selectedTest : (own p owner selector 0 (read p 1).toNat != 0) = true := bne_iff_ne.mpr selected
        simp only [selectedTest, Bool.true_or, ite_true]
        rw [LookupScan.iterations_existing p selector _ selected]
        simp only [search, ownerTest, Bool.false_eq_true, ite_false, selectedTest, ite_true]
      · have absent : own p owner selector 0 (read p 1).toNat = 0 := Classical.not_not.mp selected
        simp only [absent, bne_self_eq_false, ownerTest, Bool.false_or, Bool.false_eq_true, ite_false]
        rw [ih]
        simp only [search, ownerTest, Bool.false_eq_true, ite_false, absent, bne_self_eq_false]

theorem budget_toNat {p : Array UInt64} (classes : (read p 0).toNat ≤ 1048576)
    (methods : (read p 1).toNat ≤ 1048576) :
    (read p 0 * (read p 1 + 1)).toNat = (read p 0).toNat * ((read p 1).toNat + 1) := by
  have increment : (read p 1 + 1).toNat = (read p 1).toNat + 1 := by
    rw [UInt64.toNat_add]
    simp only [UInt64.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  have product : (read p 0).toNat * ((read p 1).toNat + 1) ≤ 1048576 * 1048577 :=
    Nat.mul_le_mul classes (by omega)
  rw [UInt64.toNat_mul, increment, Nat.mod_eq_of_lt (by omega)]

/-- The actual flat loop implements method-ID order followed by parent order,
with the class-visit limit stored in the program header. -/
theorem lookup_correct {p : Array UInt64} (classes : (read p 0).toNat ≤ 1048576)
    (methods : (read p 1).toNat ≤ 1048576) (owner selector : UInt64) :
    lookup p owner selector = search p owner selector (read p 0).toNat := by
  rw [LookupStep.lookup_eq, budget_toNat classes methods]
  exact rounds methods owner selector _

theorem validated_lookup {p : Array UInt64} (valid : programValid p = true) (owner selector : UInt64) :
    lookup p owner selector = search p owner selector (read p 0).toNat :=
  lookup_correct (ProgramBounds.header valid).classesBound (ProgramBounds.header valid).methodsBound owner selector

end Project.Smalltalk.LookupCorrect
