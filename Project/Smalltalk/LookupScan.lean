import Project.Smalltalk.LookupSpec

namespace Project.Smalltalk.LookupScan
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.LookupStep Project.Smalltalk.LookupSpec

theorem next_existing (p : Array UInt64) (selector : UInt64) (st : State) (existing : st.2.2 ≠ 0) :
    (next p selector st).2.2 = st.2.2 := by
  simp only [next, show (st.2.2 != 0) = true from bne_iff_ne.mpr existing, ite_true]

theorem iterations_existing (p : Array UInt64) (selector : UInt64) (st : State)
    (existing : st.2.2 ≠ 0) (fuel : Nat) : (Loops.applyN (next p selector) fuel st).2.2 = st.2.2 := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
    rw [Loops.applyN, ih _ (by rw [next_existing p selector st existing]; exact existing), next_existing p selector st existing]

theorem next_zero {p : Array UInt64} {selector : UInt64} {st : State}
    (owner : st.1 = 0) (result : st.2.2 = 0) : (next p selector st).1 = 0 ∧ (next p selector st).2.2 = 0 := by
  simp only [next, found, owner, result, BEq.rfl, Bool.or_true, ite_true,
    bne_self_eq_false, Bool.false_eq_true, ite_false, Bool.false_and]
  simp

theorem iterations_zero (p : Array UInt64) (selector : UInt64) (index : UInt64) (fuel : Nat) :
    (Loops.applyN (next p selector) fuel (0, index, 0)).2.2 = 0 :=
  (Loops.applyN_invariant (fun st : State => st.1 = 0 ∧ st.2.2 = 0) (next p selector)
    (fun _ both => next_zero both.1 both.2) fuel (0, index, 0) ⟨rfl, rfl⟩).2

theorem found_candidate {p : Array UInt64} {owner selector index : UInt64} (within : index < read p 1) :
    found p selector owner index = candidate p owner selector (index.toNat + 1) := by
  have converted : (index.toNat + 1).toUInt64 = index + 1 := by
    change UInt64.ofNat (index.toNat + 1) = index + 1
    rw [UInt64.ofNat_add, UInt64.ofNat_toNat]
    rfl
  simp only [found, candidate, converted, within, decide_true, Bool.and_true]

theorem next_scanning {p : Array UInt64} {owner selector index : UInt64} (within : index < read p 1) :
    next p selector (owner, index, 0) =
      (owner, index + 1, if candidate p owner selector (index.toNat + 1) then index + 1 else 0) := by
  have different : index ≠ read p 1 := by intro same; rw [same] at within; exact UInt64.lt_irrefl _ within
  simp only [next, bne_self_eq_false, Bool.false_eq_true, ite_false, Bool.false_or,
    show (index == read p 1) = false from beq_eq_false_iff_ne.mpr different, ite_self, found_candidate within]

theorem next_end (p : Array UInt64) (selector owner result : UInt64) :
    next p selector (owner, read p 1, result) =
      (if result != 0 || owner == 0 then owner else classAt p owner 0, 0, result) := by
  simp only [next, found, BEq.rfl, ite_true, UInt64.lt_irrefl, decide_false, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases zero : result = 0
  · simp [zero]
  · simp only [show (result != 0) = true from bne_iff_ne.mpr zero, ite_true]

end Project.Smalltalk.LookupScan
