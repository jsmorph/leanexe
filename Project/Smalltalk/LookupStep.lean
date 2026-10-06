import Project.Smalltalk.ProgramBounds
import Project.Smalltalk.Loops

namespace Project.Smalltalk.LookupStep
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory

abbrev State := UInt64 × UInt64 × UInt64

def found (p : Array UInt64) (selector owner index : UInt64) : Bool :=
  owner != 0 && index < read p 1 && methodAt p (index + 1) 0 == owner && methodAt p (index + 1) 1 == selector

def next (p : Array UInt64) (selector : UInt64) (st : State) : State :=
  let count := read p 1
  let c := st.1
  let i := st.2.1
  let result := st.2.2
  (if result != 0 || c == 0 then c else if i == count then classAt p c 0 else c,
    if i == count then 0 else i + 1,
    if result != 0 then result else if found p selector c i then i + 1 else 0)

theorem lookup_eq (p : Array UInt64) (owner selector : UInt64) :
    lookup p owner selector = (Loops.applyN (next p selector) (read p 0 * (read p 1 + 1)).toNat (owner, 0, 0)).2.2 := by
  rw [← Loops.loop_constant]
  rfl

def Range (p : Array UInt64) (st : State) : Prop :=
  st.2.2 = 0 ∨ (1 ≤ st.2.2.toNat ∧ st.2.2.toNat ≤ (read p 1).toNat)

theorem found_index {p : Array UInt64} {selector owner index : UInt64}
    (selected : found p selector owner index = true) : index < read p 1 := by
  have all : owner ≠ 0 ∧ index < read p 1 ∧ methodAt p (index + 1) 0 = owner ∧ methodAt p (index + 1) 1 = selector := by
    simpa only [found, Bool.and_assoc, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, beq_iff_eq] using selected
  exact all.2.1

theorem next_range {p : Array UInt64} {selector : UInt64} {st : State}
    (bound : (read p 1).toNat ≤ 1048576) (range : Range p st) : Range p (next p selector st) := by
  by_cases existing : st.2.2 ≠ 0
  · have retained : (next p selector st).2.2 = st.2.2 := by
      simp only [next, show (st.2.2 != 0) = true from bne_iff_ne.mpr existing, ite_true]
    change (next p selector st).2.2 = 0 ∨ _
    rw [retained]
    exact range
  · have zero : st.2.2 = 0 := Classical.not_not.mp existing
    by_cases selected : found p selector st.1 st.2.1 = true
    · have small := UInt64.lt_iff_toNat_lt.mp (found_index selected)
      have increment := successor_toNat (i := st.2.1) (by omega)
      have value : (next p selector st).2.2 = st.2.1 + 1 := by
        simp only [next, zero, bne_self_eq_false, Bool.false_eq_true, ite_false, selected, ite_true]
      change (next p selector st).2.2 = 0 ∨ _
      rw [value]
      exact Or.inr ⟨by rw [increment]; omega, by rw [increment]; omega⟩
    · have value : (next p selector st).2.2 = 0 := by
        simp only [next, zero, bne_self_eq_false, Bool.false_eq_true, ite_false, selected]
      exact Or.inl value

theorem lookup_range {p : Array UInt64} (bound : (read p 1).toNat ≤ 1048576) (owner selector : UInt64) :
    lookup p owner selector = 0 ∨ (1 ≤ (lookup p owner selector).toNat ∧ (lookup p owner selector).toNat ≤ (read p 1).toNat) := by
  rw [lookup_eq]
  exact Loops.applyN_invariant (Range p) (next p selector) (fun _ => next_range bound) _ _ (Or.inl rfl)

end Project.Smalltalk.LookupStep
