import Project.Smalltalk.FrameTypes
import Project.Smalltalk.Loops

namespace Project.Smalltalk.UnwindHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.PointerTypes Project.Smalltalk.FrameTypes

structure Holds (original : Array UInt64) (cap : Nat) (caller value : UInt64)
    (st : UInt64 × Array UInt64) : Prop where
  heap : Heap.Valid st.2 cap
  typed : PointerTypes.Valid st.2 cap
  cursor : Matches st.2 cap 5 st.1
  caller : Matches st.2 cap 5 caller
  value : HeapWrite.Value st.2 cap value
  registers : ∀ r : UInt64, r.toNat < 24 → read st.2 r = read original r

theorem next_holds {original s : Array UInt64} {cap : Nat} {cursor caller value : UInt64}
    (holds : Holds original cap caller value (cursor, s)) (stop : UInt64) (nonzero : cursor ≠ 0) :
    Holds original cap caller value (unwindNext s stop cursor) := by
  have cell : Handle cap cursor ∧ field s cursor 0 = 5 := holds.cursor.resolve_left nonzero
  have allocated : field s cursor 0 ≠ 0 := by rw [cell.2]; decide
  have next : Matches s cap 5 (field s cursor 4) :=
    holds.typed cursor cell.1 allocated 4 (by decide) 5 (by rw [cell.2]; simp [Required])
  have newCursor : Matches (retire s cursor) cap 5 (if cursor == stop then 0 else field s cursor 4) := by
    split
    · exact Or.inl rfl
    · exact retire_matches holds.heap.1.1 cell.1 next
  refine ⟨FrameHeap.retire_valid holds.heap cell.1 cell.2,
    retire_typed holds.heap.1.1 holds.typed cell.1 cell.2,
    newCursor, retire_matches holds.heap.1.1 cell.1 holds.caller,
    retire_value holds.heap.1.1 cell.1 holds.value, ?_⟩
  intro r bound
  exact (Frame.retire_register holds.heap.1.1 cell.1 bound).trans (holds.registers r bound)

theorem unwind_preserves {s : Array UInt64} {cap : Nat} {current caller value : UInt64}
    (heap : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (currentCell : Matches s cap 5 current) (callerCell : Matches s cap 5 caller)
    (valueValid : HeapWrite.Value s cap value) (stop fuel : UInt64) :
    Holds s cap caller value
      (LeanExe.repeatWhile fuel (current, s) (fun (cursor, _) => cursor != (0 : UInt64))
        (fun (cursor, s) => unwindNext s stop cursor)) := by
  apply Loops.repeat_invariant (Holds s cap caller value)
  · intro st holds active
    rcases st with ⟨cursor, t⟩
    have nonzero : cursor ≠ 0 := bne_iff_ne.mp active
    exact next_holds holds stop nonzero
  · exact ⟨heap, typed, currentCell, callerCell, valueValid, fun _ _ => rfl⟩

end Project.Smalltalk.UnwindHeap
