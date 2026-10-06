import Project.Smalltalk.TypedAllocation
import Project.Smalltalk.StackPush

namespace Project.Smalltalk.Construction
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.AllocationEffect

def prepend (s : Array UInt64) (value : UInt64) : Array UInt64 :=
  let t := allocate s 7 value (read s 19) 0 0 0 0
  write t 19 (read t 10)

structure Effect (s t : Array UInt64) (cap : Nat) (value : UInt64) : Prop where
  heap : Heap.Valid t cap
  typed : PointerTypes.Valid t cap
  head : Handle cap (read t 19)
  tag : field t (read t 19) 0 = 7
  value : field t (read t 19) 2 = value
  next : field t (read t 19) 3 = read s 19
  previous : ∀ h, Handle cap h → field s h 0 ≠ 0 → ∀ k : UInt64, k.toNat < 8 → field t h k = field s h k
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 13 → r ≠ 17 → r ≠ 19 →
    read t r = read s r
  count : (read t 9).toNat + 1 = (read s 9).toNat

theorem prepend_effect {s : Array UInt64} {cap : Nat} {value : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (tail : Matches s cap 7 (read s 19)) (valueValid : HeapWrite.Value s cap value)
    (enough : (1 : UInt64) ≤ read s 9) : Effect s (prepend s value) cap value := by
  rcases valid.2 with ⟨nodes, free⟩
  rcases free_nonempty free enough with ⟨h, rest, eq⟩
  subst nodes
  let t := allocate s 7 value (read s 19) 0 0 0 0
  have refs := StackPush.link_references valueValid (matches_value tail (by decide))
  have allocation : AllocationEffect.Effect s t cap 7 value (read s 19) 0 0 0 0 :=
    allocate_effect valid.1 free 7 value (read s 19) 0 0 0 0 (by simp [ValidTag]) refs
  have cellTypes : PointerTypes.Valid t cap := TypedAllocation.allocate_typed valid.1 typed free
    7 value (read s 19) 0 0 0 0 (by simp [ValidTag]) refs (TypedAllocation.link_references tail)
  have remaining := (FreeList.allocate_valid valid.1.1 free 7 value (read s 19) 0 0 0 0 (by decide)).2
  have headRead : read (write t 19 (read t 10)) 19 = read s 8 := by
    rw [read_write_same _ _ _ (register_bound allocation.heap.1.1 (show (19 : UInt64).toNat < 24 by decide)), allocation.last]
  have words := fun (k : UInt64) (bound : k.toNat < 8) =>
    show field (write t 19 (read t 10)) (read s 8) k = Allocation.allocatedWord 7 value (read s 19) 0 0 0 0 k from by
      rw [field_write_register allocation.heap.1.1 allocation.handle bound (show (19 : UInt64).toNat < 24 by decide), allocation.words k bound]
  change Effect s (write t 19 (read t 10)) cap value
  refine ⟨HeapWrite.write_register_valid allocation.heap (show (19 : UInt64).toNat < 24 by decide)
      (by decide) (by decide) (by decide) (by intro root; simp at root),
    PointerTypes.write_register_valid allocation.heap.1.1 cellTypes (show (19 : UInt64).toNat < 24 by decide),
    headRead ▸ allocation.handle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [headRead, words 0 (by decide)]; rfl
  · rw [headRead, words 2 (by decide)]; rfl
  · rw [headRead, words 3 (by decide)]; rfl
  · intro g handle allocated k bound
    rw [field_write_register allocation.heap.1.1 handle bound (show (19 : UInt64).toNat < 24 by decide)]
    exact allocation.previous g handle allocated k bound
  · intro r bound h8 h9 h10 h13 h17 h19
    rw [read_write_other _ _ _ _ (Ne.symm h19)]
    exact allocation.registers r bound h8 h9 h10 h13 h17
  · rw [read_write_other _ _ _ _ (show (19 : UInt64) ≠ 9 by decide), remaining.2.1, free.2.1]
    rfl

theorem fillOne_eq_prepend (s : Array UInt64) : fillOne s = prepend s 1 := rfl

theorem fillOne_effect {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (typed : PointerTypes.Valid s cap) (tail : Matches s cap 7 (read s 19))
    (enough : (1 : UInt64) ≤ read s 9) : Effect s (fillOne s) cap 1 := by
  have canonical : HeapWrite.Value s cap 1 := Or.inr (valid.1.2.1 1 ⟨by decide, by simp [Root]⟩)
  rw [fillOne_eq_prepend]
  exact prepend_effect valid typed tail canonical enough

end Project.Smalltalk.Construction
