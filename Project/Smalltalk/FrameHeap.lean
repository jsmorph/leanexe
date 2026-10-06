import Project.Smalltalk.HeapWrite
import Project.Smalltalk.Frame

namespace Project.Smalltalk.FrameHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.HeapWrite

theorem value_after_cell {s : Array UInt64} {cap : Nat} {h k v value : UInt64}
    (shape : Shape s cap) (handle : Handle cap h) (offset : k.toNat < 8) (notTag : k ≠ 0)
    (original : Value s cap value) : Value (write s (address h + k) v) cap value := by
  rcases original with zero | allocated
  · exact Or.inl zero
  · exact Or.inr ⟨allocated.1, by rw [cell_tag shape handle offset notTag allocated.1]; exact allocated.2⟩

theorem activation_pc_reference {s : Array UInt64} {act pc : UInt64} {cap : Nat}
    (tag : field s act 0 = 5) : PointerField (field s act 0) 3 → Value s cap pc := by
  intro pointer
  rw [tag] at pointer
  simp [PointerField] at pointer

theorem advance_valid {s : Array UInt64} {cap : Nat} {stack : UInt64}
    (valid : Heap.Valid s cap) (handle : Handle cap (read s 2)) (tag : field s (read s 2) 0 = 5)
    (value : Value s cap stack) : Heap.Valid (advance s stack) cap := by
  have allocated : field s (read s 2) 0 ≠ 0 := by rw [tag]; decide
  have middle := write_cell_valid valid handle allocated (show (3 : UInt64).toNat < 8 by decide)
    (show (3 : UInt64) ≠ 0 by decide) (activation_pc_reference tag (pc := field s (read s 2) 3 + 1))
  have allocatedMiddle : field (write s (address (read s 2) + 3) (field s (read s 2) 3 + 1)) (read s 2) 0 ≠ 0 := by
    rw [cell_tag valid.1.1 handle (show (3 : UInt64).toNat < 8 by decide) (by decide) handle]
    exact allocated
  exact write_cell_valid middle handle allocatedMiddle (show (7 : UInt64).toNat < 8 by decide)
    (by decide) (fun _ => value_after_cell valid.1.1 handle (show (3 : UInt64).toNat < 8 by decide) (by decide) value)

theorem retire_valid {s : Array UInt64} {cap : Nat} {act : UInt64}
    (valid : Heap.Valid s cap) (handle : Handle cap act) (tag : field s act 0 = 5) : Heap.Valid (retire s act) cap := by
  have allocated : field s act 0 ≠ 0 := by rw [tag]; decide
  have pc := write_cell_valid valid handle allocated (show (3 : UInt64).toNat < 8 by decide)
    (show (3 : UInt64) ≠ 0 by decide) (activation_pc_reference tag (pc := dead))
  have pcAllocated : field (write s (address act + 3) dead) act 0 ≠ 0 := by
    rw [cell_tag valid.1.1 handle (show (3 : UInt64).toNat < 8 by decide) (by decide) handle]
    exact allocated
  have caller := write_cell_valid pc handle pcAllocated (show (4 : UInt64).toNat < 8 by decide)
    (show (4 : UInt64) ≠ 0 by decide) (fun _ => Or.inl rfl) (v := 0)
  have callerAllocated : field (write (write s (address act + 3) dead) (address act + 4) 0) act 0 ≠ 0 := by
    rw [cell_tag pc.1.1 handle (show (4 : UInt64).toNat < 8 by decide) (by decide) handle]
    exact pcAllocated
  exact write_cell_valid caller handle callerAllocated (show (7 : UInt64).toNat < 8 by decide)
    (show (7 : UInt64) ≠ 0 by decide) (fun _ => Or.inl rfl) (v := 0)

end Project.Smalltalk.FrameHeap
