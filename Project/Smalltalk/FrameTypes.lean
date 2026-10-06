import Project.Smalltalk.PointerTypes
import Project.Smalltalk.FrameHeap

namespace Project.Smalltalk.FrameTypes
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.PointerTypes

theorem activation_pc {s : Array UInt64} {h k : UInt64} {cap : Nat}
    (tag : field s h 0 = 5) : Required (field s h 0) 3 k → Matches s cap k dead := by
  intro required
  rw [tag] at required
  simp [Required] at required

theorem retire_typed {s : Array UInt64} {cap : Nat} {act : UInt64}
    (shape : Shape s cap) (typed : PointerTypes.Valid s cap)
    (handle : Handle cap act) (tag : field s act 0 = 5) : PointerTypes.Valid (retire s act) cap := by
  have pc := PointerTypes.write_cell_valid shape typed handle (show (3 : UInt64).toNat < 8 by decide)
    (show (3 : UInt64) ≠ 0 by decide) (fun _ => activation_pc tag)
  have pcShape := write_shape shape (cell_index_not_register shape.2.1 handle
    (show (3 : UInt64).toNat < 8 by decide) (show (14 : UInt64).toNat < 24 by decide)) (v := dead)
  have caller := PointerTypes.write_cell_valid pcShape pc handle (show (4 : UInt64).toNat < 8 by decide)
    (show (4 : UInt64) ≠ 0 by decide) (fun _ _ => Or.inl rfl) (v := 0)
  have callerShape := write_shape pcShape (cell_index_not_register pcShape.2.1 handle
    (show (4 : UInt64).toNat < 8 by decide) (show (14 : UInt64).toNat < 24 by decide)) (v := 0)
  exact PointerTypes.write_cell_valid callerShape caller handle (show (7 : UInt64).toNat < 8 by decide)
    (show (7 : UInt64) ≠ 0 by decide) (fun _ _ => Or.inl rfl) (v := 0)

theorem retire_tag {s : Array UInt64} {cap : Nat} {act h : UInt64}
    (shape : Shape s cap) (handle : Handle cap act) (other : Handle cap h) :
    field (retire s act) h 0 = field s h 0 := by
  rw [Frame.retire_field shape handle other (show (0 : UInt64).toNat < 8 by decide)]
  simp

theorem retire_matches {s : Array UInt64} {cap : Nat} {act h tag : UInt64}
    (shape : Shape s cap) (handle : Handle cap act) (matching : Matches s cap tag h) :
    Matches (retire s act) cap tag h := by
  rcases matching with zero | cell
  · exact Or.inl zero
  · exact Or.inr ⟨cell.1, (retire_tag shape handle cell.1).trans cell.2⟩

theorem retire_value {s : Array UInt64} {cap : Nat} {act h : UInt64}
    (shape : Shape s cap) (handle : Handle cap act) (value : HeapWrite.Value s cap h) :
    HeapWrite.Value (retire s act) cap h := by
  rcases value with zero | cell
  · exact Or.inl zero
  · exact Or.inr ⟨cell.1, by rw [retire_tag shape handle cell.1]; exact cell.2⟩

end Project.Smalltalk.FrameTypes
