import Project.Smalltalk.FrameTypes

namespace Project.Smalltalk.AdvanceTypes
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.PointerTypes

theorem advance_typed {s : Array UInt64} {cap : Nat} {stack : UInt64}
    (shape : Shape s cap) (typed : PointerTypes.Valid s cap)
    (handle : Handle cap (read s 2)) (tag : field s (read s 2) 0 = 5)
    (links : Matches s cap 7 stack) : PointerTypes.Valid (advance s stack) cap := by
  let pc := field s (read s 2) 3 + 1
  let t := write s (address (read s 2) + 3) pc
  have updated : PointerTypes.Valid t cap := PointerTypes.write_cell_valid shape typed handle
    (show (3 : UInt64).toNat < 8 by decide) (show (3 : UInt64) ≠ 0 by decide)
    (by intro expected required; rw [tag] at required; simp [Required] at required)
  have middleShape : Shape t cap := write_shape shape (cell_index_not_register shape.2.1 handle
    (show (3 : UInt64).toNat < 8 by decide) (show (14 : UInt64).toNat < 24 by decide))
  have middleTag : field t (read s 2) 0 = 5 :=
    (HeapWrite.cell_tag shape handle (show (3 : UInt64).toNat < 8 by decide) (by decide) handle).trans tag
  have middleLinks : Matches t cap 7 stack := matches_after_cell shape handle (show (3 : UInt64).toNat < 8 by decide) (by decide) links
  exact PointerTypes.write_cell_valid middleShape updated handle (show (7 : UInt64).toNat < 8 by decide)
    (show (7 : UInt64) ≠ 0 by decide) (by
      intro expected required
      rw [middleTag] at required
      have expectedTag : expected = 7 := by simpa [Required] using required
      subst expected
      exact middleLinks)

theorem advance_tag {s : Array UInt64} {cap : Nat} {h stack : UInt64}
    (shape : Shape s cap) (current : Handle cap (read s 2)) (handle : Handle cap h) :
    field (advance s stack) h 0 = field s h 0 := by
  rw [Frame.advance_field shape current handle (show (0 : UInt64).toNat < 8 by decide)]
  simp

theorem advance_matches {s : Array UInt64} {cap : Nat} {h tag stack : UInt64}
    (shape : Shape s cap) (current : Handle cap (read s 2)) (matching : Matches s cap tag h) :
    Matches (advance s stack) cap tag h := by
  rcases matching with zero | cell
  · exact Or.inl zero
  · exact Or.inr ⟨cell.1, (advance_tag shape current cell.1).trans cell.2⟩

theorem advance_value {s : Array UInt64} {cap : Nat} {h stack : UInt64}
    (shape : Shape s cap) (current : Handle cap (read s 2)) (value : HeapWrite.Value s cap h) :
    HeapWrite.Value (advance s stack) cap h := by
  rcases value with zero | cell
  · exact Or.inl zero
  · exact Or.inr ⟨cell.1, by rw [advance_tag shape current cell.1]; exact cell.2⟩

end Project.Smalltalk.AdvanceTypes
