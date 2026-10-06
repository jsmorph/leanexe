import Project.Smalltalk.Memory

namespace Project.Smalltalk.Frame
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory

theorem retire_read {s : Array UInt64} {cap : Nat} {act : UInt64}
    (hs : Shape s cap) (ha : Handle cap act) (j : UInt64) :
    read (retire s act) j =
      if j = address act + 7 then 0 else if j = address act + 4 then 0 else
      if j = address act + 3 then dead else read s j := by
  have h3 := cell_index_bound hs ha (show (3 : UInt64).toNat < 8 by decide)
  have h4 := cell_index_bound hs ha (show (4 : UInt64).toNat < 8 by decide)
  have h7 := cell_index_bound hs ha (show (7 : UInt64).toNat < 8 by decide)
  simp only [retire, read_write, write_size, h3, h4, h7]

@[simp] theorem retire_size (s : Array UInt64) (act : UInt64) : (retire s act).size = s.size := by
  simp only [retire, write_size]

theorem retire_field {s : Array UInt64} {cap : Nat} {act g k : UInt64}
    (hs : Shape s cap) (ha : Handle cap act) (hg : Handle cap g) (hk : k.toNat < 8) :
    field (retire s act) g k =
      if g = act then if k = 7 ∨ k = 4 then 0 else if k = 3 then dead else field s g k
      else field s g k := by
  rw [field, retire_read hs ha]
  simp only [cell_index_eq_iff hs.2.1 hg ha hk (show (7 : UInt64).toNat < 8 by decide),
    cell_index_eq_iff hs.2.1 hg ha hk (show (4 : UInt64).toNat < 8 by decide),
    cell_index_eq_iff hs.2.1 hg ha hk (show (3 : UInt64).toNat < 8 by decide)]
  by_cases same : g = act
  · simp only [same, true_and, ite_true]
    by_cases seven : k = 7
    · simp only [seven, true_or, ite_true]
    · by_cases four : k = 4
      · simp [four]
      · simp only [seven, four, false_or, ite_false, field]
  · simp only [same, false_and, ite_false, field]

theorem retire_register {s : Array UInt64} {cap : Nat} {act r : UInt64}
    (hs : Shape s cap) (ha : Handle cap act) (hr : r.toNat < 24) : read (retire s act) r = read s r := by
  rw [retire_read hs ha]
  simp only [Ne.symm (cell_index_not_register hs.2.1 ha (show (7 : UInt64).toNat < 8 by decide) hr),
    Ne.symm (cell_index_not_register hs.2.1 ha (show (4 : UInt64).toNat < 8 by decide) hr),
    Ne.symm (cell_index_not_register hs.2.1 ha (show (3 : UInt64).toNat < 8 by decide) hr), ite_false]

theorem retire_shape {s : Array UInt64} {cap : Nat} {act : UInt64}
    (hs : Shape s cap) (ha : Handle cap act) : Shape (retire s act) cap := by
  refine ⟨hs.1, hs.2.1, by simpa using hs.2.2.1, ?_⟩
  rw [retire_register hs ha (show (14 : UInt64).toNat < 24 by decide)]
  exact hs.2.2.2

theorem advance_read {s : Array UInt64} {cap : Nat}
    (hs : Shape s cap) (ha : Handle cap (read s 2)) (stack j : UInt64) :
    read (advance s stack) j =
      if j = address (read s 2) + 7 then stack else
      if j = address (read s 2) + 3 then field s (read s 2) 3 + 1 else read s j := by
  have h3 := cell_index_bound hs ha (show (3 : UInt64).toNat < 8 by decide)
  have h7 := cell_index_bound hs ha (show (7 : UInt64).toNat < 8 by decide)
  simp only [advance, read_write, write_size, h3, h7]

theorem advance_field {s : Array UInt64} {cap : Nat} {g k : UInt64}
    (hs : Shape s cap) (ha : Handle cap (read s 2)) (hg : Handle cap g) (hk : k.toNat < 8)
    (stack : UInt64) :
    field (advance s stack) g k =
      if g = read s 2 ∧ k = 7 then stack else
      if g = read s 2 ∧ k = 3 then field s (read s 2) 3 + 1 else field s g k := by
  rw [field, advance_read hs ha]
  simp only [cell_index_eq_iff hs.2.1 hg ha hk (show (7 : UInt64).toNat < 8 by decide),
    cell_index_eq_iff hs.2.1 hg ha hk (show (3 : UInt64).toNat < 8 by decide), field]

theorem advance_register {s : Array UInt64} {cap : Nat} {r : UInt64}
    (hs : Shape s cap) (ha : Handle cap (read s 2)) (hr : r.toNat < 24) (stack : UInt64) :
    read (advance s stack) r = read s r := by
  rw [advance_read hs ha]
  simp only [Ne.symm (cell_index_not_register hs.2.1 ha (show (7 : UInt64).toNat < 8 by decide) hr),
    Ne.symm (cell_index_not_register hs.2.1 ha (show (3 : UInt64).toNat < 8 by decide) hr), ite_false]

@[simp] theorem advance_size (s : Array UInt64) (stack : UInt64) : (advance s stack).size = s.size := by
  simp only [advance, write_size]

theorem advance_shape {s : Array UInt64} {cap : Nat}
    (hs : Shape s cap) (ha : Handle cap (read s 2)) (stack : UInt64) : Shape (advance s stack) cap := by
  refine ⟨hs.1, hs.2.1, by simpa using hs.2.2.1, ?_⟩
  rw [advance_register hs ha (show (14 : UInt64).toNat < 24 by decide)]
  exact hs.2.2.2

end Project.Smalltalk.Frame
