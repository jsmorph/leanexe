import Project.Smalltalk.InitializationBase

namespace Project.Smalltalk.SeedMemory
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory

def seededWord (cap h k : UInt64) : UInt64 :=
  if h ≤ 3 then if k = 2 then h - 1 else if k = 0 then 2 else 0
  else if k = 2 then if h < cap then h + 1 else 0 else 0

theorem seedCell_eq (s : Array UInt64) (i : UInt64) :
    seedCell s i =
      if i + 1 ≤ 3 then write (write s (address (i + 1) + 0) 2) (address (i + 1) + 2) (i + 1 - 1)
      else write s (address (i + 1) + 2) (if i + 1 < read s 14 then i + 1 + 1 else 0) := by
  simp only [seedCell, UInt64.add_zero]

@[simp] theorem seedCell_size (s : Array UInt64) (i : UInt64) : (seedCell s i).size = s.size := by
  rw [seedCell_eq]
  split <;> simp only [write_size]

theorem seedCell_register {s : Array UInt64} {cap : Nat} {i r : UInt64}
    (shape : Shape s cap) (index : i.toNat < cap) (bound : r.toNat < 24) :
    read (seedCell s i) r = read s r := by
  have handle := successor_handle shape.2.1 index
  rw [seedCell_eq]
  split
  · rw [read_write_other _ _ _ _ (cell_index_not_register shape.2.1 handle (by decide) bound),
      read_write_other _ _ _ _ (cell_index_not_register shape.2.1 handle (by decide) bound)]
  · exact read_write_other _ _ _ _ (cell_index_not_register shape.2.1 handle (by decide) bound)

theorem seedCell_shape {s : Array UInt64} {cap : Nat} {i : UInt64}
    (shape : Shape s cap) (index : i.toNat < cap) : Shape (seedCell s i) cap := by
  refine ⟨shape.1, shape.2.1, by simpa using shape.2.2.1, ?_⟩
  rw [seedCell_register shape index (show (14 : UInt64).toNat < 24 by decide)]
  exact shape.2.2.2

theorem seedCell_field {s : Array UInt64} {cap : Nat} {i h k : UInt64}
    (shape : Shape s cap) (index : i.toNat < cap) (handle : Handle cap h) (bound : k.toNat < 8) :
    field (seedCell s i) h k =
      if h = i + 1 then
        if h ≤ 3 then if k = 2 then h - 1 else if k = 0 then 2 else field s h k
        else if k = 2 then if h < read s 14 then h + 1 else 0 else field s h k
      else field s h k := by
  have fresh := successor_handle shape.2.1 index
  rw [seedCell_eq]
  by_cases canonical : i + 1 ≤ 3
  · simp only [canonical, ite_true]
    have tagShape := write_shape (v := 2) shape
      (cell_index_not_register shape.2.1 fresh (show (0 : UInt64).toNat < 8 by decide) (by decide))
    rw [field_write_cell tagShape fresh handle (show (2 : UInt64).toNat < 8 by decide) bound,
      field_write_cell shape fresh handle (show (0 : UInt64).toNat < 8 by decide) bound]
    by_cases same : h = i + 1
    · subst h
      simp only [canonical, true_and, ite_true]
    · simp only [same, false_and, ite_false]
  · simp only [canonical, ite_false]
    rw [field_write_cell shape fresh handle (show (2 : UInt64).toNat < 8 by decide) bound]
    by_cases same : h = i + 1
    · subst h
      simp only [canonical, true_and, ite_true, ite_false]
    · simp only [same, false_and, ite_false]

end Project.Smalltalk.SeedMemory
