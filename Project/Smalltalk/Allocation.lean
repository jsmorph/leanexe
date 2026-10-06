import Project.Smalltalk.Memory

namespace Project.Smalltalk.Allocation
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory

/-- The complete word-level effect of the concrete allocator. All quantities
on the right are read from the original array. -/
theorem allocateCell_read {s : Array UInt64} {cap : Nat}
    (hs : Shape s cap) (hh : Handle cap (read s 8))
    (tag a b c d e f j : UInt64) :
    read (allocateCell s tag a b c d e f) j =
      if j = 17 then read s 17 + 1 else
      if j = 13 then max (read s 13) (read s 14 - (read s 9 - 1)) else
      if j = 10 then read s 8 else
      if j = 9 then read s 9 - 1 else
      if j = 8 then field s (read s 8) 2 else
      if j = address (read s 8) + 7 then f else
      if j = address (read s 8) + 6 then e else
      if j = address (read s 8) + 5 then d else
      if j = address (read s 8) + 4 then c else
      if j = address (read s 8) + 3 then b else
      if j = address (read s 8) + 2 then a else
      if j = address (read s 8) + 1 then 0 else
      if j = address (read s 8) then tag else read s j := by
  have h0 := cell_index_bound hs hh (show (0 : UInt64).toNat < 8 by decide)
  have h1 := cell_index_bound hs hh (show (1 : UInt64).toNat < 8 by decide)
  have h2 := cell_index_bound hs hh (show (2 : UInt64).toNat < 8 by decide)
  have h3 := cell_index_bound hs hh (show (3 : UInt64).toNat < 8 by decide)
  have h4 := cell_index_bound hs hh (show (4 : UInt64).toNat < 8 by decide)
  have h5 := cell_index_bound hs hh (show (5 : UInt64).toNat < 8 by decide)
  have h6 := cell_index_bound hs hh (show (6 : UInt64).toNat < 8 by decide)
  have h7 := cell_index_bound hs hh (show (7 : UInt64).toNat < 8 by decide)
  have r8 := register_bound hs (show (8 : UInt64).toNat < 24 by decide)
  have r9 := register_bound hs (show (9 : UInt64).toNat < 24 by decide)
  have r10 := register_bound hs (show (10 : UInt64).toNat < 24 by decide)
  have r13 := register_bound hs (show (13 : UInt64).toNat < 24 by decide)
  have r17 := register_bound hs (show (17 : UInt64).toNat < 24 by decide)
  simp only [UInt64.add_zero] at h0
  simp only [allocateCell, read_write, write_size, h0, h1, h2, h3, h4, h5, h6, h7,
    r8, r9, r10, r13, r17]

@[simp] theorem allocateCell_size (s : Array UInt64) (tag a b c d e f : UInt64) :
    (allocateCell s tag a b c d e f).size = s.size := by
  simp only [allocateCell, write_size]

def allocatedWord (tag a b c d e f k : UInt64) : UInt64 :=
  if k = 0 then tag else if k = 1 then 0 else if k = 2 then a else
  if k = 3 then b else if k = 4 then c else if k = 5 then d else
  if k = 6 then e else f

theorem allocateCell_field {s : Array UInt64} {cap : Nat}
    (hs : Shape s cap) (hh : Handle cap (read s 8))
    {g k : UInt64} (hg : Handle cap g) (hk : k.toNat < 8)
    (tag a b c d e f : UInt64) :
    field (allocateCell s tag a b c d e f) g k =
      if g = read s 8 then allocatedWord tag a b c d e f k else field s g k := by
  have nr : ∀ r : UInt64, r.toNat < 24 → address g + k ≠ r :=
    fun _ hr => cell_index_not_register hs.2.1 hg hk hr
  have eq : ∀ j : UInt64, j.toNat < 8 →
      (address g + k = address (read s 8) + j ↔ g = read s 8 ∧ k = j) :=
    fun _ hj => cell_index_eq_iff hs.2.1 hg hh hk hj
  have zero : (address g + k = address (read s 8)) ↔ g = read s 8 ∧ k = 0 := by
    simpa only [UInt64.add_zero] using eq 0 (by decide)
  rw [field, allocateCell_read hs hh]
  simp only [nr 17 (by decide), nr 13 (by decide), nr 10 (by decide),
    nr 9 (by decide), nr 8 (by decide), ite_false,
    eq 7 (by decide), eq 6 (by decide), eq 5 (by decide), eq 4 (by decide),
    eq 3 (by decide), eq 2 (by decide), eq 1 (by decide), zero]
  by_cases same : g = read s 8
  · simp only [same, true_and, ite_true, allocatedWord]
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
      have ns : k.toNat = 0 ∨ k.toNat = 1 ∨ k.toNat = 2 ∨ k.toNat = 3 ∨
          k.toNat = 4 ∨ k.toNat = 5 ∨ k.toNat = 6 ∨ k.toNat = 7 := by omega
      simpa only [← UInt64.toNat_inj, UInt64.reduceToNat] using ns
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [same, false_and, ite_false, field]

theorem allocateCell_preserves_other {s : Array UInt64} {cap : Nat}
    (hs : Shape s cap) (hh : Handle cap (read s 8))
    {g k : UInt64} (hg : Handle cap g) (hk : k.toNat < 8) (fresh : g ≠ read s 8)
    (tag a b c d e f : UInt64) :
    field (allocateCell s tag a b c d e f) g k = field s g k := by
  rw [allocateCell_field hs hh hg hk]
  simp only [fresh, ite_false]

theorem allocateCell_register {s : Array UInt64} {cap : Nat}
    (hs : Shape s cap) (hh : Handle cap (read s 8))
    {r : UInt64} (hr : r.toNat < 24) (tag a b c d e f : UInt64) :
    read (allocateCell s tag a b c d e f) r =
      if r = 17 then read s 17 + 1 else
      if r = 13 then max (read s 13) (read s 14 - (read s 9 - 1)) else
      if r = 10 then read s 8 else
      if r = 9 then read s 9 - 1 else
      if r = 8 then field s (read s 8) 2 else read s r := by
  have ne : ∀ k : UInt64, k.toNat < 8 → r ≠ address (read s 8) + k :=
    fun _ hk => Ne.symm (cell_index_not_register hs.2.1 hh hk hr)
  have zero : r ≠ address (read s 8) := by
    simpa only [UInt64.add_zero] using ne 0 (by decide)
  rw [allocateCell_read hs hh]
  simp only [ne 7 (by decide), ne 6 (by decide), ne 5 (by decide), ne 4 (by decide),
    ne 3 (by decide), ne 2 (by decide), ne 1 (by decide), zero, ite_false]

theorem allocateCell_shape {s : Array UInt64} {cap : Nat}
    (hs : Shape s cap) (hh : Handle cap (read s 8)) (tag a b c d e f : UInt64) :
    Shape (allocateCell s tag a b c d e f) cap := by
  refine ⟨hs.1, hs.2.1, by simpa using hs.2.2.1, ?_⟩
  rw [allocateCell_register hs hh (show (14 : UInt64).toNat < 24 by decide)]
  simpa using hs.2.2.2

end Project.Smalltalk.Allocation
