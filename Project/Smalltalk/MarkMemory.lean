import Project.Smalltalk.Memory

namespace Project.Smalltalk.MarkMemory
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory

theorem markReady_read {s : Array UInt64} {cap : Nat} {h : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (room : (read s 18).toNat < cap) (j : UInt64) :
    read (markReady s h) j =
      if j = 18 then read s 18 + 1 else
      if j = 24 + 8 * read s 14 + read s 18 then h else
      if j = address h + 1 then 1 else read s j := by
  have cell := cell_index_bound hs hh (show (1 : UInt64).toNat < 8 by decide)
  have work := work_index_bound hs room
  have reg := register_bound hs (show (18 : UInt64).toNat < 24 by decide)
  simp only [markReady, read_write, write_size, cell, work, reg]

@[simp] theorem markReady_size (s : Array UInt64) (h : UInt64) : (markReady s h).size = s.size := by
  simp only [markReady, write_size]

theorem markReady_register {s : Array UInt64} {cap : Nat} {h r : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (room : (read s 18).toNat < cap)
    (hr : r.toNat < 24) :
    read (markReady s h) r = if r = 18 then read s 18 + 1 else read s r := by
  rw [markReady_read hs hh room]
  simp only [Ne.symm (work_index_not_register (n := read s 18) hs (by omega) hr),
    Ne.symm (cell_index_not_register hs.2.1 hh (show (1 : UInt64).toNat < 8 by decide) hr), ite_false]

theorem markReady_shape {s : Array UInt64} {cap : Nat} {h : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (room : (read s 18).toNat < cap) :
    Shape (markReady s h) cap := by
  refine ⟨hs.1, hs.2.1, by simpa using hs.2.2.1, ?_⟩
  rw [markReady_register hs hh room (show (14 : UInt64).toNat < 24 by decide)]
  simpa using hs.2.2.2

theorem markReady_field {s : Array UInt64} {cap : Nat} {h g k : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (room : (read s 18).toNat < cap)
    (hg : Handle cap g) (hk : k.toNat < 8) :
    field (markReady s h) g k = if g = h ∧ k = 1 then 1 else field s g k := by
  rw [field, markReady_read hs hh room]
  simp only [cell_index_not_register hs.2.1 hg hk (show (18 : UInt64).toNat < 24 by decide),
    Ne.symm (work_index_not_cell (n := read s 18) hs (by omega) hg hk), ite_false,
    cell_index_eq_iff hs.2.1 hg hh hk (show (1 : UInt64).toNat < 8 by decide), field]

theorem markReady_preserves_payload {s : Array UInt64} {cap : Nat} {h g k : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (room : (read s 18).toNat < cap)
    (hg : Handle cap g) (hk : k.toNat < 8) (payload : k ≠ 1) :
    field (markReady s h) g k = field s g k := by
  rw [markReady_field hs hh room hg hk]
  simp only [payload, and_false, ite_false]

theorem markReady_work {s : Array UInt64} {cap : Nat} {h m : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (room : (read s 18).toNat < cap) (hm : m.toNat < cap) :
    read (markReady s h) (24 + 8 * read s 14 + m) =
      if m = read s 18 then h else read s (24 + 8 * read s 14 + m) := by
  rw [markReady_read hs hh room]
  simp only [work_index_not_register (n := m) hs (by omega) (show (18 : UInt64).toNat < 24 by decide),
    work_index_not_cell (n := m) hs (by omega) hh (show (1 : UInt64).toNat < 8 by decide), ite_false,
    work_index_eq_iff (n := m) (m := read s 18) hs (by omega) (by omega)]

theorem mark_zero (s : Array UInt64) : mark s 0 = s := rfl

theorem mark_new {s : Array UInt64} {cap : Nat} {h : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (room : (read s 18).toNat < cap)
    (allocated : field s h 0 ≠ 0) (unmarked : field s h 1 = 0) : mark s h = markReady s h := by
  have nonzero : h ≠ 0 := by
    intro zero
    have positive := hh.1
    rw [zero] at positive
    exact (by decide : ¬ 1 ≤ (0 : UInt64).toNat) positive
  have space : ¬ read s 18 ≥ read s 14 := by
    simp only [UInt64.le_iff_toNat_le, hs.2.2.2]
    omega
  simp only [mark, kind_eq_field hs hh, beq_iff_eq, bne_iff_ne, nonzero,
    allocated, unmarked, ne_eq, not_true, space, ite_false]

theorem mark_old {s : Array UInt64} {cap : Nat} {h : UInt64}
    (hs : Shape s cap) (hh : Handle cap h) (allocated : field s h 0 ≠ 0)
    (marked : field s h 1 ≠ 0) : mark s h = s := by
  have nonzero : h ≠ 0 := by
    intro zero
    have positive := hh.1
    rw [zero] at positive
    exact (by decide : ¬ 1 ≤ (0 : UInt64).toNat) positive
  simp only [mark, kind_eq_field hs hh, beq_iff_eq, bne_iff_ne, nonzero, allocated,
    ite_false]
  exact ite_eq_left marked

end Project.Smalltalk.MarkMemory
