import Project.Smalltalk.FreeList
import Project.Smalltalk.Loops

namespace Project.Smalltalk.Sweep
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.FreeList

theorem reclaim_read {s : Array UInt64} {cap : Nat} {i : UInt64}
    (hs : Shape s cap) (hh : Handle cap (i + 1)) (j : UInt64) :
    read (reclaim s i) j =
      if j = 9 then read s 9 + 1 else if j = 8 then i + 1 else
      if j = address (i + 1) + 7 then 0 else
      if j = address (i + 1) + 6 then 0 else
      if j = address (i + 1) + 5 then 0 else
      if j = address (i + 1) + 4 then 0 else
      if j = address (i + 1) + 3 then 0 else
      if j = address (i + 1) + 2 then read s 8 else
      if j = address (i + 1) then 0 else read s j := by
  have h0 := cell_index_bound hs hh (show (0 : UInt64).toNat < 8 by decide)
  have h2 := cell_index_bound hs hh (show (2 : UInt64).toNat < 8 by decide)
  have h3 := cell_index_bound hs hh (show (3 : UInt64).toNat < 8 by decide)
  have h4 := cell_index_bound hs hh (show (4 : UInt64).toNat < 8 by decide)
  have h5 := cell_index_bound hs hh (show (5 : UInt64).toNat < 8 by decide)
  have h6 := cell_index_bound hs hh (show (6 : UInt64).toNat < 8 by decide)
  have h7 := cell_index_bound hs hh (show (7 : UInt64).toNat < 8 by decide)
  have r8 := register_bound hs (show (8 : UInt64).toNat < 24 by decide)
  have r9 := register_bound hs (show (9 : UInt64).toNat < 24 by decide)
  simp only [UInt64.add_zero] at h0
  simp only [reclaim, read_write, write_size, h0, h2, h3, h4, h5, h6, h7, r8, r9]

@[simp] theorem reclaim_size (s : Array UInt64) (i : UInt64) : (reclaim s i).size = s.size := by
  simp only [reclaim, write_size]

theorem reclaim_register {s : Array UInt64} {cap : Nat} {i r : UInt64}
    (hs : Shape s cap) (hh : Handle cap (i + 1)) (hr : r.toNat < 24) :
    read (reclaim s i) r = if r = 9 then read s 9 + 1 else if r = 8 then i + 1 else read s r := by
  have ne : ∀ k : UInt64, k.toNat < 8 → r ≠ address (i + 1) + k :=
    fun _ hk => Ne.symm (cell_index_not_register hs.2.1 hh hk hr)
  have zero : r ≠ address (i + 1) := by simpa only [UInt64.add_zero] using ne 0 (by decide)
  rw [reclaim_read hs hh]
  simp only [ne 7 (by decide), ne 6 (by decide), ne 5 (by decide), ne 4 (by decide),
    ne 3 (by decide), ne 2 (by decide), zero, ite_false]

theorem reclaim_field {s : Array UInt64} {cap : Nat} {i g k : UInt64}
    (hs : Shape s cap) (hh : Handle cap (i + 1)) (hg : Handle cap g) (hk : k.toNat < 8) :
    field (reclaim s i) g k =
      if g = i + 1 then if k = 1 then field s g k else if k = 2 then read s 8 else 0
      else field s g k := by
  have nr : ∀ r : UInt64, r.toNat < 24 → address g + k ≠ r :=
    fun _ hr => cell_index_not_register hs.2.1 hg hk hr
  have eq : ∀ j : UInt64, j.toNat < 8 →
      (address g + k = address (i + 1) + j ↔ g = i + 1 ∧ k = j) :=
    fun _ hj => cell_index_eq_iff hs.2.1 hg hh hk hj
  have zero : (address g + k = address (i + 1)) ↔ g = i + 1 ∧ k = 0 := by
    simpa only [UInt64.add_zero] using eq 0 (by decide)
  rw [field, reclaim_read hs hh]
  simp only [nr 9 (by decide), nr 8 (by decide), ite_false,
    eq 7 (by decide), eq 6 (by decide), eq 5 (by decide), eq 4 (by decide),
    eq 3 (by decide), eq 2 (by decide), zero]
  by_cases same : g = i + 1
  · simp only [same, true_and, ite_true]
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
      have ns : k.toNat = 0 ∨ k.toNat = 1 ∨ k.toNat = 2 ∨ k.toNat = 3 ∨
          k.toNat = 4 ∨ k.toNat = 5 ∨ k.toNat = 6 ∨ k.toNat = 7 := by omega
      simpa only [← UInt64.toNat_inj, UInt64.reduceToNat] using ns
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [field]
  · simp only [same, false_and, ite_false, field]

theorem reclaim_shape {s : Array UInt64} {cap : Nat} {i : UInt64}
    (hs : Shape s cap) (hh : Handle cap (i + 1)) : Shape (reclaim s i) cap := by
  refine ⟨hs.1, hs.2.1, by simpa using hs.2.2.1, ?_⟩
  rw [reclaim_register hs hh (show (14 : UInt64).toNat < 24 by decide)]
  simpa using hs.2.2.2

theorem sweepNext_shape {s : Array UInt64} {cap : Nat} {i : UInt64}
    (hs : Shape s cap) (hh : Handle cap (i + 1)) : Shape (sweepNext s i).2 cap := by
  simp only [sweepNext]
  split
  · exact hs
  · exact reclaim_shape hs hh

theorem sweepNext_mark {s : Array UInt64} {cap : Nat} {i g : UInt64}
    (hs : Shape s cap) (hh : Handle cap (i + 1)) (hg : Handle cap g) :
    field (sweepNext s i).2 g 1 = field s g 1 := by
  simp only [sweepNext]
  split
  · rfl
  · rw [reclaim_field hs hh hg (show (1 : UInt64).toNat < 8 by decide)]
    split <;> simp

theorem sweepNext_preserves_marked {s : Array UInt64} {cap : Nat} {i g k : UInt64}
    (hs : Shape s cap) (hh : Handle cap (i + 1)) (hg : Handle cap g) (hk : k.toNat < 8)
    (marked : field s g 1 ≠ 0) : field (sweepNext s i).2 g k = field s g k := by
  simp only [sweepNext]
  split
  · rfl
  · rename_i unmarked
    have fresh : g ≠ i + 1 := by
      intro same
      subst g
      simp [marked] at unmarked
    rw [reclaim_field hs hh hg hk]
    simp only [fresh, ite_false]

theorem reclaim_chain {s : Array UInt64} {cap : Nat} {i : UInt64} {nodes : List UInt64}
    (hs : Shape s cap) (hh : Handle cap (i + 1))
    (chain : Chain s cap (read s 8) nodes) (fresh : i + 1 ∉ nodes) :
    Chain (reclaim s i) cap (i + 1) ((i + 1) :: nodes) := by
  refine Chain.cons (next := read s 8) hh ?_ ?_ fresh ?_
  · rw [reclaim_field hs hh hh (show (0 : UInt64).toNat < 8 by decide)]
    simp
  · rw [reclaim_field hs hh hh (show (2 : UInt64).toNat < 8 by decide)]
    simp
  · apply chain_transfer chain
    intro g mem
    have hg := chain_handle chain mem
    have ne : g ≠ i + 1 := by intro eq; subst g; exact fresh mem
    constructor
    · rw [reclaim_field hs hh hg (show (0 : UInt64).toNat < 8 by decide)]
      simp only [ne, ite_false]
    · rw [reclaim_field hs hh hg (show (2 : UInt64).toNat < 8 by decide)]
      simp only [ne, ite_false]

/-- The complete sweep keeps every word of every marked cell, regardless of
the contents of the unmarked cells or the order of the old free list. -/
theorem finishCollection_preserves_marked {s : Array UInt64} {cap : Nat} {g k : UInt64}
    (hs : Shape s cap) (hg : Handle cap g) (hk : k.toNat < 8)
    (marked : field s g 1 ≠ 0) (count : UInt64) :
    field (finishCollection s (read s 14) count) g k = field s g k := by
  let start := write (write (write s 8 0) 9 0) 10 0
  have startShape : Shape start cap :=
    write_shape (write_shape (write_shape hs (by decide)) (by decide)) (by decide)
  have startFields : ∀ j : UInt64, j.toNat < 8 → field start g j = field s g j := by
    intro j hj
    dsimp [start]
    rw [field_write_register
      (write_shape (write_shape hs (by decide)) (by decide)) hg hj (show (10 : UInt64).toNat < 24 by decide),
      field_write_register (write_shape hs (by decide)) hg hj (show (9 : UInt64).toNat < 24 by decide),
      field_write_register hs hg hj (show (8 : UInt64).toNat < 24 by decide)]
  let P := fun st : UInt64 × Array UInt64 => st.1.toNat ≤ cap ∧ Shape st.2 cap ∧
    field st.2 g 1 ≠ 0 ∧ field st.2 g k = field s g k
  have initial : P (0, start) :=
    ⟨Nat.zero_le _, startShape, by rw [startFields 1 (by decide)]; exact marked, startFields k hk⟩
  have preserve : ∀ st, P st → (decide (st.1 < read s 14)) = true →
      P (sweepNext st.2 st.1) := by
    rintro ⟨i, t⟩ ⟨_, ht, hm, same⟩ test
    have hi : i.toNat < cap := by
      have hi := of_decide_eq_true test
      simpa only [UInt64.lt_iff_toNat_lt, hs.2.2.2] using hi
    have hh := successor_handle hs.2.1 hi
    refine ⟨hh.2, sweepNext_shape ht hh, ?_, ?_⟩
    · rw [sweepNext_mark ht hh hg]; exact hm
    · rw [sweepNext_preserves_marked ht hh hg hk hm]; exact same
  have final := Project.Smalltalk.Loops.repeat_invariant P
    (fun st => decide (st.1 < read s 14)) (fun st => sweepNext st.2 st.1)
    preserve (read s 14) (0, start) initial
  rw [finishCollection]
  change field (write (LeanExe.repeatWhile (read s 14) (0, start)
    (fun st => decide (st.1 < read s 14)) (fun st => sweepNext st.2 st.1)).2 11 count) g k = _
  rw [field_write_register final.2.1 hg hk (show (11 : UInt64).toNat < 24 by decide)]
  exact final.2.2.2

theorem sweepNext_register {s : Array UInt64} {cap : Nat} {i r : UInt64}
    (hs : Shape s cap) (hh : Handle cap (i + 1)) (hr : r.toNat < 24)
    (notHead : r ≠ 8) (notCount : r ≠ 9) : read (sweepNext s i).2 r = read s r := by
  simp only [sweepNext]
  split
  · rfl
  · rw [reclaim_register hs hh hr]
    simp only [notHead, notCount, ite_false]

theorem finishCollection_shape {s : Array UInt64} {cap : Nat} (hs : Shape s cap) (count : UInt64) :
    Shape (finishCollection s (read s 14) count) cap := by
  let start := write (write (write s 8 0) 9 0) 10 0
  have ht : Shape start cap :=
    write_shape (write_shape (write_shape hs (by decide)) (by decide)) (by decide)
  let P := fun st : UInt64 × Array UInt64 => st.1.toNat ≤ cap ∧ Shape st.2 cap
  have step : ∀ st, P st → decide (st.1 < read s 14) = true → P (sweepNext st.2 st.1) := by
    rintro ⟨i, t⟩ ⟨_, ht⟩ test
    have hi : i.toNat < cap := by
      have hi := of_decide_eq_true test
      simpa only [UInt64.lt_iff_toNat_lt, hs.2.2.2] using hi
    have hh := successor_handle hs.2.1 hi
    exact ⟨hh.2, sweepNext_shape ht hh⟩
  have final := Project.Smalltalk.Loops.repeat_invariant P _ _ step (read s 14) (0, start)
    ⟨Nat.zero_le _, ht⟩
  exact write_shape final.2 (by decide)

theorem finishCollection_register {s : Array UInt64} {cap : Nat} {r : UInt64}
    (hs : Shape s cap) (hr : r.toNat < 24)
    (notHead : r ≠ 8) (notCount : r ≠ 9) (notLast : r ≠ 10) (notStats : r ≠ 11) (count : UInt64) :
    read (finishCollection s (read s 14) count) r = read s r := by
  let start := write (write (write s 8 0) 9 0) 10 0
  have ht : Shape start cap :=
    write_shape (write_shape (write_shape hs (by decide)) (by decide)) (by decide)
  have initialRead : read start r = read s r := by
    dsimp [start]
    rw [read_write_other _ _ _ _ (Ne.symm notLast), read_write_other _ _ _ _ (Ne.symm notCount),
      read_write_other _ _ _ _ (Ne.symm notHead)]
  let P := fun st : UInt64 × Array UInt64 => st.1.toNat ≤ cap ∧ Shape st.2 cap ∧ read st.2 r = read s r
  have step : ∀ st, P st → decide (st.1 < read s 14) = true → P (sweepNext st.2 st.1) := by
    rintro ⟨i, t⟩ ⟨_, ht, same⟩ test
    have hi : i.toNat < cap := by
      have hi := of_decide_eq_true test
      simpa only [UInt64.lt_iff_toNat_lt, hs.2.2.2] using hi
    have hh := successor_handle hs.2.1 hi
    exact ⟨hh.2, sweepNext_shape ht hh, (sweepNext_register ht hh hr notHead notCount).trans same⟩
  have final := Project.Smalltalk.Loops.repeat_invariant P _ _ step (read s 14) (0, start)
    ⟨Nat.zero_le _, ht, initialRead⟩
  rw [finishCollection]
  change read (write (LeanExe.repeatWhile (read s 14) (0, start) _ _).2 11 count) r = _
  rw [read_write_other _ _ _ _ (Ne.symm notStats)]
  exact final.2.2

end Project.Smalltalk.Sweep
