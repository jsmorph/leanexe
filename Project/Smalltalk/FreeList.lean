import Project.Smalltalk.Allocation

namespace Project.Smalltalk.FreeList
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Allocation

/-- A finite free list, with distinct valid handles and the actual next words. -/
inductive Chain (s : Array UInt64) (cap : Nat) : UInt64 → List UInt64 → Prop
  | nil : Chain s cap 0 []
  | cons {h next rest} : Handle cap h → field s h 0 = 0 → field s h 2 = next →
      h ∉ rest → Chain s cap next rest → Chain s cap h (h :: rest)

def Valid (s : Array UInt64) (cap : Nat) (nodes : List UInt64) : Prop :=
  Chain s cap (read s 8) nodes ∧ (read s 9).toNat = nodes.length ∧
    ∀ h, Handle cap h → (field s h 0 = 0 ↔ h ∈ nodes)

theorem chain_handle {s cap head nodes} (hc : Chain s cap head nodes)
    {h} (hm : h ∈ nodes) : Handle cap h := by
  induction hc with
  | nil => simp at hm
  | cons hh _ _ _ _ ih =>
    rcases List.mem_cons.mp hm with eq | mem
    · subst h; exact hh
    · exact ih mem

theorem chain_nodup {s cap head nodes} (hc : Chain s cap head nodes) : nodes.Nodup := by
  induction hc with
  | nil => exact List.nodup_nil
  | cons _ _ _ absent _ ih => exact List.nodup_cons.mpr ⟨absent, ih⟩

theorem chain_transfer {s t cap head nodes} (hc : Chain s cap head nodes)
    (same : ∀ h ∈ nodes, field t h 0 = field s h 0 ∧ field t h 2 = field s h 2) :
    Chain t cap head nodes := by
  induction hc with
  | nil => exact .nil
  | @cons h next rest hh zero link absent tail ih =>
    have fields := same h (by simp)
    exact .cons hh (fields.1.trans zero) (fields.2.trans link) absent
      (ih (fun g hg => same g (List.mem_cons_of_mem _ hg)))

theorem chain_cons {s cap head h rest} (hc : Chain s cap head (h :: rest)) :
    head = h ∧ Handle cap h ∧ field s h 0 = 0 ∧ h ∉ rest ∧
      Chain s cap (field s h 2) rest := by
  cases hc with
  | cons hh zero link absent tail =>
    exact ⟨rfl, hh, zero, absent, by rw [link]; exact tail⟩

theorem chain_nil {s cap head} (hc : Chain s cap head []) : head = 0 := by
  cases hc
  rfl

/-- Allocation removes the head, preserves the order of every remaining free
cell, and leaves no zero-tagged cell outside that list. -/
theorem allocateCell_valid {s : Array UInt64} {cap : Nat} {h : UInt64} {rest : List UInt64}
    (hs : Shape s cap) (valid : Valid s cap (h :: rest))
    (tag a b c d e f : UInt64) (nonzero : tag ≠ 0) :
    Valid (allocateCell s tag a b c d e f) cap rest := by
  rcases valid with ⟨chain, count, complete⟩
  rcases chain_cons chain with ⟨hEq, hh, _, absent, tail⟩
  subst h
  have hhHead : Handle cap (read s 8) := hh
  have other : ∀ g ∈ rest, ∀ k : UInt64, k.toNat < 8 →
      field (allocateCell s tag a b c d e f) g k = field s g k := by
    intro g mem k bound
    have fresh : g ≠ read s 8 := by
      intro eq
      subst g
      exact absent mem
    exact allocateCell_preserves_other hs hhHead (chain_handle tail mem) bound fresh ..
  refine ⟨?_, ?_, ?_⟩
  · have head : read (allocateCell s tag a b c d e f) 8 = field s (read s 8) 2 := by
      rw [allocateCell_register hs hhHead (show (8 : UInt64).toNat < 24 by decide)]
      simp
    rw [head]
    exact chain_transfer tail (fun g mem => ⟨other g mem 0 (by decide), other g mem 2 (by decide)⟩)
  · have positive : (1 : UInt64) ≤ read s 9 := by
      simp only [UInt64.le_iff_toNat_le, UInt64.reduceToNat]
      simp only [List.length_cons] at count
      omega
    rw [allocateCell_register hs hhHead (show (9 : UInt64).toNat < 24 by decide)]
    simp
    rw [UInt64.toNat_sub_of_le _ _ positive]
    simp only [UInt64.reduceToNat]
    simp only [List.length_cons] at count
    omega
  · intro g hg
    rw [allocateCell_field hs hhHead hg (show (0 : UInt64).toNat < 8 by decide)]
    by_cases same : g = read s 8
    · subst g
      simp [allocatedWord, nonzero, absent]
    · simp only [same, ite_false]
      rw [complete g hg]
      simp [same]

theorem allocateCell_fresh {s : Array UInt64} {cap : Nat} {h : UInt64} {rest : List UInt64}
    (valid : Valid s cap (h :: rest)) : field s h 0 = 0 ∧ h ∉ rest ∧ rest.Nodup := by
  rcases chain_cons valid.1 with ⟨_, _, zero, absent, tail⟩
  exact ⟨zero, absent, chain_nodup tail⟩

theorem allocate_success {s : Array UInt64} {cap : Nat} {h : UInt64} {rest : List UInt64}
    (valid : Valid s cap (h :: rest)) (tag a b c d e f : UInt64) :
    allocate s tag a b c d e f = allocateCell s tag a b c d e f := by
  rcases chain_cons valid.1 with ⟨eq, hh, _⟩
  have nonzero : read s 8 ≠ 0 := by
    intro zero
    have positive := hh.1
    rw [← eq, zero] at positive
    exact (by decide : ¬ 1 ≤ (0 : UInt64).toNat) positive
  simp [allocate, nonzero]

theorem allocate_valid {s : Array UInt64} {cap : Nat} {h : UInt64} {rest : List UInt64}
    (hs : Shape s cap) (valid : Valid s cap (h :: rest))
    (tag a b c d e f : UInt64) (nonzero : tag ≠ 0) :
    Shape (allocate s tag a b c d e f) cap ∧ Valid (allocate s tag a b c d e f) cap rest := by
  rw [allocate_success valid]
  have head := chain_cons valid.1
  have hh : Handle cap (read s 8) := head.1 ▸ head.2.1
  exact ⟨allocateCell_shape hs hh .., allocateCell_valid hs valid _ _ _ _ _ _ _ nonzero⟩

theorem allocate_empty {s : Array UInt64} {cap : Nat}
    (valid : Valid s cap []) (tag a b c d e f : UInt64) :
    allocate s tag a b c d e f = fail s 9 := by
  unfold allocate
  rw [chain_nil valid.1]
  rfl

theorem allocate_empty_preserves_cells {s : Array UInt64} {cap : Nat}
    (hs : Shape s cap) (valid : Valid s cap [])
    {g k : UInt64} (hg : Handle cap g) (hk : k.toNat < 8)
    (tag a b c d e f : UInt64) :
    field (allocate s tag a b c d e f) g k = field s g k := by
  rw [allocate_empty valid, field, fail_read hs]
  simp only [cell_index_not_register hs.2.1 hg hk (show (15 : UInt64).toNat < 24 by decide),
    cell_index_not_register hs.2.1 hg hk (show (0 : UInt64).toNat < 24 by decide), ite_false, field]

end Project.Smalltalk.FreeList
