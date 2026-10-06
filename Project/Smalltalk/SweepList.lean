import Project.Smalltalk.Sweep

namespace Project.Smalltalk.SweepList
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.FreeList
open Project.Smalltalk.Sweep Project.Smalltalk.Loops

def Prefix (original t : Array UInt64) (cap : Nat) (i : UInt64) (nodes : List UInt64) : Prop :=
  Shape t cap ∧ (∀ g, Handle cap g → field t g 1 = field original g 1) ∧
  Chain t cap (read t 8) nodes ∧ (read t 9).toNat = nodes.length ∧ nodes.length ≤ i.toNat ∧
    ∀ g, Handle cap g → (g ∈ nodes ↔ g.toNat ≤ i.toNat ∧ field original g 1 = 0)

theorem prefix_step {original t : Array UInt64} {cap : Nat} {i : UInt64} {nodes : List UInt64}
    (p : Prefix original t cap i nodes) (hi : i.toNat < cap) :
    ∃ more, Prefix original (sweepNext t i).2 cap (i + 1) more := by
  rcases p with ⟨ht, marks, chain, count, length, members⟩
  have hh := successor_handle ht.2.1 hi
  have inc := successor_toNat (i := i) (by have := ht.2.1; omega)
  by_cases zero : field original (i + 1) 1 = 0
  · have hz : field t (i + 1) 1 = 0 := (marks _ hh).trans zero
    have effect : (sweepNext t i).2 = reclaim t i := by
      simp only [sweepNext, bne_iff_ne, hz, ne_eq, not_true, ite_false]
    rw [effect]
    have fresh : i + 1 ∉ nodes := by
      intro mem
      have bound := ((members _ hh).mp mem).1
      rw [inc] at bound
      omega
    refine ⟨(i + 1) :: nodes, reclaim_shape ht hh, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rw [reclaim_field ht hh hg (show (1 : UInt64).toNat < 8 by decide)]
      split <;> simp only [ite_true, marks g hg]
    · rw [reclaim_register ht hh (show (8 : UInt64).toNat < 24 by decide)]
      simp only [show (8 : UInt64) ≠ 9 by decide, ite_false, ite_true]
      exact reclaim_chain ht hh chain fresh
    · rw [reclaim_register ht hh (show (9 : UInt64).toNat < 24 by decide)]
      simp only [ite_true, List.length_cons]
      rw [successor_toNat (i := read t 9) (by have := ht.2.1; omega), count]
    · simp only [List.length_cons, inc]
      omega
    · intro g hg
      rw [List.mem_cons, members g hg, inc]
      constructor
      · rintro (same | ⟨bound, mark⟩)
        · subst g; exact ⟨by omega, zero⟩
        · exact ⟨by omega, mark⟩
      · rintro ⟨bound, mark⟩
        by_cases prior : g.toNat ≤ i.toNat
        · exact Or.inr ⟨prior, mark⟩
        · left
          apply UInt64.toNat_inj.mp
          rw [inc]
          omega
  · have nz : field t (i + 1) 1 ≠ 0 := by rw [marks _ hh]; exact zero
    have effect : (sweepNext t i).2 = t := by
      simp only [sweepNext, bne_iff_ne]
      exact ite_eq_left nz
    rw [effect]
    refine ⟨nodes, ht, marks, chain, count, ?_, ?_⟩
    · rw [inc]; omega
    · intro g hg
      rw [members g hg, inc]
      constructor
      · rintro ⟨bound, mark⟩; exact ⟨by omega, mark⟩
      · rintro ⟨bound, mark⟩
        refine ⟨?_, mark⟩
        by_cases prior : g.toNat ≤ i.toNat
        · exact prior
        · have same : g = i + 1 := by
            apply UInt64.toNat_inj.mp
            rw [inc]
            omega
          subst g
          exact False.elim (zero mark)

/-- Sweeping builds a list containing exactly the unmarked handles, without
duplicates, with its exact count. Every marked cell must have a nonzero tag. -/
theorem finishCollection_freeList {s : Array UInt64} {cap : Nat}
    (hs : Shape s cap) (live : ∀ g, Handle cap g → field s g 1 ≠ 0 → field s g 0 ≠ 0)
    (gcCount : UInt64) :
    ∃ nodes, Valid (finishCollection s (read s 14) gcCount) cap nodes ∧
      (∀ g, Handle cap g → (g ∈ nodes ↔ field s g 1 = 0)) ∧ nodes.Nodup := by
  let start := write (write (write s 8 0) 9 0) 10 0
  have ht : Shape start cap :=
    write_shape (write_shape (write_shape hs (by decide)) (by decide)) (by decide)
  have head : read start 8 = 0 := by
    dsimp [start]
    rw [read_write_other _ 10 8 _ (by decide), read_write_other _ 9 8 _ (by decide),
      read_write_same _ _ _ (register_bound hs (show (8 : UInt64).toNat < 24 by decide))]
  have count : read start 9 = 0 := by
    dsimp [start]
    rw [read_write_other _ 10 9 _ (by decide), read_write_same]
    simpa only [write_size] using register_bound hs (show (9 : UInt64).toNat < 24 by decide)
  have marks : ∀ g, Handle cap g → field start g 1 = field s g 1 := by
    intro g hg
    dsimp [start]
    rw [field_write_register (write_shape (write_shape hs (by decide)) (by decide)) hg
        (show (1 : UInt64).toNat < 8 by decide) (show (10 : UInt64).toNat < 24 by decide),
      field_write_register (write_shape hs (by decide)) hg
        (show (1 : UInt64).toNat < 8 by decide) (show (9 : UInt64).toNat < 24 by decide),
      field_write_register hs hg (show (1 : UInt64).toNat < 8 by decide)
        (show (8 : UInt64).toNat < 24 by decide)]
  have initial : Prefix s start cap 0 [] := by
    refine ⟨ht, marks, ?_, ?_, by simp, ?_⟩
    · rw [head]; exact Chain.nil
    · rw [count]; rfl
    · intro g hg
      have positive := hg.1
      simp only [List.not_mem_nil, false_iff, UInt64.reduceToNat]
      omega
  let P := fun st : UInt64 × Array UInt64 => st.1.toNat ≤ cap ∧ ∃ nodes, Prefix s st.2 cap st.1 nodes
  have preserve : ∀ st, P st → decide (st.1 < read s 14) = true → P (sweepNext st.2 st.1) := by
    rintro ⟨i, t⟩ ⟨_, nodes, covered⟩ test
    have hi : i.toNat < cap := by
      have hi := of_decide_eq_true test
      simpa only [UInt64.lt_iff_toNat_lt, hs.2.2.2] using hi
    exact ⟨(successor_handle hs.2.1 hi).2, prefix_step covered hi⟩
  let final := LeanExe.repeatWhile (read s 14) (0, start)
    (fun st => decide (st.1 < read s 14)) (fun st => sweepNext st.2 st.1)
  have invariant : P final := repeat_invariant P _ _ preserve (read s 14) (0, start)
    ⟨Nat.zero_le _, [], initial⟩
  have endIndex : final.1.toNat = cap := by
    have index := counted_index (fun t i => (sweepNext t i).2) (read s 14)
      (by rw [hs.2.2.2]; exact hs.2.1) (read s 14).toNat 0 start (by simp)
    simpa only [final, LeanExe.repeatWhile, sweepNext, UInt64.reduceToNat, Nat.zero_add,
      hs.2.2.2] using index
  rcases invariant.2 with ⟨nodes, ht, marks, chain, count, length, members⟩
  have all : ∀ g, Handle cap g → (g ∈ nodes ↔ field s g 1 = 0) := by
    intro g hg
    rw [members g hg, endIndex]
    simp only [hg.2, true_and]
  have free : Valid final.2 cap nodes := by
    refine ⟨chain, count, ?_⟩
    intro g hg
    constructor
    · intro zero
      apply (all g hg).mpr
      by_cases marked : field s g 1 = 0
      · exact marked
      · have keep := finishCollection_preserves_marked hs hg (show (0 : UInt64).toNat < 8 by decide)
          marked gcCount
        have stat : field (write final.2 11 gcCount) g 0 = field final.2 g 0 :=
          field_write_register ht hg (by decide) (by decide)
        change field (write final.2 11 gcCount) g 0 = field s g 0 at keep
        rw [stat, zero] at keep
        exact False.elim (live g hg marked keep.symm)
    · intro mem
      exact chain_tag chain mem
  refine ⟨nodes, ?_, all, chain_nodup chain⟩
  change Valid (write final.2 11 gcCount) cap nodes
  apply valid_transfer free
  · exact read_write_other _ _ _ _ (by decide)
  · exact read_write_other _ _ _ _ (by decide)
  · intro g hg
    exact ⟨field_write_register ht hg (by decide) (by decide),
      field_write_register ht hg (by decide) (by decide)⟩

end Project.Smalltalk.SweepList
