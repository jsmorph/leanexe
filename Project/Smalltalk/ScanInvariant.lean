import Project.Smalltalk.ScanMemory

namespace Project.Smalltalk.ScanInvariant
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Worklist Project.Smalltalk.MarkInvariant Project.Smalltalk.ScanMemory

theorem moved_members (done queue : List UInt64) (h g : UInt64) :
    g ∈ (h :: done) ++ queue ↔ g ∈ done ++ (queue ++ [h]) := by
  simp [List.mem_append, or_comm, or_left_comm]

theorem pop_holds {original t : Array UInt64} {cap : Nat} {done queue : List UInt64} {h : UInt64}
    (st : Holds original t cap done (queue ++ [h])) :
    Holds original (write t 18 (read t 18 - 1)) cap (h :: done) queue := by
  constructor
  · exact write_shape st.shape (by decide)
  · intro g hg k hk nonmark
    rw [field_write_register st.shape hg hk (show (18 : UInt64).toNat < 24 by decide)]
    exact st.payload g hg k hk nonmark
  · intro r hr nr
    rw [read_write_other _ _ _ _ (Ne.symm nr)]
    exact st.registers r hr nr
  · exact pop_represents st.shape st.work
  · apply (List.perm_append_comm (l₁ := done ++ queue) (l₂ := [h])).nodup
    simpa only [List.append_assoc] using st.distinct
  · intro g hg
    rw [field_write_register st.shape hg (show (1 : UInt64).toNat < 8 by decide)
      (show (18 : UInt64).toNat < 24 by decide)]
    exact (st.marks g hg).trans (moved_members done queue h g).symm
  · intro g mem
    exact st.sound g ((moved_members done queue h g).mp mem)

theorem pointers_same {original t : Array UInt64} {cap : Nat} {done queue : List UInt64} {h : UInt64}
    (st : Holds original t cap done queue) (hh : Handle cap h) : pointers t h = pointers original h := by
  simp only [pointers]
  rw [st.payload h hh 0 (by decide) (by decide), st.payload h hh 2 (by decide) (by decide),
    st.payload h hh 3 (by decide) (by decide), st.payload h hh 4 (by decide) (by decide),
    st.payload h hh 5 (by decide) (by decide), st.payload h hh 6 (by decide) (by decide),
    st.payload h hh 7 (by decide) (by decide)]

/-- A scan moves one distinct pending handle to the scanned list and closes
all its outgoing edges. Cycles and repeated pointer fields remain allowed. -/
theorem scan_holds {original t : Array UInt64} {cap : Nat} {done queue : List UInt64} {h : UInt64}
    (valid : Graph.Valid original cap) (st : Holds original t cap done (queue ++ [h]))
    (closed : Closed original done (queue ++ [h])) :
    ∃ more, Holds original (scanCell t) cap (h :: done) more ∧
      Closed original (h :: done) more ∧
      (∀ g ∈ done ++ (queue ++ [h]), g ∈ (h :: done) ++ more) := by
  have reached : Reachable original h := st.sound h (by simp)
  have hh := (reachable_allocated valid reached).1
  have tag := valid.2.2.2 h hh (reachable_allocated valid reached).2
  have tagNow : ValidTag (field t h 0) := by rw [st.payload h hh 0 (by decide) (by decide)]; exact tag
  have popped := pop_holds st
  have inputs : ∀ child ∈ pointers original h, child = 0 ∨ Reachable original child := by
    intro child mem
    by_cases zero : child = 0
    · exact Or.inl zero
    · exact Or.inr (Reachable.next reached ((edge_pointers tag).mpr ⟨zero, mem⟩))
  rcases markList_holds valid popped (pointers original h) inputs with ⟨more, final, keep, covers⟩
  have monotone : ∀ g ∈ done ++ (queue ++ [h]), g ∈ (h :: done) ++ more := by
    intro g mem
    exact keep g ((moved_members done queue h g).mpr mem)
  refine ⟨more, ?_, ?_, monotone⟩
  · rw [scanCell_eq st.shape st.work hh tagNow, pointers_same st hh]
    exact final
  · intro parent visited child edge
    rcases List.mem_cons.mp visited with same | prior
    · subst parent
      have refs : child ∈ pointers original h := ((edge_pointers tag).mp edge).2
      exact covers child refs edge.1
    · exact monotone child (closed parent prior child edge)

end Project.Smalltalk.ScanInvariant
