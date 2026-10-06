import Project.Smalltalk.Graph
import Project.Smalltalk.Worklist
import Project.Smalltalk.Clear

namespace Project.Smalltalk.MarkInvariant
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.MarkMemory
open Project.Smalltalk.Graph Project.Smalltalk.Worklist

/-- Relates the actual array, mark words, and worklist to scanned and pending
handles. The graph is always read from the original payloads. -/
structure Holds (original t : Array UInt64) (cap : Nat) (done queue : List UInt64) : Prop where
  shape : Shape t cap
  payload : SamePayload original t cap
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 18 → read t r = read original r
  work : Represents t cap queue
  distinct : (done ++ queue).Nodup
  marks : ∀ h, Handle cap h → (field t h 1 ≠ 0 ↔ h ∈ done ++ queue)
  sound : ∀ h ∈ done ++ queue, Reachable original h

def Closed (original : Array UInt64) (done queue : List UInt64) : Prop :=
  ∀ parent ∈ done, ∀ child, Edge original parent child → child ∈ done ++ queue

theorem bounds {original t cap done queue} (st : Holds original t cap done queue)
    (valid : Graph.Valid original cap) : ∀ h ∈ done ++ queue, Handle cap h :=
  fun h mem => (reachable_allocated valid (st.sound h mem)).1

/-- The concrete checked `mark` preserves the graph invariant. It either
leaves the pending list alone or appends the new handle exactly once. Space
is derived from distinct valid handles, not assumed. -/
theorem mark_holds {original t : Array UInt64} {cap : Nat} {done queue : List UInt64} {h : UInt64}
    (valid : Graph.Valid original cap) (st : Holds original t cap done queue)
    (input : h = 0 ∨ Reachable original h) :
    ∃ more, Holds original (mark t h) cap done more ∧
      (more = queue ∨ more = queue ++ [h]) ∧ (h ≠ 0 → h ∈ done ++ more) := by
  by_cases zero : h = 0
  · subst h
    rw [mark_zero]
    exact ⟨queue, st, Or.inl rfl, fun impossible => False.elim (impossible rfl)⟩
  have reached : Reachable original h := input.resolve_left zero
  have hh := (reachable_allocated valid reached).1
  have allocated : field t h 0 ≠ 0 := by
    rw [st.payload h hh 0 (by decide) (by decide)]
    exact (reachable_allocated valid reached).2
  by_cases emptyMark : field t h 1 = 0
  · have fresh : h ∉ done ++ queue := by
      intro mem
      exact (st.marks h hh).mpr mem emptyMark
    have room := enqueue_room st.distinct (bounds st valid) hh fresh
    have space : (read t 18).toNat < cap := by rw [st.work.count]; exact room
    rw [mark_new st.shape hh space allocated emptyMark]
    refine ⟨queue ++ [h], ?_, Or.inr rfl, ?_⟩
    · constructor
      · exact markReady_shape st.shape hh space
      · intro g hg k hk nonmark
        rw [markReady_preserves_payload st.shape hh space hg hk nonmark]
        exact st.payload g hg k hk nonmark
      · intro r hr nr
        rw [markReady_register st.shape hh space hr]
        simp only [nr, ite_false]
        exact st.registers r hr nr
      · exact enqueue_represents st.shape hh st.work room
      · rw [← List.append_assoc, List.nodup_append]
        refine ⟨st.distinct, by simp, ?_⟩
        intro a old b last same
        have bEq : b = h := by simpa using last
        subst b
        subst a
        exact fresh old
      · intro g hg
        rw [markReady_field st.shape hh space hg (show (1 : UInt64).toNat < 8 by decide)]
        by_cases same : g = h
        · subst g
          simp
        · simp only [same, false_and, ite_false]
          rw [st.marks g hg]
          simp [List.mem_append, same]
      · intro g mem
        rw [← List.append_assoc, List.mem_append] at mem
        rcases mem with old | last
        · exact st.sound g old
        · have same : g = h := by simpa using last
          subst g; exact reached
    · intro _
      simp
  · rw [mark_old st.shape hh allocated emptyMark]
    exact ⟨queue, st, Or.inl rfl, fun _ => (st.marks h hh).mp emptyMark⟩

theorem marks_monotone {done queue more : List UInt64} {h : UInt64}
    (growth : more = queue ∨ more = queue ++ [h]) :
    ∀ g ∈ done ++ queue, g ∈ done ++ more := by
  intro g mem
  rcases growth with rfl | rfl
  · exact mem
  · rw [← List.append_assoc]
    exact List.mem_append.mpr (Or.inl mem)

theorem initial_holds {original : Array UInt64} {cap : Nat} (valid : Graph.Valid original cap) :
    Holds original (write (Project.Smalltalk.Clear.cleared original) 18 0) cap [] [] := by
  have shape := Project.Smalltalk.Clear.cleared_shape valid.1
  constructor
  · exact write_shape shape (by decide)
  · intro g hg k hk nonmark
    rw [field_write_register shape hg hk (show (18 : UInt64).toNat < 24 by decide)]
    exact Project.Smalltalk.Clear.cleared_payload valid.1 hg hk nonmark
  · intro r hr noncount
    rw [read_write_other _ _ _ _ (Ne.symm noncount)]
    exact Project.Smalltalk.Clear.cleared_register valid.1 hr
  · constructor
    · rw [read_write_same _ _ _ (register_bound shape (show (18 : UInt64).toNat < 24 by decide))]
      rfl
    · exact Nat.zero_le _
    · intro i impossible; simp at impossible
  · exact List.nodup_nil
  · intro g hg
    rw [field_write_register shape hg (show (1 : UInt64).toNat < 8 by decide)
      (show (18 : UInt64).toNat < 24 by decide), Project.Smalltalk.Clear.cleared_marks valid.1 hg]
    simp
  · intro h impossible; simp at impossible

theorem markList_holds {original t : Array UInt64} {cap : Nat} {done queue : List UInt64}
    (valid : Graph.Valid original cap) (st : Holds original t cap done queue) (refs : List UInt64)
    (inputs : ∀ h ∈ refs, h = 0 ∨ Reachable original h) :
    ∃ more, Holds original (refs.foldl mark t) cap done more ∧
      (∀ g ∈ done ++ queue, g ∈ done ++ more) ∧
      (∀ h ∈ refs, h ≠ 0 → h ∈ done ++ more) := by
  induction refs generalizing t queue with
  | nil => exact ⟨queue, st, fun _ mem => mem, by simp⟩
  | cons h rest ih =>
    rcases mark_holds valid st (inputs h (by simp)) with ⟨mid, first, growth, covered⟩
    rcases ih first (fun g mem => inputs g (List.mem_cons_of_mem _ mem)) with
      ⟨more, final, keep, covers⟩
    refine ⟨more, final, ?_, ?_⟩
    · intro g mem
      exact keep g (marks_monotone growth g mem)
    · intro g mem nonzero
      rcases List.mem_cons.mp mem with same | tail
      · subst g; exact keep h (covered nonzero)
      · exact covers g tail nonzero

theorem roots_holds {original t : Array UInt64} {cap : Nat} {queue : List UInt64}
    (valid : Graph.Valid original cap) (st : Holds original t cap [] queue) :
    ∃ more, Holds original (markRoots t) cap [] more ∧
      (∀ h, Root original h → h ∈ more) := by
  let refs := [1, 2, 3, read t 2, read t 7, read t 16]
  have same : refs = [1, 2, 3, read original 2, read original 7, read original 16] := by
    dsimp [refs]
    rw [st.registers 2 (by decide) (by decide), st.registers 7 (by decide) (by decide),
      st.registers 16 (by decide) (by decide)]
  have inputs : ∀ h ∈ refs, h = 0 ∨ Reachable original h := by
    intro h mem
    by_cases zero : h = 0
    · exact Or.inl zero
    · exact Or.inr (Reachable.root ⟨zero, same ▸ mem⟩)
  rcases markList_holds valid st refs inputs with ⟨more, final, _, covers⟩
  refine ⟨more, ?_, ?_⟩
  · exact final
  · intro h root
    have mem : h ∈ refs := same.symm ▸ root.2
    exact covers h mem root.1

end Project.Smalltalk.MarkInvariant
