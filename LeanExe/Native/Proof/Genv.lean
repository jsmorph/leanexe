import LeanExe.Native.Proof.Basics

/-!
Global environments built by `globalenv`: when a program's identifiers are distinct, each
definition is found under its identifier.
-/

namespace LClight

namespace Genv

variable {F V : Type}

theorem symb_insert_ne {m : Std.TreeMap ident block} {k a : ident} (v : block) (h : k ≠ a) :
    (m.insert k v)[a]? = m[a]? := by
  rw [Std.TreeMap.getElem?_insert]
  have : compare k a ≠ .eq := fun e => h (Nat.compare_eq_eq.mp e)
  simp [this]

theorem defs_insert_ne {m : Std.TreeMap block (globdef F V)} {k a : block} (v : globdef F V)
    (h : k ≠ a) : (m.insert k v)[a]? = m[a]? := by
  rw [Std.TreeMap.getElem?_insert]
  have : compare k a ≠ .eq := fun e => h (Nat.compare_eq_eq.mp e)
  simp [this]

theorem add_globals_cons (ge : t F V) (x : ident × globdef F V) (gl : List (ident × globdef F V)) :
    add_globals ge (x :: gl) = add_globals (add_global ge x) gl := rfl

theorem add_globals_next (ge : t F V) (gl : List (ident × globdef F V)) :
    (add_globals ge gl).genv_next = ge.genv_next + gl.length := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x gl ih =>
      rw [add_globals_cons, ih]
      simp only [add_global, List.length_cons]
      rw [Nat.add_assoc, Nat.add_comm 1]

/-- Adding definitions keeps the symbols they do not name and the blocks below `genv_next`. -/
theorem add_globals_keep (ge : t F V) (gl : List (ident × globdef F V)) :
    (∀ id, id ∉ gl.map (·.1) → find_symbol (add_globals ge gl) id = find_symbol ge id) ∧
    (∀ b, b < ge.genv_next → find_def (add_globals ge gl) b = find_def ge b) := by
  induction gl generalizing ge with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons x gl ih =>
      obtain ⟨h1, h2⟩ := ih (add_global ge x)
      refine ⟨fun id hid => ?_, fun b hb => ?_⟩
      · simp only [List.map_cons, List.mem_cons, not_or] at hid
        rw [add_globals_cons, h1 id hid.2]
        exact symb_insert_ne _ (Ne.symm hid.1)
      · rw [add_globals_cons, h2 b (Nat.lt_succ_of_lt hb)]
        exact defs_insert_ne _ (Nat.ne_of_gt hb)

/-- Each definition of a list with distinct identifiers is found under its identifier. -/
theorem find_add_globals (ge : t F V) (gl : List (ident × globdef F V))
    (hnodup : (gl.map (·.1)).Nodup) {id : ident} {d : globdef F V} (hmem : (id, d) ∈ gl) :
    ∃ b, find_symbol (add_globals ge gl) id = some b ∧ find_def (add_globals ge gl) b = some d := by
  induction gl generalizing ge with
  | nil => simp at hmem
  | cons x gl ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with rfl | hmem
      · obtain ⟨h1, h2⟩ := add_globals_keep (add_global ge (id, d)) gl
        refine ⟨ge.genv_next, ?_, ?_⟩
        · rw [add_globals_cons, h1 id hnodup.1]
          exact Std.TreeMap.getElem?_insert_self
        · rw [add_globals_cons, h2 _ (Nat.lt_succ_self _)]
          exact Std.TreeMap.getElem?_insert_self
      · rw [add_globals_cons]
        exact ih (add_global ge x) hnodup.2 hmem

theorem find_funct_ptr_of_def {ge : t F V} {b : block} {f : F}
    (h : find_def ge b = some (.Gfun f)) : find_funct_ptr ge b = some f := by
  simp [find_funct_ptr, h]

end Genv

end LClight
