import Project.Smalltalk.Seeding

namespace Project.Smalltalk.InitializationGraph
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.InitializationBase Project.Smalltalk.SeedMemory Project.Smalltalk.Seeding

theorem init_register (requested stress r : UInt64) (bound : r.toNat < 24) :
    read (init requested stress) r =
      if r = 13 then 3 else if r = 9 then capacity requested - 3 else if r = 8 then 4 else
      if r = 12 then stress else if r = 14 then capacity requested else 0 := by
  rw [(init_cells requested stress).2.1 r bound, headers_read (capacity_bounds requested).2]

theorem init_roots (requested stress h : UInt64) :
    Root (init requested stress) h ↔ h = 1 ∨ h = 2 ∨ h = 3 := by
  have current : read (init requested stress) 2 = 0 := by rw [init_register _ _ _ (by decide)]; simp
  have result : read (init requested stress) 7 = 0 := by rw [init_register _ _ _ (by decide)]; simp
  have external : read (init requested stress) 16 = 0 := by rw [init_register _ _ _ (by decide)]; simp
  simp only [Root, current, result, external, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨nonzero, (one | two | three | zero | zero | zero)⟩
    · exact Or.inl one
    · exact Or.inr (Or.inl two)
    · exact Or.inr (Or.inr three)
    · exact False.elim (nonzero zero)
    · exact False.elim (nonzero zero)
    · exact False.elim (nonzero zero)
  · rintro (rfl | rfl | rfl) <;> simp

theorem init_tag (requested stress : UInt64) {h : UInt64} (handle : Handle (capacity requested).toNat h) :
    field (init requested stress) h 0 = if h ≤ 3 then 2 else 0 := by
  rw [(init_cells requested stress).2.2 h handle 0 (by decide)]
  simp [seededWord]

theorem canonical_handle (requested : UInt64) {h : UInt64} (canonical : h = 1 ∨ h = 2 ∨ h = 3) :
    Handle (capacity requested).toNat h := by
  have bounds := capacity_bounds requested
  rcases canonical with rfl | rfl | rfl <;> simp only [Handle, UInt64.reduceToNat] <;> omega

theorem scalar_no_edge {s : Array UInt64} {parent child : UInt64} (tag : field s parent 0 = 2) :
    ¬Edge s parent child := by
  rintro ⟨_, k, _, pointer, _⟩
  rw [tag] at pointer
  simp [PointerField] at pointer

/-- A freshly initialized arena meets all assumptions of the collector's
typed graph theorem. Its only allocated cells are the three canonical values. -/
theorem init_graph_valid (requested stress : UInt64) : Graph.Valid (init requested stress) (capacity requested).toNat := by
  have shape := (init_cells requested stress).1
  refine ⟨shape, ?_, ?_, ?_⟩
  · intro h root
    have canonical := (init_roots requested stress h).mp root
    have handle := canonical_handle requested canonical
    refine ⟨handle, ?_⟩
    rcases canonical with rfl | rfl | rfl <;> rw [init_tag requested stress handle] <;> decide
  · intro parent child handle allocated edge
    have canonical : parent ≤ 3 := by
      by_cases canonical : parent ≤ 3
      · exact canonical
      · rw [init_tag requested stress handle] at allocated
        simp only [canonical, ite_false] at allocated
        exact False.elim (allocated rfl)
    have tag : field (init requested stress) parent 0 = 2 := by
      rw [init_tag requested stress handle]
      simp only [canonical, ite_true]
    exact False.elim (scalar_no_edge tag edge)
  · intro h handle allocated
    rw [init_tag requested stress handle] at allocated ⊢
    by_cases canonical : h ≤ 3
    · simp only [canonical, ite_true, ValidTag]
      simp
    · simp only [canonical, ite_false] at allocated
      exact False.elim (allocated rfl)

end Project.Smalltalk.InitializationGraph
