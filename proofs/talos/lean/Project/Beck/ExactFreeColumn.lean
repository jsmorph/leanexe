import Project.Beck.ExactCounting
import Project.Beck.Pivot
import Project.Beck.Basis

namespace Project.Beck.ExactFreeColumn

open LeanExe.Examples.BeckExact
open LeanExe.Examples.Beck (Input)

theorem source_eq (input : Input) (point : Point) (columns : Array UInt64) :
    freeColumn input point columns = ((List.range input.jobs).find?
      (fun job => !frozen point job && !LeanExe.Examples.Beck.contains columns job.toUInt64)).getD input.jobs := by
  simp only [freeColumn, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  change ((forIn (List.range input.jobs) (none, ()) (Pivot.searchStep
    (fun job => !frozen point job && !LeanExe.Examples.Beck.contains columns job.toUInt64))).run).1.getD _ = _
  rw [Pivot.forIn_find]
  rfl

theorem exists_free (input : Input) (point : Point) (columns : Array UInt64)
    (fits : input.jobs ≤ UInt64.size) (small : columns.size < (ExactCounting.live input point).card) :
    ∃ col < input.jobs, frozen point col = false ∧ col.toUInt64 ∉ columns := by
  by_contra! absent
  let values := (columns.toList.map UInt64.toNat).toFinset
  have included : (ExactCounting.live input point).image Fin.val ⊆ values := by
    intro col member
    obtain ⟨job, live, rfl⟩ := Finset.mem_image.mp member
    have flag : frozen point job.val = false := (Finset.mem_filter.mp live).2
    have chosen : job.val.toUInt64 ∈ columns := absent job.val job.isLt flag
    have encoded : job.val.toUInt64.toNat = job.val := by
      simp [Nat.toUInt64, Nat.mod_eq_of_lt (lt_of_lt_of_le job.isLt fits)]
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨job.val.toUInt64, Array.mem_toList_iff.mpr chosen, encoded⟩
  have imageSize : ((ExactCounting.live input point).image Fin.val).card =
      (ExactCounting.live input point).card := Finset.card_image_of_injective _ Fin.val_injective
  have upper : values.card ≤ columns.size :=
    (List.toFinset_card_le _).trans_eq (by simp)
  have := (Finset.card_le_card included).trans upper
  omega

theorem search_correct (input : Input) (point : Point) (columns : Array UInt64)
    (available : ∃ col < input.jobs, frozen point col = false ∧ col.toUInt64 ∉ columns) :
    let col := freeColumn input point columns
    col < input.jobs ∧ frozen point col = false ∧ col.toUInt64 ∉ columns := by
  rw [source_eq]
  cases found : (List.range input.jobs).find?
      (fun job => !frozen point job && !LeanExe.Examples.Beck.contains columns job.toUInt64) with
  | none =>
    obtain ⟨job, inside, live, fresh⟩ := available
    have falseAt := List.find?_eq_none.mp found job (List.mem_range.mpr inside)
    have absent := (Basis.contains_false_iff_not_mem columns job.toUInt64).mpr fresh
    simp [live, absent] at falseAt
  | some job =>
    have chosen := List.find?_some found
    have member := List.mem_of_find?_eq_some found
    simp only [Bool.and_eq_true] at chosen
    simp only [Option.getD_some]
    refine ⟨List.mem_range.mp member, ?_, ?_⟩
    · simpa using chosen.1
    · exact (Basis.contains_false_iff_not_mem _ _).mp (by simpa using chosen.2)

#print axioms exists_free
#print axioms search_correct

end Project.Beck.ExactFreeColumn
