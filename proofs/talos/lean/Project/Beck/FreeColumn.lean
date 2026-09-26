import Project.Beck.ProtectedMatrix

namespace Project.Beck.FreeColumn

open LeanExe.Examples.Beck

def candidate (x : Point) (columns : Array UInt64) (col : Nat) : Option Nat :=
  if !frozen x col && !contains columns col.toUInt64 then some col else none

theorem freeColumn_eq (input : Input) (x : Point) (columns : Array UInt64) :
    freeColumn input x columns =
      ((List.range input.jobs).findSome? (candidate x columns)).getD input.jobs := by
  have step (col : Nat) :
      (if !frozen x col && !contains columns col.toUInt64
       then pure (ForInStep.done (some col, ()))
       else pure (ForInStep.yield (none, ()))) =
      Basis.searchStep (candidate x columns) col (none, ()) := by
    dsimp [Basis.searchStep, candidate]
    split <;> rfl
  simp only [freeColumn, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp_rw [step]
  change ((forIn (List.range input.jobs) (none, ())
    (Basis.searchStep (candidate x columns))).run).1.getD input.jobs = _
  rw [Basis.forIn_search]
  rfl

theorem exists_free (input : Input) (x : Point) (columns : Array UInt64)
    (capacity : input.jobs ≤ 6) (small : columns.size < (Counting.live input x).card) :
    ∃ col < input.jobs, frozen x col = false ∧ col.toUInt64 ∉ columns := by
  by_contra! absent
  let values := (columns.toList.map UInt64.toNat).toFinset
  have included : (Counting.live input x).image Fin.val ⊆ values := by
    intro col member
    obtain ⟨job, hj, rfl⟩ := Finset.mem_image.mp member
    have hf : frozen x job.val = false := (Finset.mem_filter.mp hj).2
    have hc : job.val.toUInt64 ∈ columns := absent job.val job.isLt hf
    have he : job.val.toUInt64.toNat = job.val := by
      change job.val % 18446744073709551616 = job.val
      apply Nat.mod_eq_of_lt
      omega
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨job.val.toUInt64, Array.mem_toList_iff.mpr hc, he⟩
  have imageSize : ((Counting.live input x).image Fin.val).card =
      (Counting.live input x).card := Finset.card_image_of_injective _ Fin.val_injective
  have upper : values.card ≤ columns.size := by
    exact (List.toFinset_card_le _).trans_eq (by simp)
  have := (Finset.card_le_card included).trans upper
  omega

theorem freeColumn_spec (input : Input) (x : Point) (columns : Array UInt64)
    (available : ∃ col < input.jobs, frozen x col = false ∧ col.toUInt64 ∉ columns) :
    let col := freeColumn input x columns
    col < input.jobs ∧ frozen x col = false ∧ col.toUInt64 ∉ columns := by
  rw [freeColumn_eq]
  cases h : (List.range input.jobs).findSome? (candidate x columns) with
  | none =>
    obtain ⟨col, hc, hf, fresh⟩ := available
    have hz := List.findSome?_eq_none_iff.mp h col (List.mem_range.mpr hc)
    have hcontains := (Basis.contains_false_iff_not_mem columns col.toUInt64).mpr fresh
    simp [candidate, hf, hcontains] at hz
  | some col =>
    obtain ⟨i, hi, found⟩ := List.exists_of_findSome?_eq_some h
    dsimp [candidate] at found
    split at found
    · rename_i eligible
      cases found
      simp only [Bool.and_eq_true] at eligible
      exact ⟨List.mem_range.mp hi, by simpa using eligible.1,
        (Basis.contains_false_iff_not_mem _ _).mp (by simpa using eligible.2)⟩
    · contradiction

theorem source_freeColumn (input : Input) (x : Point)
    (capacity : input.jobs ≤ 6)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ Counting.members input category).card ≤ input.overlap)
    (nonempty : (Counting.live input x).Nonempty) :
    let matrix := protectedMatrix input x
    let basis := findBasis input.jobs input.jobs matrix ⟨#[], #[], 1⟩
    let col := freeColumn input x basis.columns
    col < input.jobs ∧ frozen x col = false ∧ col.toUInt64 ∉ basis.columns := by
  dsimp only
  apply freeColumn_spec
  apply exists_free input x _ capacity
  have wf := (ProtectedMatrix.source_basis_complete input x overlap nonempty).1
  have count := Basis.indices_size wf.rows
  have positive : 0 < input.jobs := by
    obtain ⟨job, _⟩ := nonempty
    exact (Nat.zero_le job.val).trans_lt job.isLt
  rw [ProtectedMatrix.protectedMatrix_size, Nat.mul_div_cancel _ positive] at count
  rw [← wf.square]
  exact count.trans_lt (Counting.protected_fewer input x overlap nonempty)

end Project.Beck.FreeColumn
