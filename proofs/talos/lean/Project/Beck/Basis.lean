import Project.Beck.Determinant

namespace Project.Beck.Basis

open LeanExe.Examples.Beck

abbrev searchStep {α β : Type} (f : α → Option β) (a : α) (_ : Option β × Unit) :
    Id (ForInStep (Option β × Unit)) :=
  Option.rec (.yield (none, ())) (fun b => .done (some b, ())) (f a)

theorem forIn_search {α β : Type} (xs : List α) (f : α → Option β) :
    forIn xs (none, ()) (searchStep f) = (xs.findSome? f, ()) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.forIn_cons]
    cases h : f a <;> simp [searchStep, h, bind, pure, ih]

theorem contains_eq (xs : Array UInt64) (value : UInt64) :
    contains xs value = ((List.range xs.size).findSome?
      (fun i => if xs[i]! == value then some true else none)).getD false := by
  let f := fun (i : Nat) => if xs[i]! == value then some true else none
  have step (i : Nat) :
      (if xs[i]! == value then pure (ForInStep.done (some true, ()))
       else pure (ForInStep.yield (none, ()))) = searchStep f i (none, ()) := by
    dsimp [searchStep, f]
    split <;> rfl
  simp only [contains, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp_rw [step]
  change ((forIn (List.range xs.size) (none, ()) (searchStep f)).run).1.getD false = _
  rw [forIn_search]
  rfl

theorem contains_false_iff (xs : Array UInt64) (value : UInt64) :
    contains xs value = false ↔ ∀ i < xs.size, xs[i]! ≠ value := by
  rw [contains_eq]
  cases h : (List.range xs.size).findSome?
      (fun i => if xs[i]! == value then some true else none) with
  | none =>
    have all := List.findSome?_eq_none_iff.mp h
    simpa using all
  | some result =>
    obtain ⟨i, hi, found⟩ := List.exists_of_findSome?_eq_some h
    have hi := List.mem_range.mp hi
    split at found
    · cases found
      simp_all
      exact ⟨i, hi, by assumption⟩
    · contradiction

theorem contains_false_iff_not_mem (xs : Array UInt64) (value : UInt64) :
    contains xs value = false ↔ value ∉ xs := by
  simp only [contains_false_iff, Array.mem_iff_getElem, not_exists]
  constructor <;> intro h i hi
  · simpa only [getElem!_pos xs i hi] using h i hi
  · simpa only [getElem!_pos xs i hi] using h i hi

def extension (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis) :
    Option LeanExe.Examples.Beck.Basis :=
  (List.range (matrix.size / width)).findSome? fun row =>
    (List.range width).findSome? (borderCandidate width matrix basis row)

theorem extend_eq (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis) :
    extend width matrix basis = (extension width matrix basis).getD basis := by
  simp only [extend, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  unfold LeanExe.Examples.Beck.extend.match_1 Break.runK.match_1
  simp only [bind, pure, Id.run]
  have search (xs : List Nat) (f : Nat → Option LeanExe.Examples.Beck.Basis) :
      (forIn xs (none, ()) (fun a (_ : Option LeanExe.Examples.Beck.Basis × Unit) =>
        Option.rec (ForInStep.yield (none, ())) (fun b => ForInStep.done (some b, ()))
          (f a)) : Id (Option LeanExe.Examples.Beck.Basis × Unit)) =
        (xs.findSome? f, ()) := forIn_search xs f
  simp only [search]
  change Option.rec (motive := fun _ => LeanExe.Examples.Beck.Basis)
    basis (fun b => b) (extension width matrix basis) = _
  cases extension width matrix basis <;> rfl

theorem extension_none (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis) :
    extension width matrix basis = none ↔
      ∀ row < matrix.size / width, ∀ col < width,
        borderCandidate width matrix basis row col = none := by
  simp [extension, List.findSome?_eq_none_iff]

theorem extension_some (width : Nat) (matrix : Array UInt64)
    (basis next : LeanExe.Examples.Beck.Basis) (h : extension width matrix basis = some next) :
    ∃ row < matrix.size / width, ∃ col < width,
      borderCandidate width matrix basis row col = some next := by
  obtain ⟨row, hr, hc⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨col, hc, result⟩ := List.exists_of_findSome?_eq_some hc
  exact ⟨row, List.mem_range.mp hr, col, List.mem_range.mp hc, result⟩

theorem candidate_grows (width : Nat) (matrix : Array UInt64)
    (basis next : LeanExe.Examples.Beck.Basis) (row col : Nat)
    (h : borderCandidate width matrix basis row col = some next) :
    next.rows = basis.rows.push row.toUInt64 ∧
      next.columns = basis.columns.push col.toUInt64 ∧ next.determinant ≠ 0 := by
  unfold borderCandidate at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · contradiction
    · cases h
      simp_all

theorem extend_stable_iff (width : Nat) (matrix : Array UInt64)
    (basis : LeanExe.Examples.Beck.Basis) :
    (extend width matrix basis).rows.size = basis.rows.size ↔
      extension width matrix basis = none := by
  rw [extend_eq]
  cases he : extension width matrix basis with
  | none => simp
  | some next =>
    obtain ⟨row, _, col, _, candidate⟩ := extension_some width matrix basis next he
    have grows := (candidate_grows width matrix basis next row col candidate).1
    simp [grows]

theorem extend_grows (width : Nat) (matrix : Array UInt64)
    (basis : LeanExe.Examples.Beck.Basis) (h : extension width matrix basis ≠ none) :
    (extend width matrix basis).rows.size = basis.rows.size + 1 := by
  rw [extend_eq]
  cases he : extension width matrix basis with
  | none => exact False.elim (h he)
  | some next =>
    obtain ⟨row, _, col, _, candidate⟩ := extension_some width matrix basis next he
    simp [(candidate_grows width matrix basis next row col candidate).1]

theorem findBasis_stops_or_grows (fuel width : Nat) (matrix : Array UInt64)
    (basis : LeanExe.Examples.Beck.Basis) :
    extension width matrix (findBasis fuel width matrix basis) = none ∨
      basis.rows.size + fuel ≤ (findBasis fuel width matrix basis).rows.size := by
  induction fuel generalizing basis with
  | zero => right; simp [findBasis]
  | succ fuel ih =>
    simp only [findBasis]
    split
    · left
      apply (extend_stable_iff width matrix basis).mp
      simpa using ‹((extend width matrix basis).rows.size == basis.rows.size) = true›
    · have hn : extension width matrix basis ≠ none := by
        intro h
        have := (extend_stable_iff width matrix basis).mpr h
        simp_all
      rcases ih (extend width matrix basis) with stopped | grown
      · exact Or.inl stopped
      · right
        have step := extend_grows width matrix basis hn
        omega

structure Indices (upper : Nat) (xs : Array UInt64) : Prop where
  nodup : xs.toList.Nodup
  bound : ∀ value ∈ xs, value.toNat < upper

theorem indices_size {upper : Nat} {xs : Array UInt64} (h : Indices upper xs) :
    xs.size ≤ upper := by
  have hn : (xs.toList.map UInt64.toNat).Nodup :=
    h.nodup.map (fun _ _ e => UInt64.toNat_inj.mp e)
  have subset : (xs.toList.map UInt64.toNat).toFinset ⊆ Finset.range upper := by
    intro i hi
    obtain ⟨word, hw, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    exact Finset.mem_range.mpr (h.bound word (Array.mem_toList_iff.mp hw))
  have hc := Finset.card_le_card subset
  simpa [List.toFinset_card_of_nodup hn] using hc

theorem indices_push {upper : Nat} {xs : Array UInt64} (h : Indices upper xs)
    (word : UInt64) (bound : word.toNat < upper) (fresh : word ∉ xs) :
    Indices upper (xs.push word) := by
  constructor
  · simp only [Array.toList_push, List.nodup_append, List.nodup_singleton,
      List.mem_singleton]
    refine ⟨h.nodup, trivial, ?_⟩
    intro a ha b hb
    subst b
    intro equality
    subst a
    exact fresh (Array.mem_toList_iff.mp ha)
  · intro value member
    rcases Array.mem_push.mp member with old | rfl
    · exact h.bound value old
    · exact bound

structure WellFormed (width : Nat) (matrix : Array UInt64)
    (basis : LeanExe.Examples.Beck.Basis) : Prop where
  rows : Indices (matrix.size / width) basis.rows
  columns : Indices width basis.columns
  square : basis.rows.size = basis.columns.size
  value : basis.determinant = determinant basis.rows.size width matrix basis.rows basis.columns
  nonzero : basis.determinant ≠ 0

theorem candidate_wellFormed (width : Nat) (matrix : Array UInt64)
    (basis next : LeanExe.Examples.Beck.Basis) (row col : Nat)
    (h : WellFormed width matrix basis)
    (hr : row < matrix.size / width) (hc : col < width)
    (candidate : borderCandidate width matrix basis row col = some next) :
    WellFormed width matrix next := by
  unfold borderCandidate at candidate
  split at candidate
  · contradiction
  · rename_i fresh
    have freshRows : row.toUInt64 ∉ basis.rows := by
      apply (contains_false_iff_not_mem _ _).mp
      simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr fresh)).1
    have freshColumns : col.toUInt64 ∉ basis.columns := by
      apply (contains_false_iff_not_mem _ _).mp
      simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr fresh)).2
    dsimp only at candidate
    split at candidate
    · contradiction
    · rename_i nonzero
      cases candidate
      refine ⟨indices_push h.rows _ ?_ freshRows, indices_push h.columns _ ?_ freshColumns,
        ?_, rfl, ?_⟩
      · change row % 18446744073709551616 < matrix.size / width
        exact (Nat.mod_le _ _).trans_lt hr
      · change col % 18446744073709551616 < width
        exact (Nat.mod_le _ _).trans_lt hc
      · simpa using h.square
      · simpa using nonzero

theorem extend_wellFormed (width : Nat) (matrix : Array UInt64)
    (basis : LeanExe.Examples.Beck.Basis) (h : WellFormed width matrix basis)
    :
    WellFormed width matrix (extend width matrix basis) := by
  rw [extend_eq]
  cases he : extension width matrix basis with
  | none => exact h
  | some next =>
    obtain ⟨row, hr, col, hc, candidate⟩ := extension_some width matrix basis next he
    exact candidate_wellFormed width matrix basis next row col h hr hc candidate

theorem findBasis_wellFormed (fuel width : Nat) (matrix : Array UInt64)
    (basis : LeanExe.Examples.Beck.Basis) (h : WellFormed width matrix basis)
    :
    WellFormed width matrix (findBasis fuel width matrix basis) := by
  induction fuel generalizing basis with
  | zero => exact h
  | succ fuel ih =>
    simp only [findBasis]
    split
    · exact h
    · exact ih _ (extend_wellFormed width matrix basis h)

theorem findBasis_maximal (fuel width : Nat) (matrix : Array UInt64)
    (basis : LeanExe.Examples.Beck.Basis) (h : WellFormed width matrix basis)
    (fuelEnough : matrix.size / width < basis.rows.size + fuel) :
    extension width matrix (findBasis fuel width matrix basis) = none := by
  rcases findBasis_stops_or_grows fuel width matrix basis with stopped | grown
  · exact stopped
  · have bound := indices_size
      (findBasis_wellFormed fuel width matrix basis h).rows
    omega

theorem empty_wellFormed (width : Nat) (matrix : Array UInt64) :
    WellFormed width matrix ⟨#[], #[], 1⟩ := by
  refine ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩, rfl, rfl, ?_⟩
  decide

theorem findBasis_fuel_sufficient (width : Nat) (matrix : Array UInt64)
    (short : matrix.size / width < width) :
    let basis := findBasis width width matrix ⟨#[], #[], 1⟩
    WellFormed width matrix basis ∧ extension width matrix basis = none ∧
      basis.rows.size < width := by
  dsimp only
  have wellFormed := findBasis_wellFormed width width matrix _ (empty_wellFormed width matrix)
  refine ⟨wellFormed,
    findBasis_maximal width width matrix _ (empty_wellFormed width matrix) (by simpa using short),
    (indices_size wellFormed.rows).trans_lt short⟩

theorem maximal_border_zero (width : Nat) (matrix : Array UInt64)
    (basis : LeanExe.Examples.Beck.Basis) (row col : Nat)
    (maximal : extension width matrix basis = none)
    (hr : row < matrix.size / width) (hc : col < width)
    (freshRow : row.toUInt64 ∉ basis.rows) (freshColumn : col.toUInt64 ∉ basis.columns) :
    determinant (basis.rows.size + 1) width matrix
      (basis.rows.push row.toUInt64) (basis.columns.push col.toUInt64) = 0 := by
  have absent := (extension_none width matrix basis).mp maximal row hr col hc
  have hrow := (contains_false_iff_not_mem _ _).mpr freshRow
  have hcol := (contains_false_iff_not_mem _ _).mpr freshColumn
  simpa [borderCandidate, hrow, hcol] using absent

end Project.Beck.Basis
