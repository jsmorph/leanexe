import Project.Beck.Counting

namespace Project.Beck.ProtectedMatrix

open LeanExe.Examples.Beck

def row (input : Input) (x : Point) (category : Nat) : List UInt64 :=
  (List.range input.jobs).map fun job =>
    if !frozen x job then input.incidence[job * input.categories + category]! else 0

def selected (input : Input) (x : Point) : List Nat :=
  (List.range input.categories).filter fun category => input.overlap < liveCount input x category

theorem row_length (input : Input) (x : Point) (category : Nat) :
    (row input x category).length = input.jobs := by simp [row]

theorem protectedMatrix_eq (input : Input) (x : Point) :
    protectedMatrix input x = ((selected input x).flatMap (row input x)).toArray := by
  have appendRow (category : Nat) (acc : Array UInt64) :
      (forIn (List.range input.jobs) acc (fun job acc => pure (ForInStep.yield
        (acc.push (if !frozen x job then input.incidence[job * input.categories + category]! else 0)))) :
        Id (Array UInt64)) = acc ++ (row input x category).toArray := by
    rw [List.forIn_pure_yield_eq_foldl]
    exact List.foldl_push_eq_append
  have collect (categories : List Nat) (acc : Array UInt64) :
      (forIn categories acc (fun category acc => ForInStep.yield
        (if input.overlap < liveCount input x category
         then acc ++ (row input x category).toArray else acc)) : Id (Array UInt64)) =
        acc ++ ((categories.filter fun category => input.overlap < liveCount input x category).flatMap
          (row input x)).toArray := by
    induction categories generalizing acc with
    | nil => simp [pure]
    | cons category categories ih =>
      rw [List.forIn_cons]
      by_cases h : input.overlap < liveCount input x category
      · simp [h, bind, ih, Array.append_assoc]
      · simp [h, bind, ih]
  simp only [protectedMatrix, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', appendRow]
  simp only [Id.run, bind, pure, ← apply_ite ForInStep.yield]
  rw [collect]
  simp [selected]

theorem selected_length (input : Input) (x : Point) :
    (selected input x).length = (Counting.protectedRows input x).card := by
  have hn : (selected input x).Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hn]
  simp only [selected, List.toFinset_filter, List.toFinset_range,
    Counting.protectedRows, Finset.card_filter]
  rw [Finset.sum_range]
  simp only [decide_eq_true_eq]

theorem flatten_length (input : Input) (x : Point) (categories : List Nat) :
    (categories.flatMap (row input x)).length = categories.length * input.jobs := by
  induction categories with
  | nil => simp
  | cons category categories ih => simp [row_length, ih, Nat.add_mul, Nat.add_comm]

theorem protectedMatrix_size (input : Input) (x : Point) :
    (protectedMatrix input x).size = (Counting.protectedRows input x).card * input.jobs := by
  rw [protectedMatrix_eq, List.size_toArray, flatten_length, selected_length]

theorem flatten_get (input : Input) (x : Point) (categories : List Nat)
    (i j : Nat) (hi : i < categories.length) (hj : j < input.jobs) :
    (categories.flatMap (row input x))[i * input.jobs + j]! =
      if !frozen x j then input.incidence[j * input.categories + categories[i]]! else 0 := by
  induction categories generalizing i with
  | nil => simp at hi
  | cons category categories ih =>
    cases i with
    | zero =>
      have hrow : j < (row input x category).length := by simpa [row_length] using hj
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [getElem!_pos _ _ (by simp only [List.length_append]; omega),
        List.getElem_append_left hrow]
      simp [row]
    | succ i =>
      have hi' : i < categories.length := by simpa using hi
      have htail : i * input.jobs + j < (categories.flatMap (row input x)).length := by
        rw [flatten_length]
        exact (Nat.add_lt_add_left hj _).trans_le (by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right input.jobs hi')
      have hindex : (i + 1) * input.jobs + j =
          (row input x category).length + (i * input.jobs + j) := by
        rw [row_length, Nat.add_mul]
        omega
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [hindex, getElem!_pos _ _ (by simp only [List.length_append]; omega),
        List.getElem_append_right (by omega)]
      have result := ih i hi'
      rw [getElem!_pos (categories.flatMap (row input x)) (i * input.jobs + j) htail] at result
      simpa only [Nat.add_sub_cancel_left] using result

theorem protectedMatrix_get (input : Input) (x : Point) (i j : Nat)
    (hi : i < (selected input x).length) (hj : j < input.jobs) :
    (protectedMatrix input x)[i * input.jobs + j]! =
      if !frozen x j then input.incidence[j * input.categories + (selected input x)[i]]! else 0 := by
  rw [protectedMatrix_eq]
  simpa using flatten_get input x (selected input x) i j hi hj

theorem frozen_column_zero (input : Input) (x : Point) (i j : Nat)
    (hi : i < (selected input x).length) (hj : j < input.jobs) (hf : frozen x j = true) :
    (protectedMatrix input x)[i * input.jobs + j]! = 0 := by
  simp [protectedMatrix_get input x i j hi hj, hf]

theorem protectedMatrix_binary (input : Input) (x : Point)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (i j : Nat) (hi : i < (selected input x).length) (hj : j < input.jobs) :
    (protectedMatrix input x)[i * input.jobs + j]! = 0 ∨
      (protectedMatrix input x)[i * input.jobs + j]! = 1 := by
  rw [protectedMatrix_get input x i j hi hj]
  split
  · apply binary j hj
    have member : (selected input x)[i] ∈ selected input x := List.getElem_mem hi
    exact List.mem_range.mp (List.mem_filter.mp member).1
  · exact Or.inl rfl

theorem protectedMatrix_short (input : Input) (x : Point)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ Counting.members input category).card ≤ input.overlap)
    (nonempty : (Counting.live input x).Nonempty) :
    (protectedMatrix input x).size / input.jobs < input.jobs := by
  have positive : 0 < input.jobs := by
    obtain ⟨job, _⟩ := nonempty
    exact (Nat.zero_le job.val).trans_lt job.isLt
  rw [protectedMatrix_size, Nat.mul_div_cancel _ positive]
  have liveBound : (Counting.live input x).card ≤ input.jobs :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  exact (Counting.protected_fewer input x overlap nonempty).trans_le liveBound

theorem source_basis_complete (input : Input) (x : Point)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ Counting.members input category).card ≤ input.overlap)
    (nonempty : (Counting.live input x).Nonempty) :
    let matrix := protectedMatrix input x
    let basis := findBasis input.jobs input.jobs matrix ⟨#[], #[], 1⟩
    Basis.WellFormed input.jobs matrix basis ∧ Basis.extension input.jobs matrix basis = none ∧
      basis.rows.size < input.jobs := by
  exact Basis.findBasis_fuel_sufficient input.jobs _ (protectedMatrix_short input x overlap nonempty)

end Project.Beck.ProtectedMatrix
