import Project.Beck.ExactCounting
import Project.Beck.IntegerOrder

namespace Project.Beck.ExactMatrix

open LeanExe.Examples.BeckExact IntegerAdd
open LeanExe.Examples.Beck (Input)

def entry (input : Input) (point : Point) (category job : ℕ) : Integer :=
  if frozen point job then Integer.zero
  else Integer.ofWord input.incidence[job * input.categories + category]!

def row (input : Input) (point : Point) (category : ℕ) : List Integer :=
  (List.range input.jobs).map (entry input point category)

def selected (input : Input) (point : Point) : List ℕ :=
  (List.range input.categories).filter fun category => input.overlap < liveCount input point category

theorem row_length (input : Input) (point : Point) (category : ℕ) :
    (row input point category).length = input.jobs := by simp [row]

theorem source_eq (input : Input) (point : Point) :
    protectedMatrix input point = ((selected input point).flatMap (row input point)).toArray := by
  have appendRow (category : ℕ) (acc : Array Integer) :
      (forIn (List.range input.jobs) acc (fun job acc => pure (ForInStep.yield
        (acc.push (entry input point category job)))) : Id (Array Integer)) =
        acc ++ (row input point category).toArray := by
    rw [List.forIn_pure_yield_eq_foldl]
    exact List.foldl_push_eq_append
  have collect (categories : List ℕ) (acc : Array Integer) :
      (forIn categories acc (fun category acc => ForInStep.yield
        (if input.overlap < liveCount input point category
         then acc ++ (row input point category).toArray else acc)) : Id (Array Integer)) =
        acc ++ ((categories.filter fun category => input.overlap < liveCount input point category).flatMap
          (row input point)).toArray := by
    induction categories generalizing acc with
    | nil => simp [pure]
    | cons category categories ih =>
      rw [List.forIn_cons]
      by_cases kept : input.overlap < liveCount input point category
      · simp [kept, bind, ih, Array.append_assoc]
      · simp [kept, bind, ih]
  simp only [protectedMatrix, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  change (forIn (List.range input.categories) #[] (fun category acc =>
    if input.overlap < liveCount input point category then
      forIn (List.range input.jobs) acc
        (fun job acc => pure (.yield (acc.push (entry input point category job)))) >>=
          (fun result => pure (.yield result))
    else pure (.yield acc)) : Id (Array Integer)) = _
  simp_rw [appendRow]
  simp only [bind, pure, ← apply_ite ForInStep.yield]
  rw [collect]
  simp [selected]

theorem selected_length (input : Input) (point : Point) :
    (selected input point).length = (ExactCounting.protectedRows input point).card := by
  have nodup : (selected input point).Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup nodup]
  simp only [selected, List.toFinset_filter, List.toFinset_range,
    ExactCounting.protectedRows, Finset.card_filter]
  rw [Finset.sum_range]
  simp only [decide_eq_true_eq]

theorem flatten_length (input : Input) (point : Point) (categories : List ℕ) :
    (categories.flatMap (row input point)).length = categories.length * input.jobs := by
  induction categories with
  | nil => simp
  | cons category categories ih => simp [row_length, ih, Nat.add_mul, Nat.add_comm]

theorem size_eq (input : Input) (point : Point) :
    (protectedMatrix input point).size = (ExactCounting.protectedRows input point).card * input.jobs := by
  rw [source_eq, List.size_toArray, flatten_length, selected_length]

theorem flatten_get (input : Input) (point : Point) (categories : List ℕ)
    (i j : ℕ) (hi : i < categories.length) (hj : j < input.jobs) :
    (categories.flatMap (row input point))[i * input.jobs + j]! =
      entry input point categories[i] j := by
  induction categories generalizing i with
  | nil => simp at hi
  | cons category categories ih =>
    cases i with
    | zero =>
      have rowBound : j < (row input point category).length := by simpa [row_length] using hj
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [getElem!_pos _ _ (by simp only [List.length_append]; omega),
        List.getElem_append_left rowBound]
      simp [row]
    | succ i =>
      have nextBound : i < categories.length := by simpa using hi
      have tailBound : i * input.jobs + j < (categories.flatMap (row input point)).length := by
        rw [flatten_length]
        nlinarith
      have index : (i + 1) * input.jobs + j =
          (row input point category).length + (i * input.jobs + j) := by
        rw [row_length]
        ring
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [index, getElem!_pos _ _ (by simp only [List.length_append]; omega),
        List.getElem_append_right (by omega)]
      have result := ih i nextBound
      rw [getElem!_pos (categories.flatMap (row input point)) (i * input.jobs + j) tailBound] at result
      simpa only [Nat.add_sub_cancel_left] using result

theorem get_eq (input : Input) (point : Point) (i j : ℕ)
    (hi : i < (selected input point).length) (hj : j < input.jobs) :
    (protectedMatrix input point)[i * input.jobs + j]! =
      entry input point (selected input point)[i] j := by
  rw [source_eq]
  simpa using flatten_get input point (selected input point) i j hi hj

theorem valid (input : Input) (point : Point) :
    ∀ item ∈ protectedMatrix input point, Valid item := by
  intro item member
  rw [source_eq, List.mem_toArray] at member
  obtain ⟨category, _, inRow⟩ := List.mem_flatMap.mp member
  obtain ⟨job, _, rfl⟩ := List.mem_map.mp inRow
  unfold entry
  split
  · exact zero_correct.1
  · exact (IntegerOrder.ofWord_correct _).1

theorem frozen_zero (input : Input) (point : Point) (i j : ℕ)
    (hi : i < (ExactCounting.protectedRows input point).card) (hj : j < input.jobs)
    (fixed : frozen point j = true) :
    value (protectedMatrix input point)[i * input.jobs + j]! = 0 := by
  rw [get_eq input point i j (by rwa [selected_length]) hj]
  simp only [entry, fixed, ite_true, zero_correct.2]

#print axioms source_eq
#print axioms get_eq
#print axioms valid

end Project.Beck.ExactMatrix
