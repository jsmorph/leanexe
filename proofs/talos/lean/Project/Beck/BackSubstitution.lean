import Project.Beck.Elimination

namespace Project.Beck.BackSubstitution

open LeanExe.Examples.BeckExact IntegerAdd Elimination

def addProduct (width row : ℕ) (matrix vector : Array Integer) (job : ℕ) (total : Integer) :
    Integer := Integer.add total (Integer.mul matrix[row * width + job]! vector[job]!)

theorem sum_correct (items : List ℕ) (width row : ℕ) (matrix vector : Array Integer)
    (total : Integer) (initialValid : Valid total)
    (entriesValid : ∀ job ∈ items, Valid matrix[row * width + job]! ∧ Valid vector[job]!) :
    let result := items.foldl (fun total job => addProduct width row matrix vector job total) total
    Valid result ∧ value result = value total +
      (items.map (fun job => value matrix[row * width + job]! * value vector[job]!)).sum := by
  induction items generalizing total with
  | nil => simpa using initialValid
  | cons job tail ih =>
    have entries := entriesValid job (by simp)
    have product := IntegerMul.mul_correct _ _ entries.1 entries.2
    have added := IntegerAdd.add_correct _ _ initialValid product.1
    have rest := ih (addProduct width row matrix vector job total) added.1
      (by intro j member; exact entriesValid j (by simp [member]))
    refine ⟨rest.1, ?_⟩
    change value (tail.foldl _ _) = _
    rw [rest.2]
    simp only [addProduct, added.2, product.2, List.map_cons, List.sum_cons]
    ring

def step (width row column : ℕ) (matrix vector : Array Integer) : Option (Array Integer) := do
  let total ← forIn (List.range' (column + 1) (width - (column + 1))) Integer.zero
    (fun job total => pure (.yield (addProduct width row matrix vector job total)))
  let quotient ← Integer.divideExact (Integer.neg total) matrix[row * width + column]!
  return vector.set! column quotient

theorem step_correct (width row column : ℕ) (matrix vector : Array Integer)
    (columnBound : column < width) (vectorSize : vector.size = width)
    (matrixValid : ∀ col, col < width → Valid matrix[row * width + col]!)
    (vectorValid : ∀ entry ∈ vector, Valid entry)
    (pivotNonzero : value matrix[row * width + column]! ≠ 0)
    (answer : ℤ)
    (equation : value matrix[row * width + column]! * answer +
      ((List.range' (column + 1) (width - (column + 1))).map
        (fun job => value matrix[row * width + job]! * value vector[job]!)).sum = 0) :
    ∃ result, step width row column matrix vector = some result ∧
      (∀ entry ∈ result, Valid entry) ∧ result.size = width ∧
      value result[column]! = answer ∧
      ∀ job, job ≠ column → result[job]! = vector[job]! := by
  let items := List.range' (column + 1) (width - (column + 1))
  let total := items.foldl (fun total job => addProduct width row matrix vector job total) Integer.zero
  have totalSpec := sum_correct items width row matrix vector Integer.zero zero_correct.1 (by
    intro job member
    have bounds := List.mem_range'_1.mp member
    have inside : job < width := by omega
    exact ⟨matrixValid job inside, get_valid vector vectorValid job (by omega)⟩)
  have totalValue : value total = (items.map
      (fun job => value matrix[row * width + job]! * value vector[job]!)).sum := by
    simpa only [zero_correct.2, zero_add] using totalSpec.2
  have negated := neg_correct total totalSpec.1
  have numerator : value (Integer.neg total) = value matrix[row * width + column]! * answer := by
    rw [negated.2, totalValue]
    linarith
  obtain ⟨quotient, division, quotientValid, quotientEquation, _⟩ := IntegerDiv.divideExact_correct
    (Integer.neg total) matrix[row * width + column]! negated.1 (matrixValid column columnBound)
    pivotNonzero ⟨answer, numerator⟩
  have quotientValue : value quotient = answer := by
    rw [numerator] at quotientEquation
    exact mul_right_cancel₀ pivotNonzero (by simpa [mul_comm] using quotientEquation)
  have loop : forIn items Integer.zero
      (fun job total => pure (.yield (addProduct width row matrix vector job total))) =
      (some total : Option Integer) := List.forIn_pure_yield_eq_foldl _ _
  refine ⟨vector.set! column quotient, ?_, ?_, by simp [vectorSize], ?_, ?_⟩
  · rw [step, loop]
    dsimp only [bind, Option.bind]
    change (Integer.divideExact (Integer.neg total) matrix[row * width + column]! >>= _) = _
    rw [division]
    rfl
  · intro entry member
    rcases Array.mem_or_eq_of_mem_setIfInBounds member with old | equal
    · exact vectorValid entry old
    · simpa [equal] using quotientValid
  · rw [Array.getElem!_set!_self _ _ _ (by omega), quotientValue]
  · intro job distinct
    exact Array.getElem!_set!_ne _ _ _ _ (Ne.symm distinct)

#print axioms step_correct

end Project.Beck.BackSubstitution
