import Project.Beck.Elimination
import Project.Beck.EchelonShape

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

theorem split_sum (width column : ℕ) (f : ℕ → ℤ) (inside : column < width)
    (zero : ∀ col, col < column → f col = 0) :
    ((List.range width).map f).sum = f column +
      ((List.range' (column + 1) (width - (column + 1))).map f).sum := by
  have range : List.range width = List.range column ++ [column] ++
      List.range' (column + 1) (width - (column + 1)) := by
    rw [← List.range_succ, List.range_eq_range', List.range_eq_range']
    have joined := List.range'_append_1 (s := 0) (m := column + 1)
      (n := width - (column + 1))
    simpa only [Nat.zero_add, Nat.add_sub_of_le (by omega : column + 1 ≤ width)] using joined.symm
  have prefixZero : ((List.range column).map f).sum = 0 := by
    apply List.sum_eq_zero
    intro z member
    obtain ⟨col, inRange, rfl⟩ := List.mem_map.mp member
    exact zero col (List.mem_range.mp inRange)
  rw [range, List.map_append, List.sum_append, List.map_append, List.sum_append, prefixZero]
  simp

def backwardBody (width : ℕ) (matrix : Array Integer) (columns : Array UInt64)
    (offset : ℕ) (vector : Array Integer) : Option (ForInStep (Array Integer)) := do
  let row := columns.size - 1 - offset
  return .yield (← step width row columns[row]!.toNat matrix vector)

def Agrees (width remaining : ℕ) (columns : Array UInt64)
    (answer : ℕ → ℤ) (vector : Array Integer) : Prop :=
  ∀ job, job < width → (∀ row, row < remaining → columns[row]!.toNat ≠ job) →
    value vector[job]! = answer job

theorem backward_step (width offset : ℕ) (matrix vector : Array Integer) (columns : Array UInt64)
    (answer : ℕ → ℤ)
    (shape : EchelonShape.Pivots columns.size width
      (fun row col => value matrix[row * width + col]!) (columns.toList.map UInt64.toNat))
    (matrixValid : ∀ row, row < columns.size → ∀ col, col < width → Valid matrix[row * width + col]!)
    (vectorValid : ∀ entry ∈ vector, Valid entry) (vectorSize : vector.size = width)
    (equations : ∀ row, row < columns.size →
      ((List.range width).map (fun col => value matrix[row * width + col]! * answer col)).sum = 0)
    (offsetBound : offset < columns.size)
    (agrees : Agrees width (columns.size - offset) columns answer vector) :
    ∃ result, backwardBody width matrix columns offset vector = some (.yield result) ∧
      (∀ entry ∈ result, Valid entry) ∧ result.size = width ∧
      Agrees width (columns.size - (offset + 1)) columns answer result := by
  let row := columns.size - 1 - offset
  let column := columns[row]!.toNat
  have rowBound : row < columns.size := by dsimp [row]; omega
  have columnGet (r : ℕ) (inside : r < columns.size) :
      (columns.toList.map UInt64.toNat)[r]! = columns[r]!.toNat := by
    rw [getElem!_pos (columns.toList.map UInt64.toNat) r (by simpa using inside),
      List.getElem_map, Array.getElem_toList, getElem!_pos columns r inside]
  have columnBound : column < width := by simpa only [columnGet row rowBound] using shape.before row rowBound
  have pivotNonzero : value matrix[row * width + column]! ≠ 0 := by
    simpa only [columnGet row rowBound] using shape.nonzero row rowBound
  have order (earlier : ℕ) (before : earlier < row) : columns[earlier]!.toNat < column := by
    simpa only [columnGet row rowBound, columnGet earlier (by omega)] using
      shape.ordered earlier row before rowBound
  have later (job : ℕ) (afterColumn : column < job) (inside : job < width) :
      value vector[job]! = answer job := by
    apply agrees job inside
    intro r remaining
    have before : r ≤ row := by dsimp [row]; omega
    rcases Nat.lt_or_eq_of_le before with before | rfl
    · have := order r before
      omega
    · exact Nat.ne_of_lt afterColumn
  have equation : value matrix[row * width + column]! * answer column +
      ((List.range' (column + 1) (width - (column + 1))).map
        (fun job => value matrix[row * width + job]! * value vector[job]!)).sum = 0 := by
    have split := split_sum width column
      (fun job => value matrix[row * width + job]! * answer job) columnBound (by
        intro job before
        have zero := shape.leadingZero row rowBound job (by simpa only [columnGet row rowBound] using before)
        rw [zero, zero_mul])
    have equation := equations row rowBound
    rw [split] at equation
    convert equation using 2
    congr 1
    apply List.map_congr_left
    intro job member
    have bounds := List.mem_range'_1.mp member
    rw [later job (by omega) (by omega)]
  obtain ⟨result, source, valid, size, recovered, untouched⟩ := step_correct width row column matrix vector
    columnBound vectorSize (matrixValid row rowBound) vectorValid pivotNonzero (answer column) equation
  refine ⟨result, ?_, valid, size, ?_⟩
  · rw [backwardBody]
    change (step width row column matrix vector >>= _) = _
    rw [source]
    rfl
  · intro job inside absent
    by_cases same : job = column
    · simpa only [same] using recovered
    · rw [untouched job same]
      apply agrees job inside
      intro r remaining
      by_cases before : r < columns.size - (offset + 1)
      · exact absent r before
      · have equal : r = row := by dsimp [row]; omega
        subst r
        exact Ne.symm same

#print axioms backward_step

theorem backward_loop (width count offset : ℕ) (matrix vector : Array Integer) (columns : Array UInt64)
    (answer : ℕ → ℤ)
    (shape : EchelonShape.Pivots columns.size width
      (fun row col => value matrix[row * width + col]!) (columns.toList.map UInt64.toNat))
    (matrixValid : ∀ row, row < columns.size → ∀ col, col < width → Valid matrix[row * width + col]!)
    (vectorValid : ∀ entry ∈ vector, Valid entry) (vectorSize : vector.size = width)
    (equations : ∀ row, row < columns.size →
      ((List.range width).map (fun col => value matrix[row * width + col]! * answer col)).sum = 0)
    (bound : offset + count ≤ columns.size)
    (agrees : Agrees width (columns.size - offset) columns answer vector) :
    ∃ result, forIn (List.range' offset count) vector (backwardBody width matrix columns) = some result ∧
      (∀ entry ∈ result, Valid entry) ∧ result.size = width ∧
      Agrees width (columns.size - (offset + count)) columns answer result := by
  induction count generalizing offset vector with
  | zero => exact ⟨vector, rfl, vectorValid, vectorSize, agrees⟩
  | succ count ih =>
    obtain ⟨middle, step, middleValid, middleSize, middleAgrees⟩ := backward_step width offset
      matrix vector columns answer shape matrixValid vectorValid vectorSize equations (by omega) agrees
    obtain ⟨result, rest, resultValid, resultSize, resultAgrees⟩ := ih (offset + 1) middle
      middleValid middleSize (by omega) middleAgrees
    refine ⟨result, ?_, resultValid, resultSize, ?_⟩
    · simpa only [List.range'_succ, List.forIn_cons, step, bind, pure, Option.bind] using rest
    · convert resultAgrees using 1 <;> omega

#print axioms backward_loop

end Project.Beck.BackSubstitution
