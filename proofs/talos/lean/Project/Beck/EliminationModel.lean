import Project.Beck.Elimination

namespace Project.Beck.Elimination

open LeanExe.Examples.BeckExact IntegerAdd

theorem fold_set_size {α : Type*} (items : List α) (position : α → ℕ) (entry : α → ℤ)
    (initial : Array ℤ) :
    (items.foldl (fun result item => result.set! (position item) (entry item)) initial).size =
      initial.size := by
  induction items generalizing initial with
  | nil => rfl
  | cons head tail ih => simpa using ih (initial.set! (position head) (entry head))

theorem fold_set_get {α : Type*} (items : List α) (position : α → ℕ) (entry : α → ℤ)
    (initial : Array ℤ) (query : ℕ) (inside : query < initial.size) (answer : ℤ)
    (same : ∀ item ∈ items, position item = query → entry item = answer) :
    (items.foldl (fun result item => result.set! (position item) (entry item)) initial)[query]! =
      if ∃ item ∈ items, position item = query then answer else initial[query]! := by
  classical
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldl_cons, ih _ (by simpa using inside)
      (by intro item member; exact same item (by simp [member]))]
    by_cases found : ∃ item ∈ tail, position item = query
    · have whole : ∃ item ∈ head :: tail, position item = query := by
        obtain ⟨item, member, equal⟩ := found
        exact ⟨item, by simp [member], equal⟩
      simp only [found, whole, ite_true]
    · by_cases equal : position head = query
      · have whole : ∃ item ∈ head :: tail, position item = query := ⟨head, by simp, equal⟩
        rw [ite_eq_right found, ite_eq_left whole, equal, Array.getElem!_set!_self _ _ _ inside]
        exact same head (by simp) equal
      · have absent : ¬∃ item ∈ head :: tail, position item = query := by
          rintro ⟨item, member, samePosition⟩
          rcases List.mem_cons.mp member with rfl | member
          · exact equal samePosition
          · exact found ⟨item, member, samePosition⟩
        simp only [found, absent, ite_false]
        exact Array.getElem!_set!_ne _ _ _ _ equal

theorem flat_unique (width row otherRow col otherCol : ℕ)
    (hc : col < width) (hd : otherCol < width)
    (equal : row * width + col = otherRow * width + otherCol) :
    row = otherRow ∧ col = otherCol := by
  have rows : row = otherRow := by
    rcases lt_trichotomy row otherRow with smaller | same | larger
    · have scaled := Nat.mul_le_mul_right width (Nat.succ_le_of_lt smaller)
      nlinarith
    · exact same
    · have scaled := Nat.mul_le_mul_right width (Nat.succ_le_of_lt larger)
      nlinarith
  exact ⟨rows, by simpa [rows] using equal⟩

theorem modelRow_size (width rank column row : ℕ) (matrix : Array Integer) (previous : Integer)
    (result : Array ℤ) : (modelRow width rank column matrix previous row result).size = result.size := by
  simp only [modelRow, Array.size_set!, fold_set_size]

theorem modelRow_get (width rank column row queryRow queryCol : ℕ)
    (matrix : Array Integer) (previous : Integer) (initial : Array ℤ)
    (columnBound : column < width) (queryColBound : queryCol < width)
    (inside : queryRow * width + queryCol < initial.size) :
    (modelRow width rank column matrix previous row initial)[queryRow * width + queryCol]! =
      if queryRow = row then
        if column < queryCol then entryValue width rank column row queryCol matrix previous
        else if queryCol = column then 0 else initial[queryRow * width + queryCol]!
      else initial[queryRow * width + queryCol]! := by
  classical
  let columns := List.range' (column + 1) (width - (column + 1))
  let updated := columns.foldl (fun result col => result.set! (row * width + col)
    (entryValue width rank column row col matrix previous)) initial
  have member_iff (col : ℕ) : col ∈ columns ↔ column < col ∧ col < width := by
    simp only [columns, List.mem_range'_1]
    omega
  have found : (∃ col ∈ columns, row * width + col = queryRow * width + queryCol) ↔
      queryRow = row ∧ column < queryCol := by
    constructor
    · rintro ⟨col, member, equal⟩
      have bounds := (member_iff col).mp member
      have unique := flat_unique width row queryRow col queryCol bounds.2 queryColBound equal
      exact ⟨unique.1.symm, unique.2 ▸ bounds.1⟩
    · rintro ⟨rfl, later⟩
      exact ⟨queryCol, (member_iff _).mpr ⟨later, queryColBound⟩, rfl⟩
  have updatedGet := fold_set_get columns (fun col => row * width + col)
    (fun col => entryValue width rank column row col matrix previous) initial
    (queryRow * width + queryCol) inside (entryValue width rank column row queryCol matrix previous)
    (by
      intro col member equal
      have unique := flat_unique width row queryRow col queryCol
        ((member_iff col).mp member).2 queryColBound equal
      rw [unique.2])
  simp only [found] at updatedGet
  change updated[queryRow * width + queryCol]! = _ at updatedGet
  have updatedSize : updated.size = initial.size := fold_set_size _ _ _ _
  change (updated.set! (row * width + column) 0)[queryRow * width + queryCol]! = _
  by_cases equal : queryRow * width + queryCol = row * width + column
  · have unique := flat_unique width queryRow row queryCol column queryColBound columnBound equal
    rw [unique.1, unique.2, Array.getElem!_set!_self]
    · simp
    · rw [updatedSize, ← equal]
      exact inside
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm equal), updatedGet]
    by_cases sameRow : queryRow = row
    · have different : queryCol ≠ column := by intro sameCol; exact equal (by rw [sameRow, sameCol])
      simp [sameRow, different]
    · simp [sameRow]

theorem model_fold_size (items : List ℕ) (width rank column : ℕ)
    (matrix : Array Integer) (previous : Integer) (initial : Array ℤ) :
    (items.foldl (fun result row => modelRow width rank column matrix previous row result) initial).size =
      initial.size := by
  induction items generalizing initial with
  | nil => rfl
  | cons head tail ih => simpa [modelRow_size] using ih (modelRow width rank column matrix previous head initial)

theorem model_fold_get (items : List ℕ) (width rank column queryRow queryCol : ℕ)
    (matrix : Array Integer) (previous : Integer) (initial : Array ℤ)
    (columnBound : column < width) (queryColBound : queryCol < width)
    (inside : queryRow * width + queryCol < initial.size) :
    (items.foldl (fun result row => modelRow width rank column matrix previous row result)
      initial)[queryRow * width + queryCol]! =
      if queryRow ∈ items then
        if column < queryCol then entryValue width rank column queryRow queryCol matrix previous
        else if queryCol = column then 0 else initial[queryRow * width + queryCol]!
      else initial[queryRow * width + queryCol]! := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldl_cons, ih _ (by simpa [modelRow_size] using inside)]
    rw [modelRow_get _ _ _ _ _ _ _ _ _ columnBound queryColBound inside]
    by_cases sameRow : queryRow = head <;> by_cases member : queryRow ∈ tail <;>
      by_cases later : column < queryCol <;> by_cases sameCol : queryCol = column <;>
        simp_all

theorem model_size (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer) :
    (model width rows rank column matrix previous).size = matrix.size := by
  simp only [model, model_fold_size, Array.size_map]

theorem model_get (width rows rank column row col : ℕ) (matrix : Array Integer) (previous : Integer)
    (size : matrix.size = rows * width) (rankBound : rank < rows) (columnBound : column < width)
    (rowBound : row < rows) (colBound : col < width) :
    (model width rows rank column matrix previous)[row * width + col]! =
      if rank < row then
        if column < col then entryValue width rank column row col matrix previous
        else if col = column then 0 else value matrix[row * width + col]!
      else value matrix[row * width + col]! := by
  have inside : row * width + col < matrix.size := by rw [size]; nlinarith
  have member : row ∈ List.range' (rank + 1) (rows - (rank + 1)) ↔ rank < row := by
    simp only [List.mem_range'_1]
    omega
  rw [model, model_fold_get _ _ _ _ _ _ _ _ _ columnBound colBound (by simpa using inside)]
  simp only [member]
  have mapped : (matrix.map value)[row * width + col]! = value matrix[row * width + col]! := by
    rw [getElem!_pos (matrix.map value) (row * width + col) (by simpa using inside),
      Array.getElem_map, getElem!_pos matrix (row * width + col) inside]
  rw [mapped]

#print axioms model_get

end Project.Beck.Elimination
