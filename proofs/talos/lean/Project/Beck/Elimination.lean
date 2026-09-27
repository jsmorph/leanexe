import LeanExe.Examples.BeckExact
import Project.Beck.Bareiss

namespace Project.Beck.Elimination

open LeanExe.Examples.BeckExact IntegerAdd

def Represents (source : Array Integer) (target : Array ℤ) : Prop :=
  (∀ entry ∈ source, Valid entry) ∧ source.map value = target

theorem represents_set (source : Array Integer) (target : Array ℤ)
    (related : Represents source target) (index : ℕ) (entry : Integer) (valid : Valid entry) :
    Represents (source.set! index entry) (target.set! index (value entry)) := by
  constructor
  · intro word member
    rcases Array.mem_or_eq_of_mem_setIfInBounds member with prior | equal
    · exact related.1 word prior
    · simpa [equal] using valid
  · simp [Array.set!_eq_setIfInBounds, ← related.2]

theorem get_valid (matrix : Array Integer) (valid : ∀ entry ∈ matrix, Valid entry)
    (index : ℕ) (inside : index < matrix.size) : Valid matrix[index]! := by
  rw [getElem!_pos matrix index inside]
  exact valid _ (Array.getElem_mem inside)

theorem forIn_refines {α β γ : Type*} (items : List α)
    (body : α → β → Option (ForInStep β)) (next : α → γ → γ)
    (related : β → γ → Prop)
    (one : ∀ item ∈ items, ∀ source target, related source target →
      ∃ result, body item source = some (.yield result) ∧ related result (next item target))
    (source : β) (target : γ) (initial : related source target) :
    ∃ result, forIn items source body = some result ∧
      related result (items.foldl (fun state item => next item state) target) := by
  induction items generalizing source target with
  | nil => exact ⟨source, rfl, initial⟩
  | cons head tail ih =>
    obtain ⟨middle, headSource, headRelated⟩ := one head (by simp) source target initial
    obtain ⟨result, tailSource, tailRelated⟩ := ih
      (by intro item member; exact one item (by simp [member])) middle (next head target) headRelated
    refine ⟨result, ?_, tailRelated⟩
    simpa [List.forIn_cons, headSource, bind, pure] using tailSource

def cell (width rank column row col : ℕ) (matrix : Array Integer) (previous : Integer) :
    Option Integer :=
  Integer.divideExact
    (Integer.sub (Integer.mul matrix[rank * width + column]! matrix[row * width + col]!)
      (Integer.mul matrix[row * width + column]! matrix[rank * width + col]!)) previous

def entryValue (width rank column row col : ℕ) (matrix : Array Integer) (previous : Integer) : ℤ :=
  (value matrix[rank * width + column]! * value matrix[row * width + col]! -
    value matrix[row * width + column]! * value matrix[rank * width + col]!) / value previous

def columnBody (width rank column row : ℕ) (matrix : Array Integer) (previous : Integer)
    (col : ℕ) (result : Array Integer) : Option (ForInStep (Array Integer)) := do
  let entry ← cell width rank column row col matrix previous
  return .yield (result.set! (row * width + col) entry)

def rowBody (width rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (row : ℕ) (result : Array Integer) : Option (ForInStep (Array Integer)) := do
  let updated ← forIn (List.range' (column + 1) (width - (column + 1))) result
    (columnBody width rank column row matrix previous)
  return .yield (updated.set! (row * width + column) Integer.zero)

def modelRow (width rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (row : ℕ) (result : Array ℤ) : Array ℤ :=
  let updated := (List.range' (column + 1) (width - (column + 1))).foldl
    (fun result col => result.set! (row * width + col)
      (entryValue width rank column row col matrix previous)) result
  updated.set! (row * width + column) 0

def model (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer) : Array ℤ :=
  (List.range' (rank + 1) (rows - (rank + 1))).foldl
    (fun result row => modelRow width rank column matrix previous row result) (matrix.map value)

theorem source_eq (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer) :
    eliminate width rows rank column matrix previous =
      forIn (List.range' (rank + 1) (rows - (rank + 1))) matrix
        (rowBody width rank column matrix previous) := by
  simp only [eliminate,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one]
  simp only [bind_pure]
  rfl

theorem eliminate_correct (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (size : matrix.size = rows * width) (rankBound : rank < rows) (columnBound : column < width)
    (valid : ∀ entry ∈ matrix, Valid entry) (previousValid : Valid previous)
    (nonzero : value previous ≠ 0)
    (divides : ∀ row, rank < row → row < rows → ∀ col, column < col → col < width →
      value previous ∣ value matrix[rank * width + column]! * value matrix[row * width + col]! -
        value matrix[row * width + column]! * value matrix[rank * width + col]!) :
    ∃ result, eliminate width rows rank column matrix previous = some result ∧
      Represents result (model width rows rank column matrix previous) := by
  have entryValid (row col : ℕ) (hr : row < rows) (hc : col < width) :
      Valid matrix[row * width + col]! := by
    apply get_valid matrix valid
    rw [size]
    nlinarith
  rw [source_eq]
  apply forIn_refines _ _ _ Represents _ matrix (matrix.map value) ⟨valid, rfl⟩
  intro row member source target related
  have rowBounds : rank < row ∧ row < rows := by
    simp only [List.mem_range'] at member
    omega
  have columns := forIn_refines (List.range' (column + 1) (width - (column + 1)))
    (columnBody width rank column row matrix previous)
    (fun col result => result.set! (row * width + col) (entryValue width rank column row col matrix previous))
    Represents ?_ source target related
  · obtain ⟨updated, sourceColumns, relatedColumns⟩ := columns
    refine ⟨updated.set! (row * width + column) Integer.zero, ?_, ?_⟩
    · simp [rowBody, sourceColumns]
    · simpa [modelRow, zero_correct.2] using
        represents_set _ _ relatedColumns (row * width + column) Integer.zero zero_correct.1
  · intro col member source target related
    have colBounds : column < col ∧ col < width := by
      simp only [List.mem_range'] at member
      omega
    obtain ⟨entry, sourceCell, validCell, valueCell⟩ := Bareiss.update_correct
      matrix[rank * width + column]! matrix[row * width + column]!
      matrix[row * width + col]! matrix[rank * width + col]! previous
      (entryValid _ _ rankBound columnBound) (entryValid _ _ rowBounds.2 columnBound)
      (entryValid _ _ rowBounds.2 colBounds.2) (entryValid _ _ rankBound colBounds.2)
      previousValid nonzero (divides row rowBounds.1 rowBounds.2 col colBounds.1 colBounds.2)
    refine ⟨source.set! (row * width + col) entry, ?_, ?_⟩
    · dsimp only [columnBody, cell]
      rw [sourceCell]
      rfl
    · have updated := represents_set _ _ related (row * width + col) entry validCell
      simpa only [valueCell, entryValue] using updated

#print axioms eliminate_correct

end Project.Beck.Elimination
