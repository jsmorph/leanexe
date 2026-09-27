import Project.Beck.DigitMulRow

namespace Project.Beck.DigitMul

open LeanExe.Examples.BeckExact DigitValue DigitAdd DigitUpdate

def step (a b : Array UInt64) (result : Array UInt64) (index : ℕ) : Array UInt64 :=
  DigitMulRow.row a[index]! b result index

def scan (a b : Array UInt64) (count : ℕ) : Array UInt64 :=
  (List.range count).foldl (step a b) (Array.replicate (a.size + b.size) 0)

theorem scan_next (a b : Array UInt64) (count : ℕ) :
    scan a b (count + 1) = step a b (scan a b count) count := by
  simp [scan, List.range_succ, List.foldl_append]

theorem scan_correct (a b : Array UInt64) (ha : Valid a) (hb : Valid b)
    (count : ℕ) (inside : count ≤ a.size) :
    (scan a b count).size = a.size + b.size ∧ Valid (scan a b count) ∧
      value (scan a b count) = lowerValue a count * value b ∧
      (∀ index, count + b.size ≤ index → (scan a b count)[index]! = 0) := by
  induction count with
  | zero =>
    simp only [scan, List.range_zero, List.foldl_nil, Array.size_replicate,
      valid_zeros, value_zeros, lowerValue, Array.extract_zero, value_empty,
      zero_mul, true_and, zero_add]
    intro index _
    by_cases inside : index < a.size + b.size
    · simp [getElem!_pos, inside]
    · simp only [getElem!_neg, Array.size_replicate, inside, not_false_eq_true]
      rfl
  | succ count ih =>
    have prior := ih (by omega)
    have indexA : count < a.size := by omega
    have result := DigitMulRow.row_correct a[count]! b (scan a b count) count
      (valid_get a ha count indexA) hb prior.2.1
      (by rw [prior.1]; omega) (prior.2.2.2 _ (by rfl))
    rw [scan_next]
    change (DigitMulRow.row a[count]! b (scan a b count) count).size = _ ∧ _
    refine ⟨result.1.trans prior.1, result.2.1, ?_, ?_⟩
    · change value (DigitMulRow.row a[count]! b (scan a b count) count) = _
      rw [result.2.2.1, prior.2.2.1, prefix_next]
      simp only [Digits.get, indexA, ite_true]
      ring
    · intro index bound
      change (DigitMulRow.row a[count]! b (scan a b count) count)[index]! = _
      rw [result.2.2.2 index (by omega)]
      exact prior.2.2.2 index (by omega)

theorem mul_eq (a b : Array UInt64) : Digits.mul a b = Digits.trim (scan a b a.size) := by
  simp only [Digits.mul, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', Id.run, bind, pure]
  have inner (digit : UInt64) (initial : Array UInt64) (offset : ℕ) :=
    List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range b.size)
      (fun index state => DigitMulRow.step digit b offset state index) (initial, 0)
  simp only [pure, DigitMulRow.step] at inner
  simp_rw [inner]
  have outer := List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range a.size)
    (fun index state => step a b state index) (Array.replicate (a.size + b.size) 0)
  simp only [pure] at outer
  apply congrArg Digits.trim
  dsimp only [scan, step, DigitMulRow.row, DigitMulRow.scan, DigitMulRow.step] at outer ⊢
  exact outer

theorem mul_correct (a b : Array UInt64) (ha : Valid a) (hb : Valid b) :
    Valid (Digits.mul a b) ∧ value (Digits.mul a b) = value a * value b := by
  have result := scan_correct a b ha hb a.size (by rfl)
  rw [mul_eq]
  exact ⟨trim_valid _ result.2.1,
    (trim_value _).trans (by simpa [prefix_full a a.size (by rfl)] using result.2.2.1)⟩

#print axioms mul_correct

end Project.Beck.DigitMul
