import Project.Beck.DigitUpdate

namespace Project.Beck.DigitMulRow

open LeanExe.Examples.BeckExact DigitValue DigitAdd DigitUpdate

def step (digit : UInt64) (b : Array UInt64) (offset : ℕ)
    (state : Array UInt64 × UInt64) (index : ℕ) : Array UInt64 × UInt64 :=
  let total := digit * b[index]! + state.1[offset + index]! + state.2
  (state.1.set! (offset + index) (total % Digits.radix), total / Digits.radix)

def scan (digit : UInt64) (b initial : Array UInt64) (offset count : ℕ) :
    Array UInt64 × UInt64 :=
  (List.range count).foldl (step digit b offset) (initial, 0)

theorem scan_next (digit : UInt64) (b initial : Array UInt64) (offset count : ℕ) :
    scan digit b initial offset (count + 1) =
      step digit b offset (scan digit b initial offset count) count := by
  simp [scan, List.range_succ, List.foldl_append]

theorem scan_correct (digit : UInt64) (b initial : Array UInt64) (offset count : ℕ)
    (hd : LimbArithmetic.Valid digit) (hb : Valid b) (hi : Valid initial)
    (space : offset + b.size < initial.size) (countBound : count ≤ b.size) :
    (scan digit b initial offset count).1.size = initial.size ∧
      Valid (scan digit b initial offset count).1 ∧
      LimbArithmetic.Valid (scan digit b initial offset count).2 ∧
      value (scan digit b initial offset count).1 +
          4294967296 ^ (offset + count) * (scan digit b initial offset count).2.toNat =
        value initial + 4294967296 ^ offset * digit.toNat * lowerValue b count ∧
      (∀ index, offset + count ≤ index →
        (scan digit b initial offset count).1[index]! = initial[index]!) := by
  induction count with
  | zero =>
    simpa [scan, lowerValue, value, LimbArithmetic.Valid] using hi
  | succ count ih =>
    have prior := ih (by omega)
    let old := scan digit b initial offset count
    let total := digit * b[count]! + old.1[offset + count]! + old.2
    have indexB : count < b.size := by omega
    have indexResult : offset + count < old.1.size := by
      dsimp [old]
      rw [prior.1]
      omega
    have carried := LimbArithmetic.mul_carry digit b[count]! old.1[offset + count]! old.2
      hd (valid_get b hb count indexB) (valid_get old.1 prior.2.1 _ indexResult) prior.2.2.1
    rw [scan_next]
    change (old.1.set! (offset + count) (total % Digits.radix)).size = initial.size ∧
      Valid (old.1.set! (offset + count) (total % Digits.radix)) ∧
      LimbArithmetic.Valid (total / Digits.radix) ∧ _
    refine ⟨by simpa using prior.1,
      valid_set old.1 prior.2.1 _ _ carried.1, carried.2.1, ?_, ?_⟩
    · change value (old.1.set! (offset + count) (total % Digits.radix)) +
          4294967296 ^ (offset + (count + 1)) * (total / Digits.radix).toNat = _
      have changed := value_set old.1 (offset + count) (total % Digits.radix) indexResult
      have scaled := congrArg (fun x : ℕ => 4294967296 ^ (offset + count) * x) carried.2.2
      have next := prefix_next b count
      simp only [Digits.get, indexB, ite_true] at next
      rw [next]
      have equation := prior.2.2.2.1
      change value old.1 + 4294967296 ^ (offset + count) * old.2.toNat = _ at equation
      change 4294967296 ^ (offset + count) *
          ((total % Digits.radix).toNat + 4294967296 * (total / Digits.radix).toNat) =
        4294967296 ^ (offset + count) *
          (digit.toNat * b[count]!.toNat + old.1[offset + count]!.toNat + old.2.toNat) at scaled
      simp only [pow_add, pow_succ] at equation changed scaled ⊢
      nlinarith only [equation, changed, scaled]
    · intro index upper
      change (old.1.set! (offset + count) (total % Digits.radix))[index]! = _
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      exact prior.2.2.2.2 index (by omega)

def row (digit : UInt64) (b initial : Array UInt64) (offset : ℕ) : Array UInt64 :=
  let result := scan digit b initial offset b.size
  result.1.set! (offset + b.size) result.2

theorem row_correct (digit : UInt64) (b initial : Array UInt64) (offset : ℕ)
    (hd : LimbArithmetic.Valid digit) (hb : Valid b) (hi : Valid initial)
    (space : offset + b.size < initial.size) (zero : initial[offset + b.size]! = 0) :
    (row digit b initial offset).size = initial.size ∧
      Valid (row digit b initial offset) ∧
      value (row digit b initial offset) = value initial + 4294967296 ^ offset * digit.toNat * value b ∧
      (∀ index, offset + b.size < index → (row digit b initial offset)[index]! = initial[index]!) := by
  have result := scan_correct digit b initial offset b.size hd hb hi space (by rfl)
  let state := scan digit b initial offset b.size
  have inside : offset + b.size < state.1.size := by simpa [state, result.1] using space
  have oldZero : state.1[offset + b.size]! = 0 :=
    (result.2.2.2.2 _ (by rfl)).trans zero
  refine ⟨by simpa [row] using result.1, valid_set _ result.2.1 _ _ result.2.2.1, ?_, ?_⟩
  · have changed := value_set state.1 (offset + b.size) state.2 inside
    rw [oldZero] at changed
    simp only [UInt64.toNat_zero, mul_zero, add_zero] at changed
    change value (state.1.set! (offset + b.size) state.2) = _
    rw [changed, result.2.2.2.1, prefix_full b b.size (by rfl)]
  · intro index upper
    change (state.1.set! (offset + b.size) state.2)[index]! = _
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact result.2.2.2.2 index (by omega)

#print axioms row_correct

end Project.Beck.DigitMulRow
