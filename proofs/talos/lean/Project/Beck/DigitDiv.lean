import Project.Beck.DigitBits
import Project.Beck.DigitShift
import Project.Beck.IntegerAdd

namespace Project.Beck.DigitDiv

open LeanExe.Examples.BeckExact DigitValue DigitUpdate DigitBits

def step (a b : Array UInt64) (state : Array UInt64 × Array UInt64) (offset : ℕ) :
    Array UInt64 × Array UInt64 :=
  let index := 32 * a.size - 1 - offset
  let bit := (a[index / 32]! >>> (index % 32).toUInt64) &&& 1
  let remainder := Digits.shiftBit state.2 bit
  if Digits.compare remainder b != 1 then
    (insertBit state.1 index, Digits.sub remainder b)
  else (state.1, remainder)

def scan (a b : Array UInt64) (count : ℕ) : Array UInt64 × Array UInt64 :=
  (List.range count).foldl (step a b) (Array.replicate a.size 0, #[])

theorem scan_next (a b : Array UInt64) (count : ℕ) :
    scan a b (count + 1) = step a b (scan a b count) count := by
  simp [scan, List.range_succ, List.foldl_append]

structure Invariant (a b : Array UInt64) (remaining : ℕ)
    (state : Array UInt64 × Array UInt64) : Prop where
  size : state.1.size = a.size
  quotient : Valid state.1
  remainder : Valid state.2
  remainder_lt : value state.2 < value b
  low_zero : value state.1 % 2 ^ remaining = 0
  equation : value a / 2 ^ remaining * 2 ^ remaining =
    value state.1 * value b + value state.2 * 2 ^ remaining

theorem prefix_step (number index : ℕ) :
    number / 2 ^ index * 2 ^ index =
      number / 2 ^ (index + 1) * 2 ^ (index + 1) +
        (number / 2 ^ index % 2) * 2 ^ index := by
  have split := Nat.mod_add_div (number / 2 ^ index) 2
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  nlinarith only [congrArg (fun n => n * 2 ^ index) split]

theorem initial (a b : Array UInt64) (ha : Valid a) (nonzero : 0 < value b) :
    Invariant a b (32 * a.size) (Array.replicate a.size 0, #[]) := by
  have bound : value a < 2 ^ (32 * a.size) := by
    rw [pow_mul]
    exact value_bound a ha
  refine ⟨by simp, valid_zeros _, ?_, ?_, ?_, ?_⟩
  · simp [Valid]
  · simpa [value_empty] using nonzero
  · simp [value_zeros]
  · simp [Nat.div_eq_of_lt bound, value_zeros, value_empty]

theorem step_correct (a b : Array UInt64) (ha : Valid a) (hb : Valid b)
    (count : ℕ) (inside : count < 32 * a.size) (state : Array UInt64 × Array UInt64)
    (prior : Invariant a b (32 * a.size - count) state) :
    Invariant a b (32 * a.size - (count + 1)) (step a b state count) := by
  let index := 32 * a.size - 1 - count
  let bit := (a[index / 32]! >>> (index % 32).toUInt64) &&& 1
  let remainder := Digits.shiftBit state.2 bit
  have remaining : 32 * a.size - count = index + 1 := by omega
  have next : 32 * a.size - (count + 1) = index := by omega
  have indexBound : index < 32 * a.size := by omega
  have bitValue : bit.toNat = value a / 2 ^ index % 2 := bit_value a ha index indexBound
  have bitBound : bit.toNat ≤ 1 := by rw [bitValue]; omega
  have shifted := DigitShift.shift_correct state.2 bit prior.remainder bitBound
  have equation := prior.equation
  rw [remaining] at equation
  have inputStep := prefix_step (value a) index
  have expanded : value a / 2 ^ index * 2 ^ index =
      value state.1 * value b + value remainder * 2 ^ index := by
    rw [inputStep, equation, pow_succ]
    rw [show value remainder = 2 * value state.2 + bit.toNat from shifted.2, bitValue]
    ring
  have twice : value remainder < 2 * value b := by
    have small := prior.remainder_lt
    have equality : value remainder = 2 * value state.2 + bit.toNat := shifted.2
    omega
  have lowZero : value state.1 % 2 ^ index = 0 := by
    have divides : 2 ^ index ∣ 2 ^ (32 * a.size - count) :=
      pow_dvd_pow 2 (by omega)
    rw [← Nat.mod_mod_of_dvd (value state.1) divides, prior.low_zero, Nat.zero_mod]
  rw [next]
  dsimp only [step]
  change Invariant a b index (if Digits.compare remainder b != 1 then
    (insertBit state.1 index, Digits.sub remainder b) else (state.1, remainder))
  rw [DigitCompare.compare_correct remainder b shifted.1 hb]
  by_cases smaller : value remainder < value b
  · simp only [smaller, ite_true, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact ⟨prior.size, prior.quotient, shifted.1, smaller, lowZero, expanded⟩
  · have enough : value b ≤ value remainder := by omega
    have subtracted := DigitSub.sub_correct remainder b shifted.1 hb enough
    have inserted := insert_correct state.1 prior.quotient index
      (by rw [prior.size]; exact indexBound) (by rw [← remaining]; exact prior.low_zero)
    have compareBranch : (if value b < value remainder then (2 : UInt64) else 0) != 1 := by
      split <;> decide
    simp only [smaller, ite_false, compareBranch, ite_true]
    refine ⟨inserted.1.trans prior.size, inserted.2.1, subtracted.1, ?_, ?_, ?_⟩
    · rw [subtracted.2]
      omega
    · rw [inserted.2.2, Nat.add_mod, lowZero, Nat.mod_self, Nat.zero_add, Nat.zero_mod]
    · rw [inserted.2.2, subtracted.2]
      nlinarith only [expanded, congrArg (fun n => n * 2 ^ index) (Nat.sub_add_cancel enough)]

theorem scan_correct (a b : Array UInt64) (ha : Valid a) (hb : Valid b)
    (nonzero : 0 < value b) (count : ℕ) (inside : count ≤ 32 * a.size) :
    Invariant a b (32 * a.size - count) (scan a b count) := by
  induction count with
  | zero => simpa [scan] using initial a b ha nonzero
  | succ count ih =>
    rw [scan_next]
    exact step_correct a b ha hb count (by omega) _ (ih (by omega))

theorem source_eq (a b : Array UInt64) :
    Digits.divRem a b = if Digits.length b == 0 then none else
      let result := scan a b (32 * a.size)
      some (Digits.trim result.1, result.2) := by
  simp only [Digits.divRem, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', Id.run, bind, pure]
  split
  · rfl
  · have loop := List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range (32 * a.size))
      (fun index state => step a b state index) (Array.replicate a.size 0, #[])
    simp only [pure, step, insertBit] at loop
    simp only [← apply_ite ForInStep.yield]
    rw [loop]
    rfl

theorem divRem_correct (a b : Array UInt64) (ha : Valid a) (hb : Valid b)
    (nonzero : 0 < value b) :
    ∃ quotient remainder, Digits.divRem a b = some (quotient, remainder) ∧
      Valid quotient ∧ Valid remainder ∧ value remainder < value b ∧
      value a = value quotient * value b + value remainder := by
  have length : Digits.length b ≠ 0 := by
    intro zero
    have valueZero := (IntegerAdd.length_zero_iff b).mp zero
    omega
  have invariant := scan_correct a b ha hb nonzero (32 * a.size) (by rfl)
  rw [source_eq]
  simp only [length, beq_iff_eq, ↓reduceIte]
  refine ⟨_, _, rfl, trim_valid _ invariant.quotient, invariant.remainder,
    invariant.remainder_lt, ?_⟩
  rw [trim_value]
  simpa using invariant.equation

#print axioms divRem_correct

end Project.Beck.DigitDiv
