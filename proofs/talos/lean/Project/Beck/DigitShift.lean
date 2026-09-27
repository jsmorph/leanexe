import Project.Beck.DigitUpdate

namespace Project.Beck.DigitShift

open LeanExe.Examples.BeckExact DigitValue DigitAdd DigitUpdate

def step (a : Array UInt64) (state : Array UInt64 × UInt64) (index : ℕ) : Array UInt64 × UInt64 :=
  let total := a[index]! * 2 + state.2
  (state.1.push (total % Digits.radix), total / Digits.radix)

def scan (a : Array UInt64) (bit : UInt64) (count : ℕ) : Array UInt64 × UInt64 :=
  (List.range count).foldl (step a) (#[], bit)

theorem scan_next (a : Array UInt64) (bit : UInt64) (count : ℕ) :
    scan a bit (count + 1) = step a (scan a bit count) count := by
  simp [scan, List.range_succ, List.foldl_append]

theorem scan_correct (a : Array UInt64) (bit : UInt64) (ha : Valid a)
    (hb : bit.toNat ≤ 1) (count : ℕ) (inside : count ≤ a.size) :
    (scan a bit count).1.size = count ∧ Valid (scan a bit count).1 ∧
      (scan a bit count).2.toNat ≤ 1 ∧
      value (scan a bit count).1 + 4294967296 ^ count * (scan a bit count).2.toNat =
        2 * lowerValue a count + bit.toNat := by
  induction count with
  | zero => simpa [scan, Valid, value, lowerValue] using hb
  | succ count ih =>
    have prior := ih (by omega)
    have indexA : count < a.size := by omega
    let old := scan a bit count
    let total := a[count]! * 2 + old.2
    have valid := valid_get a ha count indexA
    have carried := LimbArithmetic.add_carry a[count]! a[count]! old.2 valid valid prior.2.2.1
    rw [← UInt64.mul_two] at carried
    rw [scan_next]
    change (old.1.push (total % Digits.radix)).size = count + 1 ∧
      Valid (old.1.push (total % Digits.radix)) ∧ (total / Digits.radix).toNat ≤ 1 ∧ _
    refine ⟨by simpa using prior.1, ?_, carried.2.1, ?_⟩
    · intro digit member
      rcases Array.mem_push.mp member with member | equal
      · exact prior.2.1 digit member
      · simpa [equal] using carried.1
    · change value (old.1.push (total % Digits.radix)) +
          4294967296 ^ (count + 1) * (total / Digits.radix).toNat = _
      rw [value_push, prior.1, pow_succ, prefix_next]
      simp only [Digits.get, indexA, ite_true]
      have equation := prior.2.2.2
      have scaled := congrArg (fun x : ℕ => 4294967296 ^ count * x) carried.2.2
      change value old.1 + 4294967296 ^ count * old.2.toNat = _ at equation
      change 4294967296 ^ count *
          ((total % Digits.radix).toNat + 4294967296 * (total / Digits.radix).toNat) =
        4294967296 ^ count * (a[count]!.toNat + a[count]!.toNat + old.2.toNat) at scaled
      nlinarith only [equation, scaled]

theorem shift_eq (a : Array UInt64) (bit : UInt64) :
    Digits.shiftBit a bit =
      let state := scan a bit a.size
      Digits.trim (if state.2 != 0 then state.1.push state.2 else state.1) := by
  simp only [Digits.shiftBit, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', Id.run, bind, pure]
  have loop := List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range a.size)
    (fun index state => step a state index) (#[], bit)
  simp only [pure, step] at loop
  rw [loop]
  simp only [scan, ← apply_ite Digits.trim]
  rfl

theorem shift_correct (a : Array UInt64) (bit : UInt64) (ha : Valid a) (hb : bit.toNat ≤ 1) :
    Valid (Digits.shiftBit a bit) ∧ value (Digits.shiftBit a bit) = 2 * value a + bit.toNat := by
  have result := scan_correct a bit ha hb a.size (by rfl)
  rw [prefix_full a a.size (by rfl)] at result
  rw [shift_eq]
  dsimp only
  constructor
  · apply trim_valid
    split
    · intro digit member
      rcases Array.mem_push.mp member with member | equal
      · exact result.2.1 digit member
      · rw [equal]
        dsimp [LimbArithmetic.Valid]
        omega
    · exact result.2.1
  · rw [trim_value]
    split
    · rw [value_push, result.1]
      exact result.2.2.2
    · rename_i zero
      have wordZero : (scan a bit a.size).2 = 0 := by simpa using zero
      simpa [wordZero] using result.2.2.2

#print axioms shift_correct

end Project.Beck.DigitShift
