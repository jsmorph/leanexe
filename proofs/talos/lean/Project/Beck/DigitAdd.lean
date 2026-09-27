import Project.Beck.DigitValue

namespace Project.Beck.DigitAdd

open LeanExe.Examples.BeckExact DigitValue

def lowerValue (digits : Array UInt64) (count : ℕ) : ℕ := value (digits.extract 0 count)

theorem get_valid (digits : Array UInt64) (valid : Valid digits) (index : ℕ) :
    LimbArithmetic.Valid (Digits.get digits index) := by
  unfold Digits.get
  split
  · rename_i inside
    rw [getElem!_pos digits index inside]
    exact valid _ (Array.getElem_mem inside)
  · exact (by decide : (0 : UInt64).toNat < 4294967296)

theorem prefix_next (digits : Array UInt64) (count : ℕ) :
    lowerValue digits (count + 1) = lowerValue digits count +
      4294967296 ^ count * (Digits.get digits count).toNat := by
  by_cases inside : count < digits.size
  · unfold lowerValue
    rw [Array.extract_succ_right (by omega) inside, value_push]
    simp [Digits.get, inside, Array.size_extract, Nat.min_eq_left (Nat.le_of_lt inside)]
  · have bound : digits.size ≤ count := by omega
    have nextBound : digits.size ≤ count + 1 := by omega
    simp [lowerValue, Digits.get, inside, Array.extract_eq_self_of_le bound,
      Array.extract_eq_self_of_le nextBound]

theorem prefix_full (digits : Array UInt64) (count : ℕ) (bound : digits.size ≤ count) :
    lowerValue digits count = value digits := by simp [lowerValue, Array.extract_eq_self_of_le bound]

def step (a b : Array UInt64) (state : Array UInt64 × UInt64) (index : ℕ) : Array UInt64 × UInt64 :=
  let total := Digits.get a index + Digits.get b index + state.2
  (state.1.push (total % Digits.radix), total / Digits.radix)

def scan (a b : Array UInt64) (count : ℕ) : Array UInt64 × UInt64 :=
  (List.range count).foldl (step a b) (#[], 0)

theorem scan_next (a b : Array UInt64) (count : ℕ) :
    scan a b (count + 1) = step a b (scan a b count) count := by
  simp [scan, List.range_succ, List.foldl_append]

theorem scan_valid (a b : Array UInt64) (ha : Valid a) (hb : Valid b) (count : ℕ) :
    (scan a b count).1.size = count ∧ Valid (scan a b count).1 ∧
      (scan a b count).2.toNat ≤ 1 ∧
      value (scan a b count).1 + 4294967296 ^ count * (scan a b count).2.toNat =
        lowerValue a count + lowerValue b count := by
  induction count with
  | zero => simp [scan, Valid, value, lowerValue]
  | succ count ih =>
    let old := scan a b count
    let total := Digits.get a count + Digits.get b count + old.2
    have carried := LimbArithmetic.add_carry (Digits.get a count) (Digits.get b count) old.2
      (get_valid a ha count) (get_valid b hb count) ih.2.2.1
    rw [scan_next]
    change (old.1.push (total % Digits.radix)).size = count + 1 ∧
      Valid (old.1.push (total % Digits.radix)) ∧ (total / Digits.radix).toNat ≤ 1 ∧
      value (old.1.push (total % Digits.radix)) + 4294967296 ^ (count + 1) * (total / Digits.radix).toNat = _
    refine ⟨by simpa [old] using ih.1, ?_, carried.2.1, ?_⟩
    · intro digit member
      rcases Array.mem_push.mp member with member | equal
      · exact ih.2.1 digit member
      · simpa [equal] using carried.1
    · rw [value_push, ih.1, pow_succ]
      calc
        value old.1 + 4294967296 ^ count * (total % Digits.radix).toNat +
            (4294967296 ^ count * 4294967296) * (total / Digits.radix).toNat =
            value old.1 + 4294967296 ^ count *
              ((total % Digits.radix).toNat + 4294967296 * (total / Digits.radix).toNat) := by ring
        _ = value old.1 + 4294967296 ^ count *
            ((Digits.get a count).toNat + (Digits.get b count).toNat + old.2.toNat) := by rw [carried.2.2]
        _ = (value old.1 + 4294967296 ^ count * old.2.toNat) +
            4294967296 ^ count * (Digits.get a count).toNat +
            4294967296 ^ count * (Digits.get b count).toNat := by ring
        _ = lowerValue a (count + 1) + lowerValue b (count + 1) := by
          rw [ih.2.2.2, prefix_next, prefix_next]
          ring

theorem add_eq (a b : Array UInt64) :
    Digits.add a b =
      let state := scan a b (max a.size b.size)
      Digits.trim (if state.2 != 0 then state.1.push state.2 else state.1) := by
  simp only [Digits.add, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', Id.run, bind, pure]
  have loop := List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range (max a.size b.size))
    (fun index state => step a b state index) (#[], 0)
  simp only [pure, step] at loop
  rw [loop]
  simp only [scan, ← apply_ite Digits.trim]
  rfl

theorem add_value (a b : Array UInt64) (ha : Valid a) (hb : Valid b) :
    value (Digits.add a b) = value a + value b := by
  have specification := scan_valid a b ha hb (max a.size b.size)
  rw [prefix_full a _ (Nat.le_max_left _ _), prefix_full b _ (Nat.le_max_right _ _)] at specification
  rw [add_eq]
  dsimp only
  rw [trim_value]
  split
  · rw [value_push, specification.1]
    exact specification.2.2.2
  · rename_i zero
    have wordZero : (scan a b (max a.size b.size)).2 = 0 := by simpa using zero
    simpa [wordZero] using specification.2.2.2

#print axioms add_value

end Project.Beck.DigitAdd
