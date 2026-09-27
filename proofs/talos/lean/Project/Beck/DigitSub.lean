import Project.Beck.DigitAdd

namespace Project.Beck.DigitSub

open LeanExe.Examples.BeckExact DigitValue DigitAdd

theorem limb_sub (a b borrow : UInt64) (ha : LimbArithmetic.Valid a)
    (hb : LimbArithmetic.Valid b) (hc : borrow.toNat ≤ 1) :
    let digit := (a + Digits.radix - (b + borrow)) % Digits.radix
    let next : UInt64 := if a < b + borrow then 1 else 0
    LimbArithmetic.Valid digit ∧ next.toNat ≤ 1 ∧
      digit.toNat + b.toNat + borrow.toNat = a.toNat + 4294967296 * next.toNat := by
  have right : (b + borrow).toNat = b.toNat + borrow.toNat := by
    rw [UInt64.toNat_add]
    apply Nat.mod_eq_of_lt
    dsimp [LimbArithmetic.Valid] at hb
    omega
  have left : (a + Digits.radix).toNat = a.toNat + 4294967296 := by
    rw [UInt64.toNat_add]
    apply Nat.mod_eq_of_lt
    dsimp [LimbArithmetic.Valid] at ha
    change a.toNat + 4294967296 < 18446744073709551616
    omega
  have enough : b + borrow ≤ a + Digits.radix := by
    rw [UInt64.le_iff_toNat_le, left, right]
    dsimp [LimbArithmetic.Valid] at hb
    omega
  dsimp only
  rw [LimbArithmetic.Valid, UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ enough, left, right]
  change (a.toNat + 4294967296 - (b.toNat + borrow.toNat)) % 4294967296 < 4294967296 ∧ _
  refine ⟨Nat.mod_lt _ (by decide), ?_⟩
  split <;> rename_i comparison
  · rw [UInt64.lt_iff_toNat_lt, right] at comparison
    dsimp [LimbArithmetic.Valid] at ha hb
    change 1 ≤ 1 ∧ _
    constructor
    · omega
    · change (a.toNat + 4294967296 - (b.toNat + borrow.toNat)) % 4294967296 +
        b.toNat + borrow.toNat = a.toNat + 4294967296 * 1
      omega
  · have comparison' : b.toNat + borrow.toNat ≤ a.toNat := by
      simpa [UInt64.lt_iff_toNat_lt, right] using comparison
    dsimp [LimbArithmetic.Valid] at ha hb
    change 0 ≤ 1 ∧ _
    constructor
    · omega
    · change (a.toNat + 4294967296 - (b.toNat + borrow.toNat)) % 4294967296 +
        b.toNat + borrow.toNat = a.toNat + 4294967296 * 0
      omega

def step (a b : Array UInt64) (state : Array UInt64 × UInt64) (index : ℕ) : Array UInt64 × UInt64 :=
  let left := a[index]!
  let right := Digits.get b index + state.2
  (state.1.push ((left + Digits.radix - right) % Digits.radix), if left < right then 1 else 0)

def scan (a b : Array UInt64) (count : ℕ) : Array UInt64 × UInt64 :=
  (List.range count).foldl (step a b) (#[], 0)

theorem scan_next (a b : Array UInt64) (count : ℕ) :
    scan a b (count + 1) = step a b (scan a b count) count := by
  simp [scan, List.range_succ, List.foldl_append]

theorem scan_valid (a b : Array UInt64) (ha : Valid a) (hb : Valid b)
    (count : ℕ) (inside : count ≤ a.size) :
    (scan a b count).1.size = count ∧ Valid (scan a b count).1 ∧
      (scan a b count).2.toNat ≤ 1 ∧
      value (scan a b count).1 + lowerValue b count =
        lowerValue a count + 4294967296 ^ count * (scan a b count).2.toNat := by
  induction count with
  | zero => simp [scan, Valid, value, lowerValue]
  | succ count ih =>
    have prior := ih (by omega)
    have indexBound : count < a.size := by omega
    have aValid : LimbArithmetic.Valid a[count]! := by
      rw [getElem!_pos a count indexBound]
      exact ha _ (Array.getElem_mem indexBound)
    let old := scan a b count
    let digit := (a[count]! + Digits.radix - (Digits.get b count + old.2)) % Digits.radix
    let next : UInt64 := if a[count]! < Digits.get b count + old.2 then 1 else 0
    have borrowed := limb_sub a[count]! (Digits.get b count) old.2 aValid
      (get_valid b hb count) prior.2.2.1
    rw [scan_next]
    change (old.1.push digit).size = count + 1 ∧ Valid (old.1.push digit) ∧ next.toNat ≤ 1 ∧ _
    refine ⟨by simpa [old] using prior.1, ?_, borrowed.2.1, ?_⟩
    · intro word member
      rcases Array.mem_push.mp member with member | equal
      · exact prior.2.1 word member
      · simpa [equal] using borrowed.1
    · change value (old.1.push digit) + lowerValue b (count + 1) =
        lowerValue a (count + 1) + 4294967296 ^ (count + 1) * next.toNat
      rw [value_push, prior.1, prefix_next, prefix_next, pow_succ]
      have getSame : Digits.get a count = a[count]! := by simp [Digits.get, indexBound]
      rw [getSame]
      have localEquation := congrArg (fun x : ℕ => 4294967296 ^ count * x) borrowed.2.2
      nlinarith [prior.2.2.2]

theorem sub_eq (a b : Array UInt64) :
    Digits.sub a b = Digits.trim (scan a b a.size).1 := by
  simp only [Digits.sub, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', Id.run, bind, pure]
  have loop := List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range a.size)
    (fun index state => step a b state index) (#[], 0)
  simp only [pure, step] at loop
  rw [loop]
  rfl

theorem lowerValue_eq_of_lt (digits : Array UInt64) (count : ℕ)
    (bound : value digits < 4294967296 ^ count) : lowerValue digits count = value digits := by
  by_cases inside : count ≤ digits.size
  · have split := congrArg (fun xs : List UInt64 => Nat.ofDigits 4294967296 (xs.map UInt64.toNat))
      (List.take_append_drop count digits.toList)
    simp only [List.map_append, Nat.ofDigits_append, List.length_map, List.length_take,
      Array.length_toList, Nat.min_eq_left inside] at split
    have tailZero : Nat.ofDigits 4294967296 ((digits.toList.drop count).map UInt64.toNat) = 0 := by
      change _ = value digits at split
      by_contra nonzero
      have positive := Nat.one_le_iff_ne_zero.mpr nonzero
      have enough := Nat.mul_le_mul_left (4294967296 ^ count) positive
      simp only [mul_one] at enough
      omega
    rw [tailZero, mul_zero, add_zero] at split
    simpa [lowerValue, value] using split
  · exact prefix_full digits count (by omega)

theorem sub_correct (a b : Array UInt64) (ha : Valid a) (hb : Valid b)
    (ordered : value b ≤ value a) :
    Valid (Digits.sub a b) ∧ value (Digits.sub a b) = value a - value b := by
  have specification := scan_valid a b ha hb a.size (by omega)
  have bound := value_bound a ha
  have bBound : value b < 4294967296 ^ a.size := by omega
  rw [prefix_full a _ (by omega), lowerValue_eq_of_lt b _ bBound] at specification
  have outputBound := value_bound (scan a b a.size).1 specification.2.1
  rw [specification.1] at outputBound
  have zero : (scan a b a.size).2.toNat = 0 := by
    nlinarith [specification.2.2.2]
  rw [sub_eq]
  refine ⟨trim_valid _ specification.2.1, ?_⟩
  rw [trim_value]
  have equation := specification.2.2.2
  rw [zero, mul_zero, add_zero] at equation
  omega

#print axioms sub_correct

end Project.Beck.DigitSub
