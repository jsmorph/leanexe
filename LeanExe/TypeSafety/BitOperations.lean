import LeanExe.TypeSafety.NatOperations

/-!
# Finite mathematical bit operations

`bitwiseBits` uses structural recursion on the declared width. Its specification
is the arithmetic `bitAt` function below, independently of Lean's native bitwise
implementation. Inputs need not be bounded; exactly the selected low bits matter.
-/

namespace LeanExe.TypeSafety

def bitAt (value index : Nat) : Bool := decide ((value / 2 ^ index) % 2 = 1)

def bitCons (low : Bool) (high : Nat) : Nat := 2 * high + if low then 1 else 0

def bitwiseBits : Nat → (Bool → Bool → Bool) → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | bits + 1, operation, left, right =>
      bitCons (operation (bitAt left 0) (bitAt right 0))
        (bitwiseBits bits operation (left / 2) (right / 2))

theorem bitAt_zero (value : Nat) : bitAt value 0 = decide (value % 2 = 1) := by
  simp only [bitAt, Nat.pow_zero, Nat.div_one]

theorem bitAt_succ (value index : Nat) : bitAt value (index + 1) =
    bitAt (value / 2) index := by
  simp only [bitAt, Nat.pow_succ', Nat.div_div_eq_div_mul]

theorem bitCons_div_two (low : Bool) (high : Nat) : bitCons low high / 2 = high := by
  unfold bitCons
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide)]
  cases low <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.reduceDiv, Nat.zero_add]

theorem bitCons_mod_two (low : Bool) (high : Nat) :
    bitCons low high % 2 = if low then 1 else 0 := by
  cases low <;> simp [bitCons]

theorem bitAt_bitCons_zero (low : Bool) (high : Nat) :
    bitAt (bitCons low high) 0 = low := by
  rw [bitAt_zero, bitCons_mod_two]
  cases low <;> rfl

theorem bitAt_bitCons_succ (low : Bool) (high index : Nat) :
    bitAt (bitCons low high) (index + 1) = bitAt high index := by
  rw [bitAt_succ, bitCons_div_two]

theorem bitCons_reconstruct (value : Nat) : bitCons (bitAt value 0) (value / 2) = value := by
  have remainder := Nat.mod_two_eq_zero_or_one value
  have reconstruction := Nat.div_add_mod value 2
  rcases remainder with zero | one
  · simp only [bitCons, bitAt_zero, zero, show ¬(0 = 1) by decide, decide_false,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    simpa only [zero, Nat.add_zero] using reconstruction
  · simp only [bitCons, bitAt_zero, one, decide_true, ↓reduceIte]
    simpa only [one] using reconstruction

theorem bitwiseBits_bounded (bits : Nat) (operation : Bool → Bool → Bool)
    (left right : Nat) : bitwiseBits bits operation left right < 2 ^ bits := by
  induction bits generalizing left right with
  | zero => simp [bitwiseBits]
  | succ bits ih =>
      have bound := ih (left / 2) (right / 2)
      simp only [bitwiseBits, bitCons, Nat.pow_succ]
      have doubled : 2 * (bitwiseBits bits operation (left / 2) (right / 2) + 1) ≤
          2 * 2 ^ bits := Nat.mul_le_mul_left 2 bound
      rw [Nat.mul_succ] at doubled
      rw [Nat.mul_comm (2 ^ bits) 2]
      split
      · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 1 < 2) _) doubled
      · exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) doubled

/-- Universal pointwise characterization, including unbounded raw operands. -/
theorem bitwiseBits_bitAt (bits : Nat) (operation : Bool → Bool → Bool)
    (left right index : Nat) (inside : index < bits) :
    bitAt (bitwiseBits bits operation left right) index =
      operation (bitAt left index) (bitAt right index) := by
  induction bits generalizing left right index with
  | zero => exact False.elim (Nat.not_lt_zero _ inside)
  | succ bits ih =>
      cases index with
      | zero => exact bitAt_bitCons_zero _ _
      | succ index =>
          simp only [bitwiseBits, bitAt_bitCons_succ]
          rw [ih _ _ _ (Nat.lt_of_succ_lt_succ inside), bitAt_succ, bitAt_succ]

/-- Bounded natural numbers are determined by all their in-range bits. -/
theorem eq_of_bitAt_eq (bits left right : Nat) (leftBound : left < 2 ^ bits)
    (rightBound : right < 2 ^ bits)
    (same : ∀ index, index < bits → bitAt left index = bitAt right index) : left = right := by
  induction bits generalizing left right with
  | zero =>
      exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ leftBound)).trans
        (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ rightBound)).symm
  | succ bits ih =>
      have leftHalf : left / 2 < 2 ^ bits := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        simpa only [Nat.pow_succ] using leftBound
      have rightHalf : right / 2 < 2 ^ bits := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
        simpa only [Nat.pow_succ] using rightBound
      have halves : left / 2 = right / 2 := ih _ _ leftHalf rightHalf (by
        intro index inside
        rw [← bitAt_succ, ← bitAt_succ]
        exact same _ (Nat.succ_lt_succ inside))
      rw [← bitCons_reconstruct left, ← bitCons_reconstruct right, halves,
        same 0 (Nat.zero_lt_succ _)]

theorem bitAt_zero_value (index : Nat) : bitAt 0 index = false := by simp [bitAt]

theorem bitwiseBits_all_ones (bits left right : Nat) :
    bitwiseBits bits (fun _ _ => true) left right = 2 ^ bits - 1 := by
  induction bits generalizing left right with
  | zero => rfl
  | succ bits ih =>
      simp only [bitwiseBits, bitCons, ↓reduceIte, ih, Nat.pow_succ]
      have positive : 0 < 2 ^ bits := Nat.pow_pos (by decide)
      apply Eq.symm
      apply (Nat.sub_eq_iff_eq_add (Nat.le_trans (by decide : 1 ≤ 2)
        (Nat.mul_le_mul_right 2 positive))).mpr
      calc
        2 ^ bits * 2 = ((2 ^ bits - 1) + 1) * 2 := by
          rw [Nat.sub_add_cancel positive]
        _ = (2 * (2 ^ bits - 1) + 1) + 1 := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ bits - 1) 2]

theorem bitAt_mask (bits index : Nat) (inside : index < bits) :
    bitAt (2 ^ bits - 1) index = true := by
  rw [← bitwiseBits_all_ones bits 0 0]
  exact bitwiseBits_bitAt bits (fun _ _ => true) 0 0 index inside

end LeanExe.TypeSafety
