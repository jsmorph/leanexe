import LeanExe.ProofKit.F64AddBounds
import LeanExe.ProofKit.F64MulBounds
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64Approx

/-!
Error tracking through chains of rounded operations, with `F64Approx.Approx`: `Approx w X e`
states that the word `w` is finite and its value lies within `e` of the real number `X`.  The
rules for addition, subtraction, and multiplication combine the operands' errors with the
rounding of the operation, one unit of roundoff relative to a bound `S` on the computed operands'
result, plus `multiplicationUnderflowEpsilon` for a product.  Sums and differences of words on a
common grid of `2 ^ s` scaled units, small enough to fit in 53 bits on that grid, are exact.
-/

namespace LeanExe.ProofKit.F64ErrorTrack
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

export F64Approx (Approx approx_self)

theorem add_approx {a b : UInt64} {A B ea eb : ℝ} (ha : Approx a A ea) (hb : Approx b B eb)
    (S : ℝ) (hS : |A + B| + ea + eb ≤ S) (hmax : S < 2 ^ 1023) :
    Approx (Wasm.IEEE64.add a b) (A + B) (ea + eb + unitRoundoff64 * S) := by
  obtain ⟨hfa, hea⟩ := ha
  obtain ⟨hfb, heb⟩ := hb
  have hsum : |value a + value b - (A + B)| ≤ ea + eb := by
    rw [show value a + value b - (A + B) = (value a - A) + (value b - B) by ring]
    exact (abs_add_le _ _).trans (add_le_add hea heb)
  have hab : |value a + value b| ≤ S := by
    have := abs_sub_abs_le_abs_sub (value a + value b) (A + B)
    linarith
  obtain ⟨hf, he⟩ := F64AddBounds.add_real_relative a b hfa hfb (hab.trans_lt hmax)
  refine ⟨hf, ?_⟩
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have he' := he.trans (mul_le_mul_of_nonneg_left hab hu)
  calc |value (Wasm.IEEE64.add a b) - (A + B)|
      ≤ |value (Wasm.IEEE64.add a b) - (value a + value b)| + |value a + value b - (A + B)| :=
        abs_sub_le _ _ _
    _ ≤ unitRoundoff64 * S + (ea + eb) := add_le_add he' hsum
    _ = ea + eb + unitRoundoff64 * S := by ring

theorem sub_approx {a b : UInt64} {A B ea eb : ℝ} (ha : Approx a A ea) (hb : Approx b B eb)
    (S : ℝ) (hS : |A - B| + ea + eb ≤ S) (hmax : S < 2 ^ 1023) :
    Approx (Wasm.IEEE64.sub a b) (A - B) (ea + eb + unitRoundoff64 * S) := by
  obtain ⟨hfa, hea⟩ := ha
  obtain ⟨hfb, heb⟩ := hb
  have hdiff : |value a - value b - (A - B)| ≤ ea + eb := by
    rw [show value a - value b - (A - B) = (value a - A) + -(value b - B) by ring]
    exact (abs_add_le _ _).trans (add_le_add hea (by rw [abs_neg]; exact heb))
  have hab : |value a - value b| ≤ S := by
    have := abs_sub_abs_le_abs_sub (value a - value b) (A - B)
    linarith
  obtain ⟨hf, he⟩ := F64AddBounds.sub_real_relative a b hfa hfb (hab.trans_lt hmax)
  refine ⟨hf, ?_⟩
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have he' := he.trans (mul_le_mul_of_nonneg_left hab hu)
  calc |value (Wasm.IEEE64.sub a b) - (A - B)|
      ≤ |value (Wasm.IEEE64.sub a b) - (value a - value b)| + |value a - value b - (A - B)| :=
        abs_sub_le _ _ _
    _ ≤ unitRoundoff64 * S + (ea + eb) := add_le_add he' hdiff
    _ = ea + eb + unitRoundoff64 * S := by ring

theorem mul_approx {a b : UInt64} {A B ea eb : ℝ} (ha : Approx a A ea) (hb : Approx b B eb)
    (MA MB : ℝ) (hA : |A| ≤ MA) (hB : |B| ≤ MB) (hmax : (MA + ea) * (MB + eb) < 2 ^ 1022) :
    Approx (Wasm.IEEE64.mul a b) (A * B)
      ((MA + ea) * eb + ea * MB + unitRoundoff64 * ((MA + ea) * (MB + eb)) +
        multiplicationUnderflowEpsilon) := by
  have hva := ha.abs_le hA
  have hvb := hb.abs_le hB
  obtain ⟨hfa, hea⟩ := ha
  obtain ⟨hfb, heb⟩ := hb
  have hab : |value a * value b| ≤ (MA + ea) * (MB + eb) := by
    rw [abs_mul]
    exact mul_le_mul hva hvb (abs_nonneg _) ((abs_nonneg _).trans hva)
  obtain ⟨hf, he⟩ := F64MulBounds.mul_real_mixed a b hfa hfb (hab.trans_lt hmax)
  refine ⟨hf, ?_⟩
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hprod : |value a * value b - A * B| ≤ (MA + ea) * eb + ea * MB := by
    rw [show value a * value b - A * B = value a * (value b - B) + (value a - A) * B by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul hva heb (abs_nonneg _) ((abs_nonneg _).trans hva)
    · rw [abs_mul]
      exact mul_le_mul hea hB (abs_nonneg _) ((abs_nonneg _).trans hea)
  have he' : |value (Wasm.IEEE64.mul a b) - value a * value b| ≤
      unitRoundoff64 * ((MA + ea) * (MB + eb)) + multiplicationUnderflowEpsilon := by
    have := mul_le_mul_of_nonneg_left hab hu
    linarith
  calc |value (Wasm.IEEE64.mul a b) - A * B|
      ≤ |value (Wasm.IEEE64.mul a b) - value a * value b| + |value a * value b - A * B| :=
        abs_sub_le _ _ _
    _ ≤ (unitRoundoff64 * ((MA + ea) * (MB + eb)) + multiplicationUnderflowEpsilon) +
        ((MA + ea) * eb + ea * MB) := add_le_add he' hprod
    _ = _ := by ring

/-- A sum of two words on the grid of `2 ^ s` scaled units is exact when it fits in 53 bits on
that grid. -/
theorem add_exact_grid (a b : UInt64) (ha : Finite a) (hb : Finite b) (s : Nat)
    (hs : s ≤ 2043) (hda : (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue a)
    (hdb : (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue b)
    (hbound : |Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b| ≤ 2 ^ 53 * 2 ^ s) :
    Finite (Wasm.IEEE64.add a b) ∧ value (Wasm.IEEE64.add a b) = value a + value b := by
  obtain ⟨za, hza⟩ := hda
  obtain ⟨zb, hzb⟩ := hdb
  have hsum : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = (za + zb) * 2 ^ s := by
    rw [hza, hzb]
    ring
  have hz : (za + zb).natAbs ≤ 2 ^ 53 := by
    have hp : (0 : Int) < 2 ^ s := by positivity
    rw [hsum, abs_mul, abs_of_pos hp] at hbound
    have h := le_of_mul_le_mul_right hbound hp
    have h2 : ((za + zb).natAbs : Int) ≤ ((2 ^ 53 : Nat) : Int) := by
      rw [Int.natCast_natAbs]
      push_cast
      exact h
    exact_mod_cast h2
  obtain ⟨hf, hv⟩ := F64GridExact.grid_add_exact a b ha hb (za + zb) s hsum hz hs
  refine ⟨hf, ?_⟩
  simp only [value, hv]
  push_cast
  ring

/-- A difference of two words on the grid of `2 ^ s` scaled units is exact when it fits in 53
bits on that grid. -/
theorem sub_exact_grid (a b : UInt64) (ha : Finite a) (hb : Finite b) (s : Nat)
    (hs : s ≤ 2043) (hda : (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue a)
    (hdb : (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue b)
    (hbound : |Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b| ≤ 2 ^ 53 * 2 ^ s) :
    Finite (Wasm.IEEE64.sub a b) ∧ value (Wasm.IEEE64.sub a b) = value a - value b := by
  obtain ⟨za, hza⟩ := hda
  obtain ⟨zb, hzb⟩ := hdb
  have hdiff : Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b = (za - zb) * 2 ^ s := by
    rw [hza, hzb]
    ring
  have hz : (za - zb).natAbs ≤ 2 ^ 53 := by
    have hp : (0 : Int) < 2 ^ s := by positivity
    rw [hdiff, abs_mul, abs_of_pos hp] at hbound
    have h := le_of_mul_le_mul_right hbound hp
    have h2 : ((za - zb).natAbs : Int) ≤ ((2 ^ 53 : Nat) : Int) := by
      rw [Int.natCast_natAbs]
      push_cast
      exact h
    exact_mod_cast h2
  obtain ⟨hf, hv⟩ := F64GridExact.sub_grid_exact a b ha hb (za - zb) s hdiff hz hs
  refine ⟨hf, ?_⟩
  simp only [value, hv]
  push_cast
  ring

#print axioms add_approx
#print axioms sub_approx
#print axioms mul_approx
#print axioms add_exact_grid
#print axioms sub_exact_grid

end LeanExe.ProofKit.F64ErrorTrack
