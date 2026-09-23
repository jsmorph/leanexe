import LeanExe.Models.Gpt2.Quantized.Kernel
import Mathlib.Tactic

namespace Project.ProofKit.QuantizedValidity
open LeanExe.Models.Gpt2.Quantized

theorem fold_all_iff (indices : List Nat) (predicate : Nat → Bool) (initial : Bool) :
    indices.foldl (fun valid index => valid && predicate index) initial = true ↔
      initial = true ∧ ∀ index ∈ indices, predicate index = true := by
  induction indices generalizing initial with
  | nil => simp
  | cons index indices ih => simp [ih, and_assoc]

theorem finiteWords_iff (bytes : ByteArray) (offset count : Nat) :
    finiteWords bytes offset count = true ↔
      ∀ index < count, finite (LeanExe.Packed.getUInt32LE! bytes (offset + index * 4)) = true := by
  simp only [finiteWords, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  change (List.range count).foldl _ true = true ↔ _
  rw [fold_all_iff]
  simp

theorem validCoefficients_iff (bytes : ByteArray) (offset count : Nat) :
    validCoefficients bytes offset count = true ↔
      ∀ index < count, bytes[offset + index]! ≠ 128 := by
  simp only [validCoefficients, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  change (List.range count).foldl _ true = true ↔ _
  rw [fold_all_iff]
  simp

theorem validScales_iff (bytes : ByteArray) (offset count : Nat) :
    validScales bytes offset count = true ↔
      ∀ index < count,
        0x00800000 ≤ LeanExe.Packed.getUInt32LE! bytes (offset + index * 4) ∧
        LeanExe.Packed.getUInt32LE! bytes (offset + index * 4) < 0x7F800000 := by
  simp only [validScales, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Bool.and_assoc]
  change (List.range count).foldl _ true = true ↔ _
  rw [fold_all_iff]
  simp

#print axioms finiteWords_iff
#print axioms validCoefficients_iff
#print axioms validScales_iff
end Project.ProofKit.QuantizedValidity
