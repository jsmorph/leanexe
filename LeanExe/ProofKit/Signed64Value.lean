import LeanExe.ProofKit.Signed64Wasm
import LeanExe.ProofKit.F64GridExact

/-!
The integers of `Int64` values that programs compute from words, and the exact conversion of
small integers to binary64.  A program that writes a signed quantity as an `Int64`, such as the
exponent `k = (int64_t) tmp >> 52` of a logarithm, gets its integer from three facts:
`toInt_toInt64` reads a word as a signed integer, `toInt_of_word` gives the integer of a value whose
word is known modulo `2 ^ 64` and whose integer lies in the range of `Int64`, and
`toInt_shiftRight` states the arithmetic shift as the floor of a division by a power of two.
`toFloat_exact` then gives `k.toFloat` the value `k.toInt` for `|k.toInt| ≤ 2 ^ 53`, through
`Signed64.toBits_int64ToFloat`, so a proof about such a program never restates the word forms of
`Signed64` and `Signed64Float`.
-/

namespace LeanExe.ProofKit.Signed64Value
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

/-- The integer of a word read as an `Int64`. -/
theorem toInt_toInt64 (w : UInt64) :
    w.toInt64.toInt = if w.toNat < 2 ^ 63 then (w.toNat : Int) else (w.toNat : Int) - 2 ^ 64 :=
  Signed64.toInt_cond w.toInt64

/-- An `Int64` whose word is `n` modulo `2 ^ 64`, for `n` in the range of `Int64`, has the
integer `n`. -/
theorem toInt_of_word (a : Int64) (n : Int) (h1 : -2 ^ 63 ≤ n) (h2 : n < 2 ^ 63)
    (h : (a.toUInt64.toNat : Int) = n % 2 ^ 64) : a.toInt = n := by
  have hlt := a.toUInt64.toNat_lt
  rw [Signed64.toInt_cond]
  split <;> omega

/-- The word of an `Int64` is its integer modulo `2 ^ 64`. -/
theorem toNat_toUInt64 (a : Int64) : (a.toUInt64.toNat : Int) = a.toInt % 2 ^ 64 := by
  have hlt := a.toUInt64.toNat_lt
  rw [Signed64.toInt_cond]
  split <;> omega

/-- The arithmetic shift right by an amount below 64 is the floor of the division by
`2 ^ amount`. -/
theorem toInt_shiftRight (a b : Int64) (hb : b.toUInt64.toNat < 64) :
    (a >>> b).toInt = a.toInt / 2 ^ b.toUInt64.toNat := by
  show (BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 64)).toInt = a.toBitVec.toInt / _
  have hn : b.toBitVec.toNat = b.toUInt64.toNat := rfl
  rw [BitVec.toInt_sshiftRight', Signed64.smod_toNat, hn, Nat.mod_eq_of_lt hb,
    Int.shiftRight_eq_div_pow]
  norm_cast

/-- `Int64.toFloat` is exact on integers of magnitude at most `2 ^ 53`. -/
theorem toFloat_exact (a : Int64) (h : a.toInt.natAbs ≤ 2 ^ 53) :
    Finite a.toFloat.toBits ∧ value a.toFloat.toBits = (a.toInt : ℝ) := by
  rw [Signed64.toBits_int64ToFloat]
  have hg := F64GridExact.signed_grid_packing_exact a.toInt 1074 h (by norm_num)
  refine ⟨hg.1, ?_⟩
  have h2 : (2 : ℝ) ^ 1074 ≠ 0 := by positivity
  rw [value, Wasm.IEEE64.fromInt, hg.2, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    mul_div_assoc, div_self h2, mul_one]

#print axioms toInt_toInt64
#print axioms toInt_of_word
#print axioms toNat_toUInt64
#print axioms toInt_shiftRight
#print axioms toFloat_exact

end LeanExe.ProofKit.Signed64Value
