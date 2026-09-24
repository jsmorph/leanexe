import LeanExe.Correct.Scalar64.Arithmetic
import Init.Data.UInt.Bitwise

namespace LeanExe.Correct.Scalar64
open LeanExe.TypeSafety

/-- Relate the independent arithmetic bit specification to Lean's bitwise words. -/
theorem bitwise64_eq (operation : Bool → Bool → Bool) (zero : operation false false = false)
    (a b : UInt64) :
    bitwiseBits 64 operation a.toNat b.toNat = Nat.bitwise operation a.toNat b.toNat := by
  apply eq_of_bitAt_eq 64 _ _ (bitwiseBits_bounded ..)
    (Nat.bitwise_lt_two_pow a.toNat_lt b.toNat_lt)
  intro index inside
  rw [bitwiseBits_bitAt _ _ _ _ _ inside]
  simp only [bitAt, ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_bitwise zero]

theorem Runs.bitXor (leftRun : Runs program left env (encodeWord a))
    (rightRun : Runs program right env (encodeWord b)) :
    Runs program (.wordBin .w64 .bitXor left right) env (encodeWord (a ^^^ b)) := by
  have same : bitwiseBits 64 Bool.xor a.toNat b.toNat = (a ^^^ b).toNat := by
    apply eq_of_bitAt_eq 64 _ _ (bitwiseBits_bounded ..) (a ^^^ b).toNat_lt
    intro index inside
    rw [bitwiseBits_bitAt _ _ _ _ _ inside, UInt64.toNat_xor]
    simp only [bitAt, ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_xor]
  simpa only [encodeWord, evalWordBin, WordWidth.bits, same] using
    Runs.bin (op := .bitXor) leftRun rightRun

theorem Runs.bitAnd (leftRun : Runs program left env (encodeWord a))
    (rightRun : Runs program right env (encodeWord b)) :
    Runs program (.wordBin .w64 .bitAnd left right) env (encodeWord (a &&& b)) := by
  have same : bitwiseBits 64 (· && ·) a.toNat b.toNat = (a &&& b).toNat := by
    apply eq_of_bitAt_eq 64 _ _ (bitwiseBits_bounded ..) (a &&& b).toNat_lt
    intro index inside
    rw [bitwiseBits_bitAt _ _ _ _ _ inside, UInt64.toNat_and]
    simp only [bitAt, ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_and]
  simpa only [encodeWord, evalWordBin, WordWidth.bits, same] using
    Runs.bin (op := .bitAnd) leftRun rightRun

theorem Runs.bitOr (leftRun : Runs program left env (encodeWord a))
    (rightRun : Runs program right env (encodeWord b)) :
    Runs program (.wordBin .w64 .bitOr left right) env (encodeWord (a ||| b)) := by
  have same : bitwiseBits 64 (· || ·) a.toNat b.toNat = (a ||| b).toNat := by
    apply eq_of_bitAt_eq 64 _ _ (bitwiseBits_bounded ..) (a ||| b).toNat_lt
    intro index inside
    rw [bitwiseBits_bitAt _ _ _ _ _ inside, UInt64.toNat_or]
    simp only [bitAt, ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_or]
  simpa only [encodeWord, evalWordBin, WordWidth.bits, same] using
    Runs.bin (op := .bitOr) leftRun rightRun

theorem Runs.shiftRight (leftRun : Runs program left env (encodeWord a))
    (rightRun : Runs program right env (encodeWord b)) :
    Runs program (.wordBin .w64 .shiftRight left right) env (encodeWord (a >>> b)) := by
  simpa only [encodeWord, evalWordBin, shiftAmount, WordWidth.bits,
    UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] using
    Runs.bin (op := .shiftRight) leftRun rightRun

theorem Runs.shiftLeft (leftRun : Runs program left env (encodeWord a))
    (rightRun : Runs program right env (encodeWord b)) :
    Runs program (.wordBin .w64 .shiftLeft left right) env (encodeWord (a <<< b)) := by
  simpa only [encodeWord, evalWordBin, shiftAmount, WordWidth.bits, WordWidth.modulus,
    UInt64.toNat_shiftLeft, Nat.shiftLeft_eq] using
    Runs.bin (op := .shiftLeft) leftRun rightRun

end LeanExe.Correct.Scalar64
