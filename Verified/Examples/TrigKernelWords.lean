import Verified.Examples.Trig
import Verified.Examples.TrigApprox
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.PolyBound

/-!
`Trig.kernelSin` and `Trig.kernelCos` on words, the bounds of their coefficients, and the error
of the inner polynomials `r` for `z` within `[0, 0.617]`, which contains `0.78541 ^ 2`.
-/

namespace Verified.Examples.TrigKernelWords

open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack PolyBound TrigApprox

def wS1 : UInt64 := 0xBFC5555555555549
def wS2 : UInt64 := 0x3F8111111110F8A6
def wS3 : UInt64 := 0xBF2A01A019C161D5
def wS4 : UInt64 := 0x3EC71DE357B1FE7D
def wS5 : UInt64 := 0xBE5AE5E68A2B9CEB
def wS6 : UInt64 := 0x3DE5D93A5ACFD57C
def wC1 : UInt64 := 0x3FA555555555554C
def wC2 : UInt64 := 0xBF56C16C16C15177
def wC3 : UInt64 := 0x3EFA01A019CB1590
def wC4 : UInt64 := 0xBE927E4F809C52AD
def wC5 : UInt64 := 0x3E21EE9EBDB4B1C4
def wC6 : UInt64 := 0xBDA8FAE9BE8838D4
def half : UInt64 := 0x3FE0000000000000
def one : UInt64 := 0x3FF0000000000000

/-- The polynomial `r` of `kernelSin` on words. -/
def sinR (z : UInt64) : UInt64 :=
  Wasm.IEEE64.add
    (Wasm.IEEE64.add wS2 (Wasm.IEEE64.mul z (Wasm.IEEE64.add wS3 (Wasm.IEEE64.mul z wS4))))
    (Wasm.IEEE64.mul (Wasm.IEEE64.mul z (Wasm.IEEE64.mul z z))
      (Wasm.IEEE64.add wS5 (Wasm.IEEE64.mul z wS6)))

/-- The polynomial `r` of `kernelCos` on words. -/
def cosR (z : UInt64) : UInt64 :=
  Wasm.IEEE64.add
    (Wasm.IEEE64.mul z
      (Wasm.IEEE64.add wC1 (Wasm.IEEE64.mul z (Wasm.IEEE64.add wC2 (Wasm.IEEE64.mul z wC3)))))
    (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul z z) (Wasm.IEEE64.mul z z))
      (Wasm.IEEE64.add wC4 (Wasm.IEEE64.mul z (Wasm.IEEE64.add wC5 (Wasm.IEEE64.mul z wC6)))))

/-- `kernelSin x y true` on words. -/
def sinTailW (x y : UInt64) : UInt64 :=
  let z := Wasm.IEEE64.mul x x
  let v := Wasm.IEEE64.mul z x
  Wasm.IEEE64.sub x
    (Wasm.IEEE64.sub
      (Wasm.IEEE64.sub
        (Wasm.IEEE64.mul z
          (Wasm.IEEE64.sub (Wasm.IEEE64.mul half y) (Wasm.IEEE64.mul v (sinR z)))) y)
      (Wasm.IEEE64.mul v wS1))

/-- `kernelSin x y false` on words. -/
def sinDirectW (x : UInt64) : UInt64 :=
  let z := Wasm.IEEE64.mul x x
  let v := Wasm.IEEE64.mul z x
  Wasm.IEEE64.add x (Wasm.IEEE64.mul v (Wasm.IEEE64.add wS1 (Wasm.IEEE64.mul z (sinR z))))

/-- `kernelCos x y` on words. -/
def cosW (x y : UInt64) : UInt64 :=
  let z := Wasm.IEEE64.mul x x
  let hz := Wasm.IEEE64.mul half z
  let w := Wasm.IEEE64.sub one hz
  Wasm.IEEE64.add w
    (Wasm.IEEE64.add (Wasm.IEEE64.sub (Wasm.IEEE64.sub one w) hz)
      (Wasm.IEEE64.sub (Wasm.IEEE64.mul z (cosR z)) (Wasm.IEEE64.mul x y)))

theorem const_bits :
    (Float.ofBits 0xBFC5555555555549).toBits = wS1 ∧
      (Float.ofBits 0x3F8111111110F8A6).toBits = wS2 ∧
      (Float.ofBits 0xBF2A01A019C161D5).toBits = wS3 ∧
      (Float.ofBits 0x3EC71DE357B1FE7D).toBits = wS4 ∧
      (Float.ofBits 0xBE5AE5E68A2B9CEB).toBits = wS5 ∧
      (Float.ofBits 0x3DE5D93A5ACFD57C).toBits = wS6 ∧
      (Float.ofBits 0x3FA555555555554C).toBits = wC1 ∧
      (Float.ofBits 0xBF56C16C16C15177).toBits = wC2 ∧
      (Float.ofBits 0x3EFA01A019CB1590).toBits = wC3 ∧
      (Float.ofBits 0xBE927E4F809C52AD).toBits = wC4 ∧
      (Float.ofBits 0x3E21EE9EBDB4B1C4).toBits = wC5 ∧
      (Float.ofBits 0xBDA8FAE9BE8838D4).toBits = wC6 ∧
      (0.5 : Float).toBits = half ∧ (1.0 : Float).toBits = one := by
  simp only [F64Bits.toBits_ofBits]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem kernelSin_tail_bits (x y : Float) :
    (Trig.kernelSin x y true).toBits = sinTailW x.toBits y.toBits := by
  obtain ⟨s1, s2, s3, s4, s5, s6, -, -, -, -, -, -, h, -⟩ := const_bits
  unfold Trig.kernelSin sinTailW sinR
  simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add, s1, s2, s3, s4, s5, s6,
    h, ite_true]

theorem kernelSin_direct_bits (x y : Float) :
    (Trig.kernelSin x y false).toBits = sinDirectW x.toBits := by
  obtain ⟨s1, s2, s3, s4, s5, s6, -⟩ := const_bits
  unfold Trig.kernelSin sinDirectW sinR
  simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add, s1, s2, s3, s4, s5, s6,
    Bool.false_eq_true, ite_false]

theorem kernelCos_bits (x y : Float) :
    (Trig.kernelCos x y).toBits = cosW x.toBits y.toBits := by
  obtain ⟨-, -, -, -, -, -, c1, c2, c3, c4, c5, c6, h, o⟩ := const_bits
  unfold Trig.kernelCos cosW cosR
  simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add, c1, c2, c3, c4, c5, c6,
    h, o]

theorem coeffs_checked :
    (-(1666667 / 10000000 : ℚ) ≤ ratOfWord wS1 ∧ ratOfWord wS1 ≤ 1666667 / 10000000) ∧
    (-(8334 / 1000000 : ℚ) ≤ ratOfWord wS2 ∧ ratOfWord wS2 ≤ 8334 / 1000000) ∧
    (-(1985 / 10000000 : ℚ) ≤ ratOfWord wS3 ∧ ratOfWord wS3 ≤ 1985 / 10000000) ∧
    (-(2756 / 1000000000 : ℚ) ≤ ratOfWord wS4 ∧ ratOfWord wS4 ≤ 2756 / 1000000000) ∧
    (-(2506 / 100000000000 : ℚ) ≤ ratOfWord wS5 ∧ ratOfWord wS5 ≤ 2506 / 100000000000) ∧
    (-(159 / 1000000000000 : ℚ) ≤ ratOfWord wS6 ∧ ratOfWord wS6 ≤ 159 / 1000000000000) ∧
    (-(41667 / 1000000 : ℚ) ≤ ratOfWord wC1 ∧ ratOfWord wC1 ≤ 41667 / 1000000) ∧
    (-(13889 / 10000000 : ℚ) ≤ ratOfWord wC2 ∧ ratOfWord wC2 ≤ 13889 / 10000000) ∧
    (-(2481 / 100000000 : ℚ) ≤ ratOfWord wC3 ∧ ratOfWord wC3 ≤ 2481 / 100000000) ∧
    (-(2756 / 10000000000 : ℚ) ≤ ratOfWord wC4 ∧ ratOfWord wC4 ≤ 2756 / 10000000000) ∧
    (-(2088 / 1000000000000 : ℚ) ≤ ratOfWord wC5 ∧ ratOfWord wC5 ≤ 2088 / 1000000000000) ∧
    (-(1136 / 100000000000000 : ℚ) ≤ ratOfWord wC6 ∧ ratOfWord wC6 ≤ 1136 / 100000000000000) ∧
    ratOfWord half = 1 / 2 ∧ ratOfWord one = 1 := by
  decide +kernel

theorem words_finite :
    Finite wS1 ∧ Finite wS2 ∧ Finite wS3 ∧ Finite wS4 ∧ Finite wS5 ∧ Finite wS6 ∧
      Finite wC1 ∧ Finite wC2 ∧ Finite wC3 ∧ Finite wC4 ∧ Finite wC5 ∧ Finite wC6 ∧
      Finite half ∧ Finite one := by
  unfold CodeLib.IEEE64.Finite
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem abs_of_rat (w : UInt64) (q : ℚ) (h : -q ≤ ratOfWord w ∧ ratOfWord w ≤ q) :
    |value w| ≤ q := by
  rw [← ratOfWord_cast, abs_le]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem value_half : value half = 1 / 2 := by
  rw [← ratOfWord_cast, coeffs_checked.2.2.2.2.2.2.2.2.2.2.2.2.1]
  norm_num

theorem value_one : value one = 1 := by
  rw [← ratOfWord_cast, coeffs_checked.2.2.2.2.2.2.2.2.2.2.2.2.2]
  norm_num

/-- The constants with their bounds. -/
theorem coeffs_AB :
    AB wS1 (value wS1) 0 (1666667 / 10000000) ∧ AB wS2 (value wS2) 0 (8334 / 1000000) ∧
      AB wS3 (value wS3) 0 (1985 / 10000000) ∧ AB wS4 (value wS4) 0 (2756 / 1000000000) ∧
      AB wS5 (value wS5) 0 (2506 / 100000000000) ∧ AB wS6 (value wS6) 0 (159 / 1000000000000) ∧
      AB wC1 (value wC1) 0 (41667 / 1000000) ∧ AB wC2 (value wC2) 0 (13889 / 10000000) ∧
      AB wC3 (value wC3) 0 (2481 / 100000000) ∧ AB wC4 (value wC4) 0 (2756 / 10000000000) ∧
      AB wC5 (value wC5) 0 (2088 / 1000000000000) ∧ AB wC6 (value wC6) 0 (1136 / 100000000000000) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, g1, g2, g3, g4, g5, g6, -, -⟩ := words_finite
  obtain ⟨b1, b2, b3, b4, b5, b6, d1, d2, d3, d4, d5, d6, -, -⟩ := coeffs_checked
  refine ⟨AB.const _ f1 _ ?_, AB.const _ f2 _ ?_, AB.const _ f3 _ ?_, AB.const _ f4 _ ?_,
    AB.const _ f5 _ ?_, AB.const _ f6 _ ?_, AB.const _ g1 _ ?_, AB.const _ g2 _ ?_,
    AB.const _ g3 _ ?_, AB.const _ g4 _ ?_, AB.const _ g5 _ ?_, AB.const _ g6 _ ?_⟩
  · have h := abs_of_rat _ _ b1
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ b2
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ b3
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ b4
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ b5
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ b6
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ d1
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ d2
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ d3
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ d4
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ d5
    push_cast at h
    linarith
  · have h := abs_of_rat _ _ d6
    push_cast at h
    linarith

set_option exponentiation.threshold 1200 in
/-- The polynomial of `kernelSin` for `z` within `u · 0.617 + η` of `Z` in `[0, 0.617]`. -/
theorem sinR_AB (z : UInt64) (Z : ℝ)
    (hz : AB z Z (unitRoundoff64 * (617 / 1000) + multiplicationUnderflowEpsilon) (617 / 1000)) :
    AB (sinR z)
      (value wS2 + Z * (value wS3 + Z * value wS4) + Z * (Z * Z) * (value wS5 + Z * value wS6))
      (unitRoundoff64 / 32) (85 / 10000) := by
  obtain ⟨-, c2, c3, c4, c5, c6, -⟩ := coeffs_AB
  have a4 := AB.mul hz c4 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num)
  have a3 := AB.add c3 a4 (by norm_num)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a3' := AB.mul hz a3 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a2 := AB.add c2 a3' (by norm_num)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have w := AB.mul hz hz (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have zw := AB.mul hz w (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a6 := AB.mul hz c6 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num)
  have a5 := AB.add c5 a6 (by norm_num)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have b5 := AB.mul zw a5 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have r := AB.add a2 b5 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  exact r.mono (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num)

set_option exponentiation.threshold 1200 in
/-- The polynomial of `kernelCos` for `z` within `u · 0.617 + η` of `Z` in `[0, 0.617]`. -/
theorem cosR_AB (z : UInt64) (Z : ℝ)
    (hz : AB z Z (unitRoundoff64 * (617 / 1000) + multiplicationUnderflowEpsilon) (617 / 1000)) :
    AB (cosR z)
      (Z * (value wC1 + Z * (value wC2 + Z * value wC3)) +
        Z * Z * (Z * Z) * (value wC4 + Z * (value wC5 + Z * value wC6)))
      (3 * unitRoundoff64 / 25) (263 / 10000) := by
  obtain ⟨-, -, -, -, -, -, c1, c2, c3, c4, c5, c6⟩ := coeffs_AB
  have a3 := AB.mul hz c3 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num)
  have a2 := AB.add c2 a3 (by norm_num)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a2' := AB.mul hz a2 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a1 := AB.add c1 a2' (by norm_num)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have p1 := AB.mul hz a1 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have w := AB.mul hz hz (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have ww := AB.mul w w (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a6 := AB.mul hz c6 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num)
  have a5 := AB.add c5 a6 (by norm_num)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a5' := AB.mul hz a5 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have a4 := AB.add c4 a5' (by norm_num)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have p2 := AB.mul ww a4 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have r := AB.add p1 p2 (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  exact r.mono (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) (by norm_num)

#print axioms const_bits
#print axioms kernelSin_tail_bits
#print axioms kernelSin_direct_bits
#print axioms kernelCos_bits
#print axioms coeffs_checked
#print axioms coeffs_AB
#print axioms sinR_AB
#print axioms cosR_AB

end Verified.Examples.TrigKernelWords
