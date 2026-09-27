import Project.ExpArm.PolynomialBounds
import Project.ProofKit.F64ApproximationSmall

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit.F64Horner

set_option exponentiation.threshold 4096

def correctionWord (r tail : UInt64) : UInt64 :=
  let r2 := Wasm.IEEE64.mul r r
  let p := Wasm.IEEE64.mul r2
    (Wasm.IEEE64.add 0x3FDFFFFFFFFFFDBD (Wasm.IEEE64.mul r 0x3FC555555555543C))
  let q := Wasm.IEEE64.mul (Wasm.IEEE64.mul r2 r2)
    (Wasm.IEEE64.add 0x3FA55555CF172B91 (Wasm.IEEE64.mul r 0x3F81111167A4D017))
  Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add tail r) p) q

theorem coefficient_magnitudes :
    |value 0x3FDFFFFFFFFFFDBD| ≤ 1/2 ∧ |value 0x3FC555555555543C| ≤ 1/6 ∧
    |value 0x3FA55555CF172B91| ≤ 1/20 ∧ |value 0x3F81111167A4D017| ≤ 1/100 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem correction_rounding (r tail : UInt64) (hf : Finite r) (ht : Finite tail)
    (hr : |value r| ≤ 3/1000) (hb : |value tail| ≤ 1/(2 : ℝ)^53) :
    Approximation (correctionWord r tail) (value tail + idealPolynomial (value r) - 1)
      (4/1000) (11/10000000000000000000) := by
  have ar := Approximation.exact r hf (3/1000) hr
  have atail := Approximation.exact tail ht (1/(2 : ℝ)^53) hb
  have a2 := Approximation.exact 0x3FDFFFFFFFFFFDBD (by rfl) (1/2) coefficient_magnitudes.1
  have a3 := Approximation.exact 0x3FC555555555543C (by rfl) (1/6) coefficient_magnitudes.2.1
  have a4 := Approximation.exact 0x3FA55555CF172B91 (by rfl) (1/20) coefficient_magnitudes.2.2.1
  have a5 := Approximation.exact 0x3F81111167A4D017 (by rfl) (1/100) coefficient_magnitudes.2.2.2
  have r2 := (ar.mul_mixed ar hr (bound := 9/1000000) (by norm_num) (by norm_num)).weaken
    (b' := 1/100000) (e' := 2/1000000000000000000000)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have v3 := (ar.mul_mixed a3 coefficient_magnitudes.2.1
    (bound := 1/2000) (by norm_num) (by norm_num)).weaken
    (b' := 501/1000000) (e' := 1/10000000000000000000)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have s3 := (a2.add_relative v3 (bound := 501/1000) (by norm_num) (by norm_num)).weaken
    (b' := 502/1000) (e' := 6/100000000000000000)
    (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
  have bs3 : |value 0x3FDFFFFFFFFFFDBD + value r*value 0x3FC555555555543C| ≤ 501/1000 := by
    have hm : |value r*value 0x3FC555555555543C| ≤ (3/1000)*(1/6) := by
      rw [abs_mul]
      exact mul_le_mul hr coefficient_magnitudes.2.1 (abs_nonneg _) (by norm_num)
    exact (abs_add_le _ _).trans ((add_le_add coefficient_magnitudes.1 hm).trans (by norm_num))
  have p := (r2.mul_mixed s3 bs3 (bound := 6/1000000) (by norm_num) (by norm_num)).weaken
    (b' := 7/1000000) (e' := 3/1000000000000000000000)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have br2 : |value r*value r| ≤ 9/1000000 := by
    rw [abs_mul]
    exact (mul_le_mul hr hr (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have r4 := (r2.mul_mixed r2 br2 (bound := 1/10000000000) (by norm_num) (by norm_num)).weaken
    (b' := 2/10000000000) (e' := 5/100000000000000000000000000)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have v5 := (ar.mul_mixed a5 coefficient_magnitudes.2.2.2
    (bound := 3/100000) (by norm_num) (by norm_num)).weaken
    (b' := 31/1000000) (e' := 4/1000000000000000000000)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have s5 := (a4.add_relative v5 (bound := 51/1000) (by norm_num) (by norm_num)).weaken
    (b' := 52/1000) (e' := 6/1000000000000000000)
    (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
  have bs5 : |value 0x3FA55555CF172B91 + value r*value 0x3F81111167A4D017| ≤ 51/1000 := by
    have hm : |value r*value 0x3F81111167A4D017| ≤ (3/1000)*(1/100) := by
      rw [abs_mul]
      exact mul_le_mul hr coefficient_magnitudes.2.2.2 (abs_nonneg _) (by norm_num)
    exact (abs_add_le _ _).trans ((add_le_add coefficient_magnitudes.2.2.1 hm).trans (by norm_num))
  have q := (r4.mul_mixed s5 bs5 (bound := 11/1000000000000) (by norm_num) (by norm_num)).weaken
    (b' := 12/1000000000000) (e' := 5/1000000000000000000000000000)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
  have s1 := (atail.add_relative ar (bound := 3001/1000000) (by norm_num) (by norm_num)).weaken
    (b' := 3002/1000000) (e' := 34/100000000000000000000)
    (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
  have s2 := (s1.add_relative p (bound := 3009/1000000) (by norm_num) (by norm_num)).weaken
    (b' := 3010/1000000) (e' := 68/100000000000000000000)
    (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
  have s3 := (s2.add_relative q (bound := 3011/1000000) (by norm_num) (by norm_num)).weaken
    (b' := 4/1000) (e' := 11/10000000000000000000)
    (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
  convert s3 using 1
  all_goals first | rfl | (dsimp [idealPolynomial]; ring)

#print axioms correction_rounding
end Project.ExpArm
