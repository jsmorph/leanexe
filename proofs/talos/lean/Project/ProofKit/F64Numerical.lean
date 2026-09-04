import CodeLib.Numerical.Kernels

/-!
# Reusable binary64 Horner error bounds

This module fills the binary64 counterpart of CodeLib's binary32 Horner-stage
lemma and composes two stages on the guarded half-unit domain.  Every operation
is interpreted by Talos's pure IEEE-754 model; native Lean `Float` evaluation
is outside the proof boundary.
-/

namespace Project.ProofKit.F64Numerical

open Wasm

set_option exponentiation.threshold 4096

/-- One modeled binary64 Horner multiply-then-add stage. -/
def hornerStepBits (accumulator x coefficient : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.mul accumulator x) coefficient

/-- Two explicitly rounded binary64 Horner stages for a quadratic. -/
def horner2Bits (x c₂ c₁ c₀ : UInt64) : UInt64 :=
  hornerStepBits (hornerStepBits c₂ x c₁) x c₀

/-- A finite binary64 Horner stage contributes at most one multiplication
error and one addition error when its operands and product stay in the unit
interval. -/
theorem horner64_step_real_error (accumulator x coefficient : UInt64)
    (haccumulator : CodeLib.IEEE64.Finite accumulator)
    (hx : CodeLib.IEEE64.Finite x)
    (hcoefficient : CodeLib.IEEE64.Finite coefficient)
    (haccumulatorBound : |CodeLib.IEEE64.value accumulator| ≤ 1)
    (hxBound : |CodeLib.IEEE64.value x| ≤ 1)
    (hcoefficientBound : |CodeLib.IEEE64.value coefficient| ≤ 1)
    (hproductBound :
      |CodeLib.IEEE64.value (Wasm.IEEE64.mul accumulator x)| ≤ 1) :
    CodeLib.IEEE64.Finite (hornerStepBits accumulator x coefficient) ∧
      |CodeLib.IEEE64.value (hornerStepBits accumulator x coefficient) -
          (CodeLib.IEEE64.value accumulator * CodeLib.IEEE64.value x +
            CodeLib.IEEE64.value coefficient)| ≤
        2 * CodeLib.Numerical.Kernels.f64Epsilon := by
  unfold hornerStepBits
  let product := Wasm.IEEE64.mul accumulator x
  have hproduct := CodeLib.IEEE64.mul_real_error accumulator x
    haccumulator hx haccumulatorBound hxBound
  change CodeLib.IEEE64.Finite product ∧
    |CodeLib.IEEE64.value product -
      CodeLib.IEEE64.value accumulator * CodeLib.IEEE64.value x| ≤
        CodeLib.IEEE64.multiplicationEpsilon at hproduct
  have hsum := CodeLib.IEEE64.add_real_error product coefficient
    hproduct.1 hcoefficient hproductBound hcoefficientBound
  change CodeLib.IEEE64.Finite (Wasm.IEEE64.add product coefficient) ∧
    |CodeLib.IEEE64.value (Wasm.IEEE64.add product coefficient) -
      (CodeLib.IEEE64.value product +
        CodeLib.IEEE64.value coefficient)| ≤
        CodeLib.IEEE64.arithmeticEpsilon at hsum
  have hproductError :
      |CodeLib.IEEE64.value product -
        CodeLib.IEEE64.value accumulator * CodeLib.IEEE64.value x| ≤
          CodeLib.Numerical.Kernels.f64Epsilon := by
    simpa [CodeLib.Numerical.Kernels.f64Epsilon,
      CodeLib.IEEE64.multiplicationEpsilon] using hproduct.2
  have hsumError :
      |CodeLib.IEEE64.value (Wasm.IEEE64.add product coefficient) -
        (CodeLib.IEEE64.value product +
          CodeLib.IEEE64.value coefficient)| ≤
          CodeLib.Numerical.Kernels.f64Epsilon := by
    simpa [CodeLib.Numerical.Kernels.f64Epsilon,
      CodeLib.IEEE64.arithmeticEpsilon] using hsum.2
  have hsecond :
      |(0 : ℝ) -
        ((CodeLib.IEEE64.value accumulator * CodeLib.IEEE64.value x +
            CodeLib.IEEE64.value coefficient) -
          (CodeLib.IEEE64.value product +
            CodeLib.IEEE64.value coefficient))| ≤
          CodeLib.Numerical.Kernels.f64Epsilon := by
    rw [show (0 : ℝ) -
        ((CodeLib.IEEE64.value accumulator * CodeLib.IEEE64.value x +
            CodeLib.IEEE64.value coefficient) -
          (CodeLib.IEEE64.value product +
            CodeLib.IEEE64.value coefficient)) =
        CodeLib.IEEE64.value product -
          CodeLib.IEEE64.value accumulator * CodeLib.IEEE64.value x by ring]
    exact hproductError
  have hcomposed := CodeLib.Numerical.sum_perturbations
    (x := CodeLib.IEEE64.value (Wasm.IEEE64.add product coefficient))
    (x₀ := CodeLib.IEEE64.value product + CodeLib.IEEE64.value coefficient)
    (y := 0)
    (y₀ :=
      (CodeLib.IEEE64.value accumulator * CodeLib.IEEE64.value x +
        CodeLib.IEEE64.value coefficient) -
      (CodeLib.IEEE64.value product + CodeLib.IEEE64.value coefficient))
    hsumError hsecond
  change CodeLib.IEEE64.Finite (Wasm.IEEE64.add product coefficient) ∧ _
  constructor
  · exact hsum.1
  · rw [show
      CodeLib.IEEE64.value (Wasm.IEEE64.add product coefficient) -
          (CodeLib.IEEE64.value accumulator * CodeLib.IEEE64.value x +
            CodeLib.IEEE64.value coefficient) =
        (CodeLib.IEEE64.value (Wasm.IEEE64.add product coefficient) + 0) -
          ((CodeLib.IEEE64.value product +
              CodeLib.IEEE64.value coefficient) +
            ((CodeLib.IEEE64.value accumulator * CodeLib.IEEE64.value x +
                CodeLib.IEEE64.value coefficient) -
              (CodeLib.IEEE64.value product +
                CodeLib.IEEE64.value coefficient))) by ring]
    convert hcomposed using 1 <;> ring

/-- On the half-unit input domain, the explicitly staged quadratic Horner
evaluation is finite and differs from the exact real polynomial by at most
`3 * 2^-52`.  The first stage contributes two units, but its error is
attenuated by `|x| ≤ 1/2` before the second two-unit stage is added. -/
theorem horner2_real_error_of_half (x c₂ c₁ c₀ : UInt64)
    (hx : CodeLib.IEEE64.Finite x)
    (hc₂ : CodeLib.IEEE64.Finite c₂)
    (hc₁ : CodeLib.IEEE64.Finite c₁)
    (hc₀ : CodeLib.IEEE64.Finite c₀)
    (hxBound : |CodeLib.IEEE64.value x| ≤ (1 : ℝ) / 2)
    (hc₂Bound : |CodeLib.IEEE64.value c₂| ≤ (1 : ℝ) / 2)
    (hc₁Bound : |CodeLib.IEEE64.value c₁| ≤ (1 : ℝ) / 2)
    (hc₀Bound : |CodeLib.IEEE64.value c₀| ≤ (1 : ℝ) / 2) :
    CodeLib.IEEE64.Finite (horner2Bits x c₂ c₁ c₀) ∧
      |CodeLib.IEEE64.value (horner2Bits x c₂ c₁ c₀) -
          ((CodeLib.IEEE64.value c₂ * CodeLib.IEEE64.value x +
              CodeLib.IEEE64.value c₁) * CodeLib.IEEE64.value x +
            CodeLib.IEEE64.value c₀)| ≤
        3 * CodeLib.Numerical.Kernels.f64Epsilon := by
  let first := hornerStepBits c₂ x c₁
  have hxUnit : |CodeLib.IEEE64.value x| ≤ (1 : ℝ) :=
    hxBound.trans (by norm_num)
  have hc₂Unit : |CodeLib.IEEE64.value c₂| ≤ (1 : ℝ) :=
    hc₂Bound.trans (by norm_num)
  have hc₁Unit : |CodeLib.IEEE64.value c₁| ≤ (1 : ℝ) :=
    hc₁Bound.trans (by norm_num)
  have hc₀Unit : |CodeLib.IEEE64.value c₀| ≤ (1 : ℝ) :=
    hc₀Bound.trans (by norm_num)
  have hfirstProductExact :
      |CodeLib.IEEE64.value c₂ * CodeLib.IEEE64.value x| ≤ (1 : ℝ) / 4 := by
    rw [abs_mul]
    calc
      |CodeLib.IEEE64.value c₂| * |CodeLib.IEEE64.value x| ≤
          ((1 : ℝ) / 2) * ((1 : ℝ) / 2) :=
        mul_le_mul hc₂Bound hxBound (abs_nonneg _) (by norm_num)
      _ = (1 : ℝ) / 4 := by ring
  have hfirstProductHeadroom :
      |CodeLib.IEEE64.value c₂ * CodeLib.IEEE64.value x| +
          CodeLib.Numerical.Kernels.f64Epsilon ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) / 4 + CodeLib.Numerical.Kernels.f64Epsilon :=
        add_le_add hfirstProductExact (le_refl _)
      _ ≤ 1 := by
        norm_num [CodeLib.Numerical.Kernels.f64Epsilon]
  have hfirstProductBound :=
    CodeLib.Numerical.Kernels.mul64_value_bound_of_headroom c₂ x
      hc₂ hx hc₂Unit hxUnit hfirstProductHeadroom
  have hfirst :
      CodeLib.IEEE64.Finite first ∧
        |CodeLib.IEEE64.value first -
            (CodeLib.IEEE64.value c₂ * CodeLib.IEEE64.value x +
              CodeLib.IEEE64.value c₁)| ≤
          2 * CodeLib.Numerical.Kernels.f64Epsilon := by
    simpa [first] using
      (horner64_step_real_error c₂ x c₁ hc₂ hx hc₁
        hc₂Unit hxUnit hc₁Unit hfirstProductBound)
  have hfirstExact :
      |CodeLib.IEEE64.value c₂ * CodeLib.IEEE64.value x +
          CodeLib.IEEE64.value c₁| ≤ (3 : ℝ) / 4 := by
    calc
      _ ≤ |CodeLib.IEEE64.value c₂ * CodeLib.IEEE64.value x| +
          |CodeLib.IEEE64.value c₁| := abs_add_le _ _
      _ ≤ (1 : ℝ) / 4 + (1 : ℝ) / 2 :=
        add_le_add hfirstProductExact hc₁Bound
      _ = (3 : ℝ) / 4 := by ring
  have hfirstHeadroom :
      |CodeLib.IEEE64.value c₂ * CodeLib.IEEE64.value x +
          CodeLib.IEEE64.value c₁| +
          2 * CodeLib.Numerical.Kernels.f64Epsilon ≤ 1 := by
    calc
      _ ≤ (3 : ℝ) / 4 +
          2 * CodeLib.Numerical.Kernels.f64Epsilon :=
        add_le_add hfirstExact (le_refl _)
      _ ≤ 1 := by
        norm_num [CodeLib.Numerical.Kernels.f64Epsilon]
  have hfirstBound : |CodeLib.IEEE64.value first| ≤ (1 : ℝ) :=
    CodeLib.Numerical.abs_le_of_error_headroom hfirst.2 hfirstHeadroom
  have hsecondProductExact :
      |CodeLib.IEEE64.value first * CodeLib.IEEE64.value x| ≤
          (1 : ℝ) / 2 := by
    rw [abs_mul]
    calc
      |CodeLib.IEEE64.value first| * |CodeLib.IEEE64.value x| ≤
          (1 : ℝ) * ((1 : ℝ) / 2) :=
        mul_le_mul hfirstBound hxBound (abs_nonneg _) (by norm_num)
      _ = (1 : ℝ) / 2 := by ring
  have hsecondProductHeadroom :
      |CodeLib.IEEE64.value first * CodeLib.IEEE64.value x| +
          CodeLib.Numerical.Kernels.f64Epsilon ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) / 2 + CodeLib.Numerical.Kernels.f64Epsilon :=
        add_le_add hsecondProductExact (le_refl _)
      _ ≤ 1 := by
        norm_num [CodeLib.Numerical.Kernels.f64Epsilon]
  have hsecondProductBound :=
    CodeLib.Numerical.Kernels.mul64_value_bound_of_headroom first x
      hfirst.1 hx hfirstBound hxUnit hsecondProductHeadroom
  have hsecond := horner64_step_real_error first x c₀
    hfirst.1 hx hc₀ hfirstBound hxUnit hc₀Unit hsecondProductBound
  constructor
  · simpa [horner2Bits, first] using hsecond.1
  · have htotal := CodeLib.Numerical.horner_two_step
      (x := CodeLib.IEEE64.value x)
      (a := CodeLib.IEEE64.value c₂)
      (b := CodeLib.IEEE64.value c₁)
      (c := CodeLib.IEEE64.value c₀)
      (r₁ := CodeLib.IEEE64.value first)
      (r₂ := CodeLib.IEEE64.value (hornerStepBits first x c₀))
      (e₁ := 2 * CodeLib.Numerical.Kernels.f64Epsilon)
      (e₂ := 2 * CodeLib.Numerical.Kernels.f64Epsilon)
      (M := (1 : ℝ) / 2)
      hxBound hfirst.2 hsecond.2
    calc
      |CodeLib.IEEE64.value (horner2Bits x c₂ c₁ c₀) -
          ((CodeLib.IEEE64.value c₂ * CodeLib.IEEE64.value x +
              CodeLib.IEEE64.value c₁) * CodeLib.IEEE64.value x +
            CodeLib.IEEE64.value c₀)| ≤
          2 * CodeLib.Numerical.Kernels.f64Epsilon +
            (2 * CodeLib.Numerical.Kernels.f64Epsilon) * ((1 : ℝ) / 2) := by
              simpa [horner2Bits, first] using htotal
      _ = 3 * CodeLib.Numerical.Kernels.f64Epsilon := by ring

#print axioms horner64_step_real_error
#print axioms horner2_real_error_of_half

end Project.ProofKit.F64Numerical
