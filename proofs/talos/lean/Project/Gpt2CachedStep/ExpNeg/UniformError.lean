import Project.Gpt2CachedStep.ExpNeg.ForwardError
import Project.ProofKit.F32Absolute

set_option exponentiation.threshold 512

namespace Project.Gpt2CachedStep.ExpNeg.UniformError
open Project.ProofKit CodeLib.IEEE32 LeanExe.Models.Gpt2

noncomputable def hornerUpper (count : Nat) : ℝ :=
  1 / 2 ^ 24 + count * (4 / 2 ^ 24)

theorem horner_nonnegative (count : Nat) : 0 ≤ hornerUpper count := by
  unfold hornerUpper
  positivity

theorem horner_upper (input : UInt32) (count : Nat) (hx : |value input| ≤ 1) :
    F32HornerError.error input 0x253413C3 PolynomialError.coefficient (value input) 0
      PolynomialError.coefficientError (fun _ => PolynomialError.coefficientError)
      (fun _ => 299) (fun _ => 151) count ≤ hornerUpper count := by
  induction count with
  | zero => norm_num [F32HornerError.error, hornerUpper, PolynomialError.coefficientError]
  | succ count ih =>
    have hm := mul_le_mul ih hx (abs_nonneg (value input)) (horner_nonnegative count)
    rw [mul_one] at hm
    simp only [F32HornerError.error, mul_zero, zero_add]
    norm_num [F32AdditionBounds.epsilon, F32MultiplicationBounds.epsilon,
      PolynomialError.coefficientError, hornerUpper] at hm ⊢
    linarith

noncomputable def polynomialUpper : ℝ := hornerUpper 18 + 1 / 100000000000000000

theorem polynomial_upper (input : UInt32) (hx : |value input| ≤ 1) :
    PolynomialError.error input (fun _ => 299) (fun _ => 151) ≤ polynomialUpper := by
  exact add_le_add (horner_upper input 18 hx) le_rfl

noncomputable def squareUpper : Nat → ℝ
  | 0 => polynomialUpper
  | count + 1 => 1 / 2 ^ 24 + 3 * squareUpper count

theorem square_nonnegative (count : Nat) : 0 ≤ squareUpper count := by
  induction count with
  | zero => norm_num [squareUpper, polynomialUpper, hornerUpper]
  | succ count ih => simp only [squareUpper]; positivity

theorem square_input_magnitude (a : UInt32)
    (h : Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude a < 2 ^ 299) :
    |value a| ≤ 2 := by
  have hm : Wasm.IEEE32.scaledMagnitude a ≤ 2 ^ 150 := by
    by_contra! hn
    have hp := Nat.mul_le_mul hn.le hn.le
    norm_num at hp
    norm_num at h
    omega
  rw [F32Order.abs_value_scaledMagnitude]
  apply (div_le_iff₀ (by positivity)).mpr
  have hr : (Wasm.IEEE32.scaledMagnitude a : ℝ) ≤ 2 ^ 150 := by exact_mod_cast hm
  norm_num at hr ⊢
  exact hr

theorem square_upper (input : UInt32) (reference initial : ℝ) (count : Nat)
    (hr : |reference| ≤ 1) (he : initial ≤ polynomialUpper)
    (hm : ∀ i < count, |value (squarePrefix input i)| ≤ 2) :
    SquareError.error input reference initial (fun _ => 299) count ≤ squareUpper count := by
  induction count with
  | zero => exact he
  | succ count ih =>
    have hp := ih (fun i hi => hm i (by omega))
    have hpow : |reference ^ (2 ^ count)| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) hr
    have hc := hm count (by omega)
    have hleft := mul_le_mul hp hc (abs_nonneg (value (squarePrefix input count)))
      (square_nonnegative count)
    have hright := mul_le_mul hp hpow (abs_nonneg _) (square_nonnegative count)
    simp only [SquareError.error, squareUpper]
    norm_num [F32MultiplicationBounds.epsilon] at hleft hright ⊢
    nlinarith

theorem error_upper (input : UInt32) (hneg : value input ≤ 0)
    (h : input ≤ 0xC2800000 → ForwardError.Ranges input (fun _ => 299) (fun _ => 151) (fun _ => 299)) :
    ForwardError.error input (fun _ => 299) (fun _ => 151) (fun _ => 299) ≤ 1 / 300 := by
  unfold ForwardError.error
  split_ifs with hc
  · norm_num
  · have hb : input ≤ 0xC2800000 := by
      change input.toNat ≤ (0xC2800000 : UInt32).toNat
      change ¬(0xC2800000 : UInt32).toNat < input.toNat at hc
      omega
    have hr := h hb
    have heq := hr.reductionExact
    have hpos : (0 : ℝ) < (2 ^ (reducePrefix input 6).2 : Nat) := by positivity
    have hx : value (reducePrefix input 6).1 ≤ 0 := by nlinarith
    have he : |Real.exp (value (reducePrefix input 6).1)| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr hx
    have hs := square_upper (expPolynomial (reducePrefix input 6).1)
      (Real.exp (value (reducePrefix input 6).1)) _ (reducePrefix input 6).2 he
      (polynomial_upper _ hr.reducedMagnitude)
      (fun i hi => square_input_magnitude _ (hr.squareRange i hi))
    apply hs.trans
    have hn := reducePrefix_count input 6
    generalize (reducePrefix input 6).2 = count at hn ⊢
    interval_cases count <;> norm_num [squareUpper, polynomialUpper, hornerUpper]

#print axioms error_upper
end Project.Gpt2CachedStep.ExpNeg.UniformError
