import Project.Gpt2CachedStep.ExpNeg.SquareError

namespace Project.Gpt2CachedStep.ExpNeg.ForwardError
open Project.ProofKit CodeLib.IEEE32 LeanExe.Models.Gpt2

structure Ranges (input : UInt32) (mulBounds addBounds squareBounds : Nat → Nat) : Prop where
  reducedFinite : CodeLib.IEEE32.Finite (reducePrefix input 6).1
  reducedMagnitude : |value (reducePrefix input 6).1| ≤ 1
  reductionExact : ((2 ^ (reducePrefix input 6).2 : Nat) : ℝ) * value (reducePrefix input 6).1 = value input
  mulLower : ∀ i < 18, 173 ≤ mulBounds i
  mulUpper : ∀ i < 18, mulBounds i ≤ 425
  mulRange : ∀ i < 18,
    Wasm.IEEE32.scaledMagnitude (F32HornerError.compute (reducePrefix input 6).1 0x253413C3 PolynomialError.coefficient i) *
      Wasm.IEEE32.scaledMagnitude (reducePrefix input 6).1 < 2 ^ mulBounds i
  addUpper : ∀ i < 18, addBounds i ≤ 276
  addRange : ∀ i < 18,
    (Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits
      (F32HornerError.compute (reducePrefix input 6).1 0x253413C3 PolynomialError.coefficient i) (reducePrefix input 6).1) +
      Wasm.IEEE32.scaledValue (PolynomialError.coefficient i)).natAbs < 2 ^ addBounds i
  squareLower : ∀ i < (reducePrefix input 6).2, 173 ≤ squareBounds i
  squareUpper : ∀ i < (reducePrefix input 6).2, squareBounds i ≤ 425
  squareRange : ∀ i < (reducePrefix input 6).2,
    Wasm.IEEE32.scaledMagnitude (squarePrefix (expPolynomial (reducePrefix input 6).1) i) *
      Wasm.IEEE32.scaledMagnitude (squarePrefix (expPolynomial (reducePrefix input 6).1) i) < 2 ^ squareBounds i

noncomputable def error (input : UInt32) (mulBounds addBounds squareBounds : Nat → Nat) : ℝ :=
  if input > 0xC2800000 then 1 / 2 ^ 64 else
    SquareError.error (expPolynomial (reducePrefix input 6).1) (Real.exp (value (reducePrefix input 6).1))
      (PolynomialError.error (reducePrefix input 6).1 mulBounds addBounds) squareBounds (reducePrefix input 6).2

theorem cutoff_error (x : ℝ) (hx : x ≤ -64) : Real.exp x ≤ 1 / 2 ^ 64 := by
  have hExpOne : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hPow : (2 : ℝ) ^ 64 ≤ (Real.exp 1) ^ 64 := pow_le_pow_left₀ (by norm_num) hExpOne 64
  have hExp64 : (2 : ℝ) ^ 64 ≤ Real.exp 64 := by simpa only [← Real.exp_nat_mul, mul_one, Nat.cast_ofNat] using hPow
  calc
    Real.exp x ≤ Real.exp (-64) := Real.exp_le_exp.mpr hx
    _ = 1 / Real.exp 64 := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / 2 ^ 64 := one_div_le_one_div_of_le (by positivity) hExp64

theorem exp_error (input : UInt32) (mulBounds addBounds squareBounds : Nat → Nat)
    (hCutoff : input > 0xC2800000 → value input ≤ -64)
    (hRanges : input ≤ 0xC2800000 → Ranges input mulBounds addBounds squareBounds) :
    CodeLib.IEEE32.Finite (expNeg input) ∧
      |value (expNeg input) - Real.exp (value input)| ≤ error input mulBounds addBounds squareBounds := by
  rw [expNeg_eq]
  by_cases hBranch : input > 0xC2800000
  · simp only [hBranch, ite_true, error]
    constructor
    · change Wasm.IEEE32.isFinite 0 = true
      decide
    · have hz : value (0 : UInt32) = 0 := by norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
        Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
      rw [hz, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)]
      exact cutoff_error _ (hCutoff hBranch)
  · have hNot : input ≤ 0xC2800000 := by
      change input.toNat ≤ (0xC2800000 : UInt32).toNat
      change ¬(0xC2800000 : UInt32).toNat < input.toNat at hBranch
      omega
    have h := hRanges hNot
    have hPolynomial := PolynomialError.polynomial_error (reducePrefix input 6).1 mulBounds addBounds
      h.reducedFinite h.reducedMagnitude h.mulLower h.mulUpper h.mulRange h.addUpper h.addRange
    have hSquared := SquareError.exp_reconstruction (expPolynomial (reducePrefix input 6).1)
      (value (reducePrefix input 6).1) (PolynomialError.error (reducePrefix input 6).1 mulBounds addBounds)
      squareBounds (reducePrefix input 6).2 hPolynomial.1 hPolynomial.2 h.squareLower h.squareUpper h.squareRange
    rw [h.reductionExact] at hSquared
    simpa only [hBranch, ite_false, error] using hSquared

#print axioms cutoff_error
#print axioms exp_error
end Project.Gpt2CachedStep.ExpNeg.ForwardError
