import Verified.Examples.Exp2Approximation
import LeanExe.ProofKit.F64ErrorTrack
import LeanExe.ProofKit.F64Bits

/-!
The evaluation of `Exp2.exp2Core`'s polynomial on words: `tmp = t + r C1 + r ^ 2 (C2 + r C3) +
r ^ 4 (C4 + r C5)` with every operation rounded, in the order of the code.  For `|r| ≤ 1/256` and
a table tail `|t| ≤ 2 ^ -53`, `tmp` is within `2 ^ -56` of `t + 2 ^ r - 1` and at most `1/64` in
magnitude.
-/

namespace Verified.Examples.Exp2Evaluation
open CodeLib.IEEE64
open LeanExe.ProofKit F64ErrorTrack Exp2Approximation

set_option exponentiation.threshold 4096

/-- The polynomial evaluation of `Exp2.exp2Core` on the residual `r` and the tail `t`. -/
def evaluation (r t : UInt64) : UInt64 :=
  let r2 := Wasm.IEEE64.mul r r
  Wasm.IEEE64.add
    (Wasm.IEEE64.add (Wasm.IEEE64.add t (Wasm.IEEE64.mul r c1))
      (Wasm.IEEE64.mul r2 (Wasm.IEEE64.add c2 (Wasm.IEEE64.mul r c3))))
    (Wasm.IEEE64.mul (Wasm.IEEE64.mul r2 r2) (Wasm.IEEE64.add c4 (Wasm.IEEE64.mul r c5)))

/-- The same evaluation on floats, as `Exp2.exp2Core` writes it. -/
def floatEvaluation (r t : Float) : Float :=
  let C1 := Float.ofBits 0x3FE62E42FEFA39EF
  let C2 := Float.ofBits 0x3FCEBFBDFF82C424
  let C3 := Float.ofBits 0x3FAC6B08D70CF4B5
  let C4 := Float.ofBits 0x3F83B2ABD24650CC
  let C5 := Float.ofBits 0x3F55D7E09B4E3A84
  let r2 := r * r
  t + r * C1 + r2 * (C2 + r * C3) + r2 * r2 * (C4 + r * C5)

theorem evaluation_bits (r t : Float) :
    (floatEvaluation r t).toBits = evaluation r.toBits t.toBits := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := coefficient_finite
  simp only [floatEvaluation, evaluation, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, c1, c2, c3, c4, c5] at h1 h2 h3 h4 h5 ⊢
  simp only [not_nan_of_finite h1, not_nan_of_finite h2, not_nan_of_finite h3,
    not_nan_of_finite h4, not_nan_of_finite h5, Bool.false_eq_true, ite_false]

theorem evaluation_error (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 1 / 256) (ht : |value t| ≤ 1 / 2 ^ 53) :
    Finite (evaluation r t) ∧ |value (evaluation r t)| ≤ 1 / 64 ∧
      |value (evaluation r t) - (value t + polynomial (value r))| ≤ 1 / 2 ^ 57 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := coefficient_finite
  obtain ⟨b1, b2, b3, b4, b5⟩ := coefficient_bounds
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hm : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := rfl
  set R := value r
  set T := value t
  have hR := approx_self r hrf
  have hT := approx_self t htf
  have hC1 := approx_self c1 f1
  have hC2 := approx_self c2 f2
  have hC3 := approx_self c3 f3
  have hC4 := approx_self c4 f4
  have hC5 := approx_self c5 f5
  have hR2 : |R * R| ≤ 1 / 2 ^ 16 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 256 * (1 / 256) := mul_le_mul hr hr (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 16 := by norm_num
  -- r²
  have ar2 := (mul_approx hR hR (1 / 256) (1 / 256) hr hr (by norm_num)).mono
    (e' := 1 / 2 ^ 68) (by rw [hu, hm]; norm_num)
  -- r C1, r C3, r C5
  have a1 := (mul_approx hR hC1 (1 / 256) (7 / 10) hr b1 (by norm_num)).mono
    (e' := 1 / 2 ^ 61) (by rw [hu, hm]; norm_num)
  have a3 := (mul_approx hR hC3 (1 / 256) (1 / 16) hr b3 (by norm_num)).mono
    (e' := 1 / 2 ^ 64) (by rw [hu, hm]; norm_num)
  have a5 := (mul_approx hR hC5 (1 / 256) (1 / 512) hr b5 (by norm_num)).mono
    (e' := 1 / 2 ^ 69) (by rw [hu, hm]; norm_num)
  -- C2 + r C3 and C4 + r C5
  have hRC3 : |R * value c3| ≤ 1 / 2 ^ 12 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 256 * (1 / 16) := mul_le_mul hr b3 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 12 := by norm_num
  have hRC5 : |R * value c5| ≤ 1 / 2 ^ 17 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 256 * (1 / 512) := mul_le_mul hr b5 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 17 := by norm_num
  have p23 := (add_approx hC2 a3 (1 / 2) (by
      have := abs_add_le (value c2) (R * value c3)
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 53) (by rw [hu]; norm_num)
  have p45 := (add_approx hC4 a5 (1 / 32) (by
      have := abs_add_le (value c4) (R * value c5)
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 57) (by rw [hu]; norm_num)
  have hP23 : |value c2 + R * value c3| ≤ 1 / 2 := by
    have := abs_add_le (value c2) (R * value c3)
    linarith
  have hP45 : |value c4 + R * value c5| ≤ 1 / 32 := by
    have := abs_add_le (value c4) (R * value c5)
    linarith
  -- r² (C2 + r C3) and r⁴ (C4 + r C5)
  have q23 := (mul_approx ar2 p23 (1 / 2 ^ 16) (1 / 2) hR2 hP23 (by norm_num)).mono
    (e' := 1 / 2 ^ 67) (by rw [hu, hm]; norm_num)
  have ar4 := (mul_approx ar2 ar2 (1 / 2 ^ 16) (1 / 2 ^ 16) hR2 hR2 (by norm_num)).mono
    (e' := 1 / 2 ^ 82) (by rw [hu, hm]; norm_num)
  have hR4 : |R * R * (R * R)| ≤ 1 / 2 ^ 32 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 2 ^ 16 * (1 / 2 ^ 16) := mul_le_mul hR2 hR2 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 32 := by norm_num
  have q45 := (mul_approx ar4 p45 (1 / 2 ^ 32) (1 / 32) hR4 hP45 (by norm_num)).mono
    (e' := 1 / 2 ^ 85) (by rw [hu, hm]; norm_num)
  -- the sums
  have hRC1 : |R * value c1| ≤ 7 / 2560 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 256 * (7 / 10) := mul_le_mul hr b1 (abs_nonneg _) (by norm_num)
      _ = 7 / 2560 := by norm_num
  have s1 := (add_approx hT a1 (1 / 256) (by
      have := abs_add_le T (R * value c1)
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 60) (by rw [hu]; norm_num)
  have hS1 : |T + R * value c1| ≤ 1 / 256 := by
    have := abs_add_le T (R * value c1)
    linarith
  have hQ23 : |R * R * (value c2 + R * value c3)| ≤ 1 / 2 ^ 17 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 2 ^ 16 * (1 / 2) := mul_le_mul hR2 hP23 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 17 := by norm_num
  have s2 := (add_approx s1 q23 (1 / 128) (by
      have := abs_add_le (T + R * value c1) (R * R * (value c2 + R * value c3))
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 58) (by rw [hu]; norm_num)
  have hS2 : |T + R * value c1 + R * R * (value c2 + R * value c3)| ≤ 1 / 128 := by
    have := abs_add_le (T + R * value c1) (R * R * (value c2 + R * value c3))
    linarith
  have hQ45 : |R * R * (R * R) * (value c4 + R * value c5)| ≤ 1 / 2 ^ 37 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 2 ^ 32 * (1 / 32) := mul_le_mul hR4 hP45 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 37 := by norm_num
  have y := (add_approx s2 q45 (1 / 64) (by
      have := abs_add_le (T + R * value c1 + R * R * (value c2 + R * value c3))
        (R * R * (R * R) * (value c4 + R * value c5))
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 57) (by rw [hu]; norm_num)
  have hid : T + R * value c1 + R * R * (value c2 + R * value c3) +
      R * R * (R * R) * (value c4 + R * value c5) = T + polynomial R := by
    simp only [polynomial]
    ring
  have y' : Approx (evaluation r t) (T + polynomial R) (1 / 2 ^ 57) := y.congr hid
  refine ⟨y'.1, ?_, y'.2⟩
  have hY : |T + polynomial R| ≤ 1 / 128 + 1 / 2 ^ 37 := by
    rw [← hid]
    have := abs_add_le (T + R * value c1 + R * R * (value c2 + R * value c3))
      (R * R * (R * R) * (value c4 + R * value c5))
    linarith
  have := y'.abs_le hY
  linarith [show (1 : ℝ) / 128 + 1 / 2 ^ 37 + 1 / 2 ^ 57 ≤ 1 / 64 by norm_num]

/-- The evaluation against `t + 2 ^ r - 1`. -/
theorem evaluation_exp_error (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 1 / 256) (ht : |value t| ≤ 1 / 2 ^ 53) :
    |value (evaluation r t) -
        (value t + Real.exp (value r * Real.log 2) - 1)| ≤ 1 / 2 ^ 56 := by
  have he := (evaluation_error r t hrf htf hr ht).2.2
  have hp := polynomial_error (value r) hr
  calc
    _ = |(value (evaluation r t) - (value t + polynomial (value r))) -
        (Real.exp (value r * Real.log 2) - 1 - polynomial (value r))| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ 1 / 2 ^ 57 + 1 / 2 ^ 58 := add_le_add he hp
    _ ≤ 1 / 2 ^ 56 := by norm_num

#print axioms evaluation_bits
#print axioms evaluation_error
#print axioms evaluation_exp_error

end Verified.Examples.Exp2Evaluation
