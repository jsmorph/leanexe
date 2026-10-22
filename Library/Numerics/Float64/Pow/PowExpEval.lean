import Library.Numerics.Float64.Exp.ExpEvaluationBounds
import LeanExe.ProofKit.F64ErrorTrack
import LeanExe.ProofKit.PolyBound
import LeanExe.ProofKit.TaylorRemainder

/-!
The polynomial of Arm's `exp_inline` as `pow` uses it, whose residual carries the tail `xtail` of
the product `y log x` and so reaches `1/360`.  On `|r| ≤ 1/360` the polynomial is within `2 ^ -63`
of `exp r - 1`, from the Taylor polynomial of degree 7 and `PolyBound.check`, and its evaluation
in the order of the code is within `2 ^ -59` of the polynomial.  A coarse bound covers residuals up
to `1/128`, for arguments beyond 768, whose results overflow or vanish.
-/

namespace Library.Numerics.Float64.Pow.PowExpEval
open CodeLib.IEEE64
open LeanExe.ProofKit F64ErrorTrack PolyBound TaylorRemainder Library.Numerics.Float64.Exp.ExpEvaluationBounds

set_option exponentiation.threshold 4096

/-- `1 + r + C2 r ^ 2 + C3 r ^ 3 + C4 r ^ 4 + C5 r ^ 5`. -/
def kernel : List ℚ :=
  [1, 1, ratOfWord 0x3FDFFFFFFFFFFDBD, ratOfWord 0x3FC555555555543C,
    ratOfWord 0x3FA55555CF172B91, ratOfWord 0x3F81111167A4D017]

theorem kernel_check :
    check (subP (expCoeffs 8) kernel) (-1 / 360) (1 / 360) (1 / 2 ^ 64) 4 = true := by
  decide +kernel

theorem kernel_eval (r : ℝ) : eval kernel r = 1 + Library.Numerics.Float64.Exp.ExpApproximation.polynomial r := by
  simp only [kernel, eval_cons, eval_nil, ratOfWord_cast, Rat.cast_one,
    Library.Numerics.Float64.Exp.ExpApproximation.polynomial]
  ring

theorem polynomial_error (r : ℝ) (hr : |r| ≤ 1 / 360) :
    |Real.exp r - (1 + Library.Numerics.Float64.Exp.ExpApproximation.polynomial r)| ≤ 1 / 2 ^ 63 := by
  have hrem := exp_remainder r (hr.trans (by norm_num)) 8 (by norm_num)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hr
  have hc := check_sound _ _ _ _ _ kernel_check r (by push_cast; linarith)
    (by push_cast; linarith)
  rw [eval_subP, kernel_eval] at hc
  have hc' : |eval (expCoeffs 8) r - (1 + Library.Numerics.Float64.Exp.ExpApproximation.polynomial r)| ≤ 1 / 2 ^ 64 :=
    hc.trans (le_of_eq (by norm_num))
  have hp : |r| ^ 8 ≤ (1 / 360) ^ 8 := pow_le_pow_left₀ (abs_nonneg r) hr 8
  have ht : |r| ^ 8 * (((8 : ℕ) + 1 : ℝ) / ((Nat.factorial 8 : ℕ) * (8 : ℕ))) ≤ 1 / 2 ^ 64 := by
    calc
      _ ≤ (1 / 360) ^ 8 * (((8 : ℕ) + 1 : ℝ) / ((Nat.factorial 8 : ℕ) * (8 : ℕ))) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ ≤ 1 / 2 ^ 64 := by norm_num [Nat.factorial]
  calc
    _ ≤ |Real.exp r - eval (expCoeffs 8) r| +
        |eval (expCoeffs 8) r - (1 + Library.Numerics.Float64.Exp.ExpApproximation.polynomial r)| := abs_sub_le _ _ _
    _ ≤ 1 / 2 ^ 64 + 1 / 2 ^ 64 := add_le_add (hrem.trans (by exact_mod_cast ht)) hc'
    _ = 1 / 2 ^ 63 := by norm_num

theorem evaluation_tight (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 1 / 360) (ht : |value t| ≤ 1 / 2 ^ 53) :
    Finite (evaluation r t) ∧ |value (evaluation r t)| ≤ 1 / 256 ∧
      |value (evaluation r t) - (value t + Library.Numerics.Float64.Exp.ExpApproximation.polynomial (value r))| ≤
        1 / 2 ^ 59 := by
  obtain ⟨f2, f3, f4, f5⟩ := coefficient_finite
  obtain ⟨b2, b3, b4, b5⟩ := coefficient_bounds
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hm : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := rfl
  set R := value r
  set T := value t
  have hR := approx_self r hrf
  have hT := approx_self t htf
  have hC2 := approx_self _ f2
  have hC3 := approx_self _ f3
  have hC4 := approx_self _ f4
  have hC5 := approx_self _ f5
  have hR2 : |R * R| ≤ 1 / 129600 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 360 * (1 / 360) := mul_le_mul hr hr (abs_nonneg _) (by norm_num)
      _ = 1 / 129600 := by norm_num
  have ar2 := (mul_approx hR hR (1 / 360) (1 / 360) hr hr (by norm_num)).mono
    (e' := 1 / 2 ^ 69) (by rw [hu, hm]; norm_num)
  have a3 := (mul_approx hR hC3 (1 / 360) (1 / 6) hr b3 (by norm_num)).mono
    (e' := 1 / 2 ^ 64) (by rw [hu, hm]; norm_num)
  have a5 := (mul_approx hR hC5 (1 / 360) (1 / 64) hr b5 (by norm_num)).mono
    (e' := 1 / 2 ^ 67) (by rw [hu, hm]; norm_num)
  have hRC3 : |R * value 0x3FC555555555543C| ≤ 1 / 2160 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 360 * (1 / 6) := mul_le_mul hr b3 (abs_nonneg _) (by norm_num)
      _ = 1 / 2160 := by norm_num
  have hRC5 : |R * value 0x3F81111167A4D017| ≤ 1 / 23040 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 360 * (1 / 64) := mul_le_mul hr b5 (abs_nonneg _) (by norm_num)
      _ = 1 / 23040 := by norm_num
  have hP23 : |value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C| ≤ 1 / 2 + 1 / 2160 := by
    have := abs_add_le (value 0x3FDFFFFFFFFFFDBD) (R * value 0x3FC555555555543C)
    linarith
  have hP45 : |value 0x3FA55555CF172B91 + R * value 0x3F81111167A4D017| ≤
      1 / 16 + 1 / 23040 := by
    have := abs_add_le (value 0x3FA55555CF172B91) (R * value 0x3F81111167A4D017)
    linarith
  have n1 : (1 : ℝ) / 2 ^ 64 ≤ 1 / 2000 - 1 / 2160 := by norm_num
  have p23 := (add_approx hC2 a3 (1 / 2 + 1 / 2000) (by linarith) (by norm_num)).mono
    (e' := 1 / 2 ^ 53) (by rw [hu]; norm_num)
  have n2 : (1 : ℝ) / 2 ^ 67 ≤ 1 / 20000 - 1 / 23040 := by norm_num
  have p45 := (add_approx hC4 a5 (1 / 16 + 1 / 20000) (by linarith) (by norm_num)).mono
    (e' := 1 / 2 ^ 56) (by rw [hu]; norm_num)
  have q23 := (mul_approx ar2 p23 (1 / 129600) (1 / 2 + 1 / 2160) hR2 hP23 (by norm_num)).mono
    (e' := 1 / 2 ^ 68) (by rw [hu, hm]; norm_num)
  have hR4 : |R * R * (R * R)| ≤ 1 / 129600 ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 129600 * (1 / 129600) := mul_le_mul hR2 hR2 (abs_nonneg _) (by norm_num)
      _ = 1 / 129600 ^ 2 := by norm_num
  have ar4 := (mul_approx ar2 ar2 (1 / 129600) (1 / 129600) hR2 hR2 (by norm_num)).mono
    (e' := 1 / 2 ^ 84) (by rw [hu, hm]; norm_num)
  have q45 := (mul_approx ar4 p45 (1 / 129600 ^ 2) (1 / 16 + 1 / 23040) hR4 hP45
    (by norm_num)).mono (e' := 1 / 2 ^ 86) (by rw [hu, hm]; norm_num)
  have hS1 : |T + R| ≤ 1 / 360 + 1 / 2 ^ 53 := by
    have := abs_add_le T R
    linarith
  have n3 : (1 : ℝ) / 2 ^ 53 ≤ 1 / 2 ^ 52 := by norm_num
  have s1 := (add_approx hT hR (1 / 360 + 1 / 2 ^ 52) (by linarith) (by norm_num)).mono
    (e' := 3 / 2 ^ 63) (by rw [hu]; norm_num)
  have hQ23 : |R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C)| ≤
      1 / 129600 * (1 / 2 + 1 / 2160) := by
    rw [abs_mul]
    exact mul_le_mul hR2 hP23 (abs_nonneg _) (by norm_num)
  have hS2 : |T + R + R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C)| ≤
      1 / 360 + 1 / 2 ^ 53 + 1 / 129600 * (1 / 2 + 1 / 2160) := by
    have := abs_add_le (T + R) (R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C))
    linarith
  have s2 := (add_approx s1 q23 (1 / 360 + 1 / 2 ^ 17) (by
      have : (1 : ℝ) / 360 + 1 / 2 ^ 53 + 1 / 129600 * (1 / 2 + 1 / 2160) + 3 / 2 ^ 63 +
          1 / 2 ^ 68 ≤ 1 / 360 + 1 / 2 ^ 17 := by norm_num
      linarith) (by norm_num)).mono (e' := 3 / 2 ^ 62) (by rw [hu]; norm_num)
  have hQ45 : |R * R * (R * R) * (value 0x3FA55555CF172B91 + R * value 0x3F81111167A4D017)| ≤
      1 / 129600 ^ 2 * (1 / 16 + 1 / 23040) := by
    rw [abs_mul]
    exact mul_le_mul hR4 hP45 (abs_nonneg _) (by norm_num)
  have hY : |T + R + R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C) +
      R * R * (R * R) * (value 0x3FA55555CF172B91 + R * value 0x3F81111167A4D017)| ≤
      1 / 360 + 1 / 2 ^ 53 + 1 / 129600 * (1 / 2 + 1 / 2160) +
        1 / 129600 ^ 2 * (1 / 16 + 1 / 23040) := by
    have := abs_add_le (T + R + R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C))
      (R * R * (R * R) * (value 0x3FA55555CF172B91 + R * value 0x3F81111167A4D017))
    linarith
  have y := (add_approx s2 q45 (1 / 360 + 1 / 2 ^ 17) (by
      have : (1 : ℝ) / 360 + 1 / 2 ^ 53 + 1 / 129600 * (1 / 2 + 1 / 2160) +
          1 / 129600 ^ 2 * (1 / 16 + 1 / 23040) + 3 / 2 ^ 62 + 1 / 2 ^ 86 ≤
          1 / 360 + 1 / 2 ^ 17 := by norm_num
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 59) (by rw [hu]; norm_num)
  have hid : T + R + R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C) +
      R * R * (R * R) * (value 0x3FA55555CF172B91 + R * value 0x3F81111167A4D017) =
      T + Library.Numerics.Float64.Exp.ExpApproximation.polynomial R := by
    simp only [Library.Numerics.Float64.Exp.ExpApproximation.polynomial]
    ring
  have y' : Approx (evaluation r t) (T + Library.Numerics.Float64.Exp.ExpApproximation.polynomial R) (1 / 2 ^ 59) :=
    y.congr hid
  refine ⟨y'.1, ?_, y'.2⟩
  have hY' : |T + Library.Numerics.Float64.Exp.ExpApproximation.polynomial R| ≤ 1 / 360 + 1 / 2 ^ 53 +
      1 / 129600 * (1 / 2 + 1 / 2160) + 1 / 129600 ^ 2 * (1 / 16 + 1 / 23040) := by
    rw [← hid]
    exact hY
  have := y'.abs_le hY'
  have hnum : (1 : ℝ) / 360 + 1 / 2 ^ 53 + 1 / 129600 * (1 / 2 + 1 / 2160) +
      1 / 129600 ^ 2 * (1 / 16 + 1 / 23040) + 1 / 2 ^ 59 ≤ 1 / 256 := by norm_num
  linarith

/-- The evaluation against `t + exp r - 1`. -/
theorem evaluation_exp_tight (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 1 / 360) (ht : |value t| ≤ 1 / 2 ^ 53) :
    |value (evaluation r t) - (value t + Real.exp (value r) - 1)| ≤ 17 / 2 ^ 63 := by
  have he := (evaluation_tight r t hrf htf hr ht).2.2
  have hp := polynomial_error (value r) hr
  calc
    _ = |(value (evaluation r t) - (value t + Library.Numerics.Float64.Exp.ExpApproximation.polynomial (value r))) -
        (Real.exp (value r) - (1 + Library.Numerics.Float64.Exp.ExpApproximation.polynomial (value r)))| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ 1 / 2 ^ 59 + 1 / 2 ^ 63 := add_le_add he hp
    _ = 17 / 2 ^ 63 := by norm_num

/-- A coarse bound for `|r| ≤ 1/128`. -/
theorem evaluation_coarse (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 1 / 128) (ht : |value t| ≤ 1 / 2 ^ 53) :
    Finite (evaluation r t) ∧ |value (evaluation r t)| ≤ 1 / 64 := by
  obtain ⟨f2, f3, f4, f5⟩ := coefficient_finite
  obtain ⟨b2, b3, b4, b5⟩ := coefficient_bounds
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hm : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := rfl
  set R := value r
  set T := value t
  have hR := approx_self r hrf
  have hT := approx_self t htf
  have hR2 : |R * R| ≤ 1 / 2 ^ 14 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 128 * (1 / 128) := mul_le_mul hr hr (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 14 := by norm_num
  have ar2 := (mul_approx hR hR (1 / 128) (1 / 128) hr hr (by norm_num)).mono
    (e' := 1 / 2 ^ 60) (by rw [hu, hm]; norm_num)
  have a3 := (mul_approx hR (approx_self _ f3) (1 / 128) (1 / 6) hr b3 (by norm_num)).mono
    (e' := 1 / 2 ^ 60) (by rw [hu, hm]; norm_num)
  have a5 := (mul_approx hR (approx_self _ f5) (1 / 128) (1 / 64) hr b5 (by norm_num)).mono
    (e' := 1 / 2 ^ 60) (by rw [hu, hm]; norm_num)
  have hP23 : |value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C| ≤ 1 := by
    have := abs_add_le (value 0x3FDFFFFFFFFFFDBD) (R * value 0x3FC555555555543C)
    have := abs_mul R (value 0x3FC555555555543C)
    have : |R| * |value 0x3FC555555555543C| ≤ 1 / 128 * (1 / 6) :=
      mul_le_mul hr b3 (abs_nonneg _) (by norm_num)
    linarith
  have hP45 : |value 0x3FA55555CF172B91 + R * value 0x3F81111167A4D017| ≤ 1 := by
    have := abs_add_le (value 0x3FA55555CF172B91) (R * value 0x3F81111167A4D017)
    have := abs_mul R (value 0x3F81111167A4D017)
    have : |R| * |value 0x3F81111167A4D017| ≤ 1 / 128 * (1 / 64) :=
      mul_le_mul hr b5 (abs_nonneg _) (by norm_num)
    linarith
  have n1 : (1 : ℝ) / 2 ^ 60 ≤ 1 := by norm_num
  have p23 := (add_approx (approx_self _ f2) a3 2 (by linarith) (by norm_num)).mono
    (e' := 1 / 2 ^ 50) (by rw [hu]; norm_num)
  have p45 := (add_approx (approx_self _ f4) a5 2 (by linarith) (by norm_num)).mono
    (e' := 1 / 2 ^ 50) (by rw [hu]; norm_num)
  have q23 := (mul_approx ar2 p23 (1 / 2 ^ 14) 1 hR2 hP23 (by norm_num)).mono
    (e' := 1 / 2 ^ 59) (by rw [hu, hm]; norm_num)
  have hR4 : |R * R * (R * R)| ≤ 1 / 2 ^ 28 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 2 ^ 14 * (1 / 2 ^ 14) := mul_le_mul hR2 hR2 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 28 := by norm_num
  have ar4 := (mul_approx ar2 ar2 (1 / 2 ^ 14) (1 / 2 ^ 14) hR2 hR2 (by norm_num)).mono
    (e' := 1 / 2 ^ 60) (by rw [hu, hm]; norm_num)
  have q45 := (mul_approx ar4 p45 (1 / 2 ^ 28) 1 hR4 hP45 (by norm_num)).mono
    (e' := 1 / 2 ^ 59) (by rw [hu, hm]; norm_num)
  have hS1 : |T + R| ≤ 1 / 128 + 1 / 2 ^ 53 := by
    have := abs_add_le T R
    linarith
  have n2 : (1 : ℝ) / 128 + 1 / 2 ^ 53 ≤ 1 / 64 := by norm_num
  have s1 := (add_approx hT hR (1 / 64) (by linarith) (by norm_num)).mono
    (e' := 1 / 2 ^ 58) (by rw [hu]; norm_num)
  have hQ23 : |R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C)| ≤ 1 / 2 ^ 14 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 2 ^ 14 * 1 := mul_le_mul hR2 hP23 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 14 := by norm_num
  have hQ45 : |R * R * (R * R) * (value 0x3FA55555CF172B91 + R * value 0x3F81111167A4D017)| ≤
      1 / 2 ^ 28 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 2 ^ 28 * 1 := mul_le_mul hR4 hP45 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 ^ 28 := by norm_num
  have s2 := (add_approx s1 q23 (1 / 64) (by
      have := abs_add_le (T + R) (R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C))
      have : (1 : ℝ) / 128 + 1 / 2 ^ 53 + 1 / 2 ^ 14 + 1 / 2 ^ 58 + 1 / 2 ^ 59 ≤ 1 / 64 := by
        norm_num
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 57) (by rw [hu]; norm_num)
  have hY : |T + R + R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C) +
      R * R * (R * R) * (value 0x3FA55555CF172B91 + R * value 0x3F81111167A4D017)| ≤
      1 / 128 + 1 / 2 ^ 53 + 1 / 2 ^ 14 + 1 / 2 ^ 28 := by
    have := abs_add_le (T + R) (R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C))
    have := abs_add_le (T + R + R * R * (value 0x3FDFFFFFFFFFFDBD + R * value 0x3FC555555555543C))
      (R * R * (R * R) * (value 0x3FA55555CF172B91 + R * value 0x3F81111167A4D017))
    linarith
  have y := (add_approx s2 q45 (1 / 64) (by
      have : (1 : ℝ) / 128 + 1 / 2 ^ 53 + 1 / 2 ^ 14 + 1 / 2 ^ 28 + 1 / 2 ^ 57 + 1 / 2 ^ 59 ≤
          1 / 64 := by norm_num
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 56) (by rw [hu]; norm_num)
  have y' : Approx (evaluation r t) _ (1 / 2 ^ 56) := y
  refine ⟨y'.1, ?_⟩
  have := y'.abs_le hY
  have hnum : (1 : ℝ) / 128 + 1 / 2 ^ 53 + 1 / 2 ^ 14 + 1 / 2 ^ 28 + 1 / 2 ^ 56 ≤ 1 / 64 := by
    norm_num
  linarith

#print axioms kernel_check
#print axioms kernel_eval
#print axioms polynomial_error
#print axioms evaluation_tight
#print axioms evaluation_exp_tight
#print axioms evaluation_coarse

end Library.Numerics.Float64.Pow.PowExpEval
