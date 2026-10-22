import LeanExe.ProofKit.AsinRemainder

/-!
The approximation error of fdlibm's rational function for `arcsin`, as FreeBSD msun's `e_asin.c`
and `e_acos.c` at commit `20381bce4b63975494a2f4bc84257f6932e6d379` hold its coefficients `pS0` to
`pS5` and `qS1` to `qS4`.  With `t = x ^ 2`, the code computes `p = t (pS0 + ... + pS5 t ^ 5)` and
`q = 1 + qS1 t + ... + qS4 t ^ 4` and returns `x + x (p/q)`, so `x ^ 3 (eval asinP t / eval asinQ t)`
is `x (p/q)` in exact arithmetic.  `e_asin.c` uses it for `|x| < 0.5`, and both files use it for
`arcsin s` with `s = √t` and `t = (1 - |x|)/2 ≤ 1/4`, so the argument satisfies `|x| ≤ 1/2`.
The source bounds `|(arcsin x - x)/x ^ 3 - R(x ^ 2)|` by `2 ^ -58.75`.  That bound leaves out the
rounding of `pS0 ≈ 1/6`: the error at `x = 0` is `1/6 - pS0`, about `2 ^ -56.58`, the largest on
`[0, 1/2]`, and `asin_kernel_error` states `(11/16) 2 ^ -56`, about `2 ^ -56.54`.
-/

namespace Library.Numerics.Float64.Asin.AsinKernelPoly
open LeanExe.ProofKit PolyBound PolyChecks AsinRemainder

/-- `pS0 + pS1 t + ... + pS5 t ^ 5`. -/
def asinP : List ℚ :=
  [ratOfWord 0x3FC5555555555555, ratOfWord 0xBFD4D61203EB6F7D, ratOfWord 0x3FC9C1550E884455,
    ratOfWord 0xBFA48228B5688F3B, ratOfWord 0x3F49EFE07501B288, ratOfWord 0x3F023DE10DFDF709]

/-- `1 + qS1 t + ... + qS4 t ^ 4`. -/
def asinQ : List ℚ :=
  [1, ratOfWord 0xC0033A271C8A2D4B, ratOfWord 0x40002AE59C598AC8, ratOfWord 0xBFE6066C1B8D0159,
    ratOfWord 0x3FB3B8C5B12E9282]

/-- The Taylor polynomial of `(arcsin x - x) / x ^ 3` in `t = x ^ 2`, of degree 34. -/
def asinTail : List ℚ := (asinCoeffs 36).tail

theorem asin_split : asinCoeffs 36 = 1 :: asinTail := by
  decide +kernel

theorem defect_low : ((invSqrtDefect 36).take 36).all (fun a => decide (a = 0)) = true := by
  decide +kernel

theorem defect_high : check ((invSqrtDefect 36).drop 36) 0 (1 / 4) (1 / 2) 18 = true := by
  decide +kernel

/-- `T q - p` for the Taylor polynomial `T`. -/
def asinDefect : List ℚ := subP (mulP asinTail asinQ) asinP

/-- The relative bound checked against the weight `q`. -/
def asinEps : ℚ := (43 / 64) / 2 ^ 56

/-- `T q - p - ε q + ε`. -/
def asinUpper : List ℚ := addP (subP asinDefect (scaleP asinEps asinQ)) [asinEps]

/-- `T q - p + ε q - ε`. -/
def asinLower : List ℚ := subP (addP asinDefect (scaleP asinEps asinQ)) [asinEps]

theorem asin_up_1 : check asinUpper (0 : ℚ) (1 / 16 : ℚ) asinEps 18 = true := by
  decide +kernel

theorem asin_up_2 : check asinUpper (1 / 16 : ℚ) (1 / 8 : ℚ) asinEps 18 = true := by
  decide +kernel

theorem asin_up_3 : check asinUpper (1 / 8 : ℚ) (3 / 16 : ℚ) asinEps 18 = true := by
  decide +kernel

theorem asin_up_4 : check asinUpper (3 / 16 : ℚ) (1 / 4 : ℚ) asinEps 18 = true := by
  decide +kernel

theorem asin_up_covers : Covers asinUpper asinEps 18 (0 : ℚ) (1 / 4 : ℚ)
    [(1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ)] :=
  ⟨asin_up_1, asin_up_2, asin_up_3, asin_up_4⟩

theorem asin_lo_1 : check asinLower (0 : ℚ) (1 / 16 : ℚ) asinEps 18 = true := by
  decide +kernel

theorem asin_lo_2 : check asinLower (1 / 16 : ℚ) (1 / 8 : ℚ) asinEps 18 = true := by
  decide +kernel

theorem asin_lo_3 : check asinLower (1 / 8 : ℚ) (3 / 16 : ℚ) asinEps 18 = true := by
  decide +kernel

theorem asin_lo_4 : check asinLower (3 / 16 : ℚ) (1 / 4 : ℚ) asinEps 18 = true := by
  decide +kernel

theorem asin_lo_covers : Covers asinLower asinEps 18 (0 : ℚ) (1 / 4 : ℚ)
    [(1 / 16 : ℚ), (1 / 8 : ℚ), (3 / 16 : ℚ)] :=
  ⟨asin_lo_1, asin_lo_2, asin_lo_3, asin_lo_4⟩

theorem asin_q_range : check (subP asinQ [3 / 4]) 0 (1 / 4) (1 / 4) 18 = true := by
  decide +kernel

/-- The rational function's error, relative to `x ^ 3`. -/
theorem asin_kernel_error (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |Real.arcsin x - x - x ^ 3 * (eval asinP (x ^ 2) / eval asinQ (x ^ 2))| ≤
      |x| ^ 3 * ((11 / 16) / 2 ^ 56) := by
  have hz0 : (((0 : ℚ)) : ℝ) ≤ x ^ 2 := by simpa using sq_nonneg x
  have hz1 : x ^ 2 ≤ (((1 / 4 : ℚ)) : ℝ) := by
    push_cast
    rw [← sq_abs]
    nlinarith [abs_nonneg x]
  have hrem := asin_remainder 36 (1 / 2) defect_low (bounded_of_check _ _ _ _ _ defect_high) x hx
  rw [asin_split, eval_cons] at hrem
  have hw := abs_le_weighted asinDefect asinQ asinEps 0 (1 / 4) asinEps asinEps
    (bounded_of_covers _ _ _ _ _ _ asin_up_covers) (bounded_of_covers _ _ _ _ _ _ asin_lo_covers)
    (x ^ 2) hz0 hz1
  rw [asinDefect, eval_subP, eval_mulP,
    show ((asinEps : ℚ) : ℝ) = (43 / 64) / 2 ^ 56 by norm_num [asinEps]] at hw
  have hq := check_sound _ _ _ _ _ asin_q_range (x ^ 2) hz0 hz1
  rw [eval_subP] at hq
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at hq
  set T := eval asinTail (x ^ 2) with hT
  set p := eval asinP (x ^ 2) with hp
  set q := eval asinQ (x ^ 2) with hq'
  have hq1 : |q - 3 / 4| ≤ 1 / 4 := by
    push_cast at hq
    exact hq
  have hqpos : 0 < q := by linarith [(abs_le.mp (show |q - 3 / 4| ≤ 1 / 4 from hq1)).1]
  have hd := sub_div_le T p q ((43 / 64) / 2 ^ 56) hqpos hw
  have hrem' : |Real.arcsin x - x - x ^ 3 * T| ≤ 4 / 3 * (1 / 2) * |x| ^ (2 * 36 + 1) := by
    have e : x * (((1 : ℚ) : ℝ) + x ^ 2 * T) = x + x ^ 3 * T := by
      push_cast
      ring
    rw [e, show ((1 / 2 : ℚ) : ℝ) = 1 / 2 by norm_num] at hrem
    rw [sub_sub]
    exact hrem
  have hx70 : |x| ^ 70 ≤ (1 / 2) ^ 70 := pow_le_pow_left₀ (abs_nonneg x) hx 70
  have hx3 : 0 ≤ |x| ^ 3 := by positivity
  have ht : 4 / 3 * (1 / 2) * |x| ^ (2 * 36 + 1) ≤ |x| ^ 3 * ((1 / 64) / 2 ^ 56) := by
    rw [show 2 * 36 + 1 = 3 + 70 by norm_num, pow_add]
    have : 4 / 3 * (1 / 2) * (1 / 2 : ℝ) ^ 70 ≤ (1 / 64) / 2 ^ 56 := by norm_num
    calc 4 / 3 * (1 / 2) * (|x| ^ 3 * |x| ^ 70) = |x| ^ 3 * (4 / 3 * (1 / 2) * |x| ^ 70) := by ring
      _ ≤ |x| ^ 3 * (4 / 3 * (1 / 2) * (1 / 2) ^ 70) := by gcongr
      _ ≤ |x| ^ 3 * ((1 / 64) / 2 ^ 56) := by gcongr
  have hdiff : |x ^ 3 * T - x ^ 3 * (p / q)| ≤ |x| ^ 3 * ((43 / 64) / 2 ^ 56) := by
    rw [← mul_sub, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left hd hx3
  calc |Real.arcsin x - x - x ^ 3 * (p / q)| ≤
      |Real.arcsin x - x - x ^ 3 * T| + |x ^ 3 * T - x ^ 3 * (p / q)| := abs_sub_le _ _ _
    _ ≤ |x| ^ 3 * ((1 / 64) / 2 ^ 56) + |x| ^ 3 * ((43 / 64) / 2 ^ 56) :=
        add_le_add (hrem'.trans ht) hdiff
    _ = |x| ^ 3 * ((11 / 16) / 2 ^ 56) := by ring

#print axioms defect_low
#print axioms defect_high
#print axioms asin_up_covers
#print axioms asin_lo_covers
#print axioms asin_kernel_error

end Library.Numerics.Float64.Asin.AsinKernelPoly
