import LeanExe.ProofKit.TaylorRemainder
import LeanExe.ProofKit.PolyChecks

/-!
The approximation error of fdlibm's tangent polynomial, as FreeBSD msun's `k_tan.c` at commit
`20381bce4b63975494a2f4bc84257f6932e6d379` holds its coefficients `T[0]` to `T[12]`.  The kernel
evaluates `x + T[0] x ^ 3 + ... + T[12] x ^ 27`, which is `x * eval tanKernel (x ^ 2)` in exact
arithmetic, on `|x| ≤ 0.67434`, and on `[0.67434, π/4]` it applies the polynomial to `π/4 - x`.
The source bounds `|tan x / x - eval tanKernel (x ^ 2)|` by `2 ^ -59.2`.  The largest error on
`[0, 0.67434]` is about `2 ^ -59.147`, at `x ≈ 0.670`, above the stated bound, and
`tan_kernel_error` states `(59/64) 2 ^ -59`, about `2 ^ -59.12`.  With `S` and `C` the Taylor
polynomials of `sin x / x` and `cos x` in `z = x ^ 2`, the checks bound `S - C P` by `ε C`, and
the remainders of `sin` and `cos` and the lower bound `0.76` on `cos x` complete the bound.
-/

namespace Verified.Examples.TanKernelPoly
open LeanExe.ProofKit PolyBound PolyChecks TaylorRemainder

/-- `1 + T[0] z + ... + T[12] z ^ 13`. -/
def tanKernel : List ℚ :=
  [1, ratOfWord 0x3FD5555555555563, ratOfWord 0x3FC111111110FE7A, ratOfWord 0x3FABA1BA1BB341FE,
    ratOfWord 0x3F9664F48406D637, ratOfWord 0x3F8226E3E96E8493, ratOfWord 0x3F6D6D22C9560328,
    ratOfWord 0x3F57DBC8FEE08315, ratOfWord 0x3F4344D8F2F26501, ratOfWord 0x3F3026F71A8D1068,
    ratOfWord 0x3F147E88A03792A6, ratOfWord 0x3F12B80F32F0A7E9, ratOfWord 0xBEF375CBDB605373,
    ratOfWord 0x3EFB2A7074BF7AD4]

/-- `S - C P` for the Taylor polynomials `S` of `sin x / x` and `C` of `cos x` in `z`. -/
def tanDefect : List ℚ := subP (sinCoeffs 11) (mulP (cosCoeffs 11) tanKernel)

/-- The relative bound checked against the weight `C`. -/
def tanEps : ℚ := (233 / 256) / 2 ^ 59

/-- `S - C P - ε C + ε`, at most `ε` in magnitude exactly when `S - C P ≤ ε C` and more. -/
def tanUpper : List ℚ := addP (subP tanDefect (scaleP tanEps (cosCoeffs 11))) [tanEps]

/-- `S - C P + ε C - ε`. -/
def tanLower : List ℚ := subP (addP tanDefect (scaleP tanEps (cosCoeffs 11))) [tanEps]

theorem tan_up_1 : check tanUpper (0 : ℚ) (59603 / 1048576 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_up_2 : check tanUpper (59603 / 1048576 : ℚ) (59603 / 524288 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_up_3 : check tanUpper (59603 / 524288 : ℚ) (178809 / 1048576 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_up_4 : check tanUpper (178809 / 1048576 : ℚ) (59603 / 262144 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_up_5 : check tanUpper (59603 / 262144 : ℚ) (298015 / 1048576 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_up_6 : check tanUpper (298015 / 1048576 : ℚ) (178809 / 524288 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_up_7 : check tanUpper (178809 / 524288 : ℚ) (417221 / 1048576 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_up_8 : check tanUpper (417221 / 1048576 : ℚ) (59603 / 131072 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_up_covers : Covers tanUpper tanEps 18 (0 : ℚ) (59603 / 131072 : ℚ)
    [(59603 / 1048576 : ℚ), (59603 / 524288 : ℚ), (178809 / 1048576 : ℚ), (59603 / 262144 : ℚ), (298015 / 1048576 : ℚ), (178809 / 524288 : ℚ), (417221 / 1048576 : ℚ)] :=
  ⟨tan_up_1, tan_up_2, tan_up_3, tan_up_4, tan_up_5, tan_up_6, tan_up_7, tan_up_8⟩

theorem tan_lo_1 : check tanLower (0 : ℚ) (59603 / 1048576 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_lo_2 : check tanLower (59603 / 1048576 : ℚ) (59603 / 524288 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_lo_3 : check tanLower (59603 / 524288 : ℚ) (178809 / 1048576 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_lo_4 : check tanLower (178809 / 1048576 : ℚ) (59603 / 262144 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_lo_5 : check tanLower (59603 / 262144 : ℚ) (298015 / 1048576 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_lo_6 : check tanLower (298015 / 1048576 : ℚ) (178809 / 524288 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_lo_7 : check tanLower (178809 / 524288 : ℚ) (417221 / 1048576 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_lo_8 : check tanLower (417221 / 1048576 : ℚ) (59603 / 131072 : ℚ) tanEps 18 = true := by
  decide +kernel

theorem tan_lo_covers : Covers tanLower tanEps 18 (0 : ℚ) (59603 / 131072 : ℚ)
    [(59603 / 1048576 : ℚ), (59603 / 524288 : ℚ), (178809 / 1048576 : ℚ), (59603 / 262144 : ℚ), (298015 / 1048576 : ℚ), (178809 / 524288 : ℚ), (417221 / 1048576 : ℚ)] :=
  ⟨tan_lo_1, tan_lo_2, tan_lo_3, tan_lo_4, tan_lo_5, tan_lo_6, tan_lo_7, tan_lo_8⟩

theorem tan_range : check (subP tanKernel [1]) 0 (59603 / 131072 : ℚ) (1 / 4) 18 = true := by
  decide +kernel

/-- The tangent polynomial's error, relative to `x`. -/
theorem tan_kernel_error (x : ℝ) (hx : |x| ≤ 67434 / 100000) :
    |Real.tan x - x * eval tanKernel (x ^ 2)| ≤ |x| * ((59 / 64) / 2 ^ 59) := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num)
  have hx2 : x ^ 2 ≤ (67434 / 100000) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hz0 : (((0 : ℚ)) : ℝ) ≤ x ^ 2 := by simpa using sq_nonneg x
  have hz1 : x ^ 2 ≤ (((59603 / 131072 : ℚ)) : ℝ) := by
    push_cast
    have : (67434 / 100000 : ℝ) ^ 2 ≤ 59603 / 131072 := by norm_num
    linarith
  have hw := abs_le_weighted tanDefect (cosCoeffs 11) tanEps 0 (59603 / 131072) tanEps tanEps
    (bounded_of_covers _ _ _ _ _ _ tan_up_covers) (bounded_of_covers _ _ _ _ _ _ tan_lo_covers)
    (x ^ 2) hz0 hz1
  rw [tanDefect, eval_subP, eval_mulP,
    show ((tanEps : ℚ) : ℝ) = (233 / 256) / 2 ^ 59 by norm_num [tanEps]] at hw
  have hp := check_sound _ _ _ _ _ tan_range (x ^ 2) hz0 hz1
  rw [eval_subP] at hp
  simp only [eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one] at hp
  set S := eval (sinCoeffs 11) (x ^ 2) with hS
  set C := eval (cosCoeffs 11) (x ^ 2) with hC
  set P := eval tanKernel (x ^ 2) with hP
  have hP1 : |P - 1| ≤ 1 / 4 := hp.trans (le_of_eq (by norm_num))
  have hPb : |P| ≤ 5 / 4 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hP1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsin := sin_remainder x hx1 11
  have hcos := cos_remainder x hx1 11
  have hr1 : |Real.sin x - x * S| ≤ |x| * (2 / ((2 * 11 + 1).factorial : ℝ)) := by
    have hpw : |x| ^ (2 * 11 + 1) ≤ |x| := by
      rw [pow_succ']
      exact mul_le_of_le_one_right (abs_nonneg x) (pow_le_one₀ (abs_nonneg x) hx1)
    have hF : (0 : ℝ) < ((2 * 11 + 1).factorial : ℝ) := by positivity
    refine hsin.trans ?_
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hF]
    linarith
  have hr2 : |Real.cos x - C| ≤ 2 / ((2 * 11).factorial : ℝ) := by
    have hpw : |x| ^ (2 * 11) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
    have hF : (0 : ℝ) < ((2 * 11).factorial : ℝ) := by positivity
    refine hcos.trans ?_
    rw [div_le_div_iff_of_pos_right hF]
    linarith
  have hcpos : 76 / 100 ≤ Real.cos x := by
    have hcb := Real.cos_bound hx1
    have h4 : |x| ^ 4 ≤ (67434 / 100000) ^ 4 := pow_le_pow_left₀ (abs_nonneg x) hx 4
    have hn : (76 / 100 : ℝ) ≤ 1 - (67434 / 100000) ^ 2 / 2 - (67434 / 100000) ^ 4 * (5 / 96) := by
      norm_num
    have := (abs_le.mp hcb).1
    nlinarith
  have hcos0 : 0 < Real.cos x := by linarith
  have key : Real.tan x - x * P =
      (x * (S - C * P) + (Real.sin x - x * S) - x * P * (Real.cos x - C)) / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have htri : ∀ a b c : ℝ, |a + b - c| ≤ |a| + |b| + |c| := by
    intro a b c
    calc |a + b - c| = |a + b + (-c)| := by rw [sub_eq_add_neg]
      _ ≤ |a + b| + |-c| := abs_add_le _ _
      _ ≤ |a| + |b| + |c| := by
          rw [abs_neg]
          gcongr
          exact abs_add_le _ _
  have h1 : |x * (S - C * P)| ≤ |x| * ((233 / 256) / 2 ^ 59 * C) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hw (abs_nonneg x)
  have h3 : |x * P * (Real.cos x - C)| ≤ |x| * (5 / 4 * (2 / ((2 * 11).factorial : ℝ))) := by
    rw [abs_mul, abs_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg x)
    exact mul_le_mul hPb hr2 (abs_nonneg _) (by norm_num)
  have hCb : C ≤ Real.cos x + 2 / ((2 * 11).factorial : ℝ) := by
    have := (abs_le.mp hr2).1
    linarith
  have hsmall : (233 / 256) / 2 ^ 59 * (2 / ((2 * 11).factorial : ℝ)) +
      2 / ((2 * 11 + 1).factorial : ℝ) + 5 / 4 * (2 / ((2 * 11).factorial : ℝ)) ≤
      (3 / 256) / 2 ^ 59 * (76 / 100) := by
    norm_num [Nat.factorial]
  rw [key, abs_div, abs_of_pos hcos0, div_le_iff₀ hcos0]
  calc |x * (S - C * P) + (Real.sin x - x * S) - x * P * (Real.cos x - C)| ≤
      |x * (S - C * P)| + |Real.sin x - x * S| + |x * P * (Real.cos x - C)| := htri _ _ _
    _ ≤ |x| * ((233 / 256) / 2 ^ 59 * C) + |x| * (2 / ((2 * 11 + 1).factorial : ℝ)) +
        |x| * (5 / 4 * (2 / ((2 * 11).factorial : ℝ))) := add_le_add (add_le_add h1 hr1) h3
    _ ≤ |x| * ((233 / 256) / 2 ^ 59 * (Real.cos x + 2 / ((2 * 11).factorial : ℝ))) +
        |x| * (2 / ((2 * 11 + 1).factorial : ℝ)) +
        |x| * (5 / 4 * (2 / ((2 * 11).factorial : ℝ))) := by gcongr
    _ = |x| * ((233 / 256) / 2 ^ 59 * Real.cos x +
        ((233 / 256) / 2 ^ 59 * (2 / ((2 * 11).factorial : ℝ)) +
          2 / ((2 * 11 + 1).factorial : ℝ) + 5 / 4 * (2 / ((2 * 11).factorial : ℝ)))) := by ring
    _ ≤ |x| * ((233 / 256) / 2 ^ 59 * Real.cos x + (3 / 256) / 2 ^ 59 * Real.cos x) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg x)
        have : (3 / 256) / 2 ^ 59 * (76 / 100 : ℝ) ≤ (3 / 256) / 2 ^ 59 * Real.cos x :=
          mul_le_mul_of_nonneg_left hcpos (by norm_num)
        linarith
    _ = |x| * ((59 / 64) / 2 ^ 59) * Real.cos x := by ring

#print axioms tan_up_covers
#print axioms tan_lo_covers
#print axioms tan_range
#print axioms tan_kernel_error

end Verified.Examples.TanKernelPoly
