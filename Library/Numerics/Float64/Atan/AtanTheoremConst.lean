import Library.Numerics.Float64.Atan.AtanTheoremPoly
import LeanExe.ProofKit.TaylorRemainder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
The constants of `Atan.atan` against the arctangents they stand for, and two facts about
`arctan`.  Each pair `atanhi[i] + atanlo[i]` lies within `2 ^ -64` of `arctan 0.5`, `π/4`,
`arctan 1.5`, and `π/2`.  The arctangents of `1/2` and `2/3` come from the Taylor polynomials of
`TaylorRemainder.atan_remainder` evaluated in `ℚ` by the kernel, `arctan 1.5 = π/2 - arctan (2/3)`,
and `π` from Mathlib's twenty-digit bounds.  `arctan` is 1-Lipschitz, since its derivative is at
most 1.
-/

namespace Library.Numerics.Float64.Atan.AtanTheoremConst
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound TaylorRemainder

set_option exponentiation.threshold 4096

/-- The value of a polynomial at a rational point, in `ℚ`. -/
def evalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * evalQ p x

theorem eval_cast (p : List ℚ) (q : ℚ) : eval p (q : ℝ) = ((evalQ p q : ℚ) : ℝ) := by
  induction p with
  | nil => simp [evalQ]
  | cons a p ih => simp [eval_cons, evalQ, ih]

theorem arctan_lipschitz (a b : ℝ) : |Real.arctan a - Real.arctan b| ≤ |a - b| := by
  have hd : ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt Real.arctan (1 / (1 + x ^ 2)) Set.univ x :=
    fun x _ => (Real.hasDerivAt_arctan x).hasDerivWithinAt
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖1 / (1 + x ^ 2)‖ ≤ 1 := by
    intro x _
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith [sq_nonneg x]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb convex_univ
    (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using h

theorem abs_arctan_le (x : ℝ) : |Real.arctan x| ≤ |x| := by
  have h := arctan_lipschitz x 0
  rwa [Real.arctan_zero, sub_zero, sub_zero] at h

/-- `π` within `5 · 10 ^ -21` of the midpoint of Mathlib's twenty-digit bounds. -/
theorem pi_close : |Real.pi - 3141592653589793238465 / 10 ^ 21| ≤ 5 / 10 ^ 21 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  rw [abs_le]
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- A sum of word values within `δ` of a rational, checked by the kernel. -/
theorem words_close (h l : UInt64) (q δ : ℚ)
    (hc : qabs (ratOfWord h + ratOfWord l - q) ≤ δ) :
    |value h + value l - (q : ℝ)| ≤ (δ : ℝ) := by
  rw [← ratOfWord_cast, ← ratOfWord_cast]
  have := qabs_cast (ratOfWord h + ratOfWord l - q)
  push_cast at this
  rw [← this]
  exact_mod_cast hc

theorem atan_half :
    |value 0x3FDDAC670561BB4F + value 0x3C7A2B7F222F65E2 - Real.arctan (1 / 2)| ≤ 1 / 2 ^ 64 := by
  have hr := atan_remainder (1 / 2) (by norm_num) 36
  have he : (1 / 2 : ℝ) * eval (atanCoeffs 36) ((1 / 2) ^ 2) =
      (((1 / 2) * evalQ (atanCoeffs 36) (1 / 4) : ℚ) : ℝ) := by
    rw [show ((1 / 2 : ℝ)) ^ 2 = ((1 / 4 : ℚ) : ℝ) by norm_num, eval_cast]
    push_cast
    ring
  rw [he] at hr
  have hc := words_close 0x3FDDAC670561BB4F 0x3C7A2B7F222F65E2
    ((1 / 2) * evalQ (atanCoeffs 36) (1 / 4)) (1 / 2 ^ 70) (by decide +kernel)
  have hn : |(1 / 2 : ℝ)| ^ (2 * 36 + 1) / (1 - (1 / 2) ^ 2) ≤ 1 / 2 ^ 70 := by norm_num
  calc |value 0x3FDDAC670561BB4F + value 0x3C7A2B7F222F65E2 - Real.arctan (1 / 2)|
      ≤ |value 0x3FDDAC670561BB4F + value 0x3C7A2B7F222F65E2 -
          (((1 / 2) * evalQ (atanCoeffs 36) (1 / 4) : ℚ) : ℝ)| +
        |Real.arctan (1 / 2) - (((1 / 2) * evalQ (atanCoeffs 36) (1 / 4) : ℚ) : ℝ)| := by
        rw [abs_sub_comm (Real.arctan (1 / 2))]
        exact abs_sub_le _ _ _
    _ ≤ 1 / 2 ^ 70 + 1 / 2 ^ 70 := add_le_add (hc.trans (le_of_eq (by norm_num))) (hr.trans hn)
    _ ≤ 1 / 2 ^ 64 := by norm_num

theorem atan_two_thirds :
    |Real.arctan (2 / 3) - (((2 / 3) * evalQ (atanCoeffs 64) (4 / 9) : ℚ) : ℝ)| ≤ 1 / 2 ^ 74 := by
  have hr := atan_remainder (2 / 3) (by norm_num) 64
  have he : (2 / 3 : ℝ) * eval (atanCoeffs 64) ((2 / 3) ^ 2) =
      (((2 / 3) * evalQ (atanCoeffs 64) (4 / 9) : ℚ) : ℝ) := by
    rw [show ((2 / 3 : ℝ)) ^ 2 = ((4 / 9 : ℚ) : ℝ) by norm_num, eval_cast]
    push_cast
    ring
  rw [he] at hr
  exact hr.trans (by norm_num)

/-- `atanhi[1] + atanlo[1]` against `π/4 = arctan 1`. -/
theorem atan_one :
    |value 0x3FE921FB54442D18 + value 0x3C81A62633145C07 - Real.arctan 1| ≤ 1 / 2 ^ 64 := by
  rw [Real.arctan_one]
  have hp := pi_close
  have hc := words_close 0x3FE921FB54442D18 0x3C81A62633145C07
    (3141592653589793238465 / 10 ^ 21 / 4) (1 / 2 ^ 68) (by decide +kernel)
  push_cast at hc
  rw [abs_le] at hp hc ⊢
  constructor <;> nlinarith [hp.1, hp.2, hc.1, hc.2]

/-- `atanhi[3] + atanlo[3]` against `π/2`. -/
theorem atan_inf :
    |value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2| ≤ 1 / 2 ^ 64 := by
  have hp := pi_close
  have hc := words_close 0x3FF921FB54442D18 0x3C91A62633145C07
    (3141592653589793238465 / 10 ^ 21 / 2) (1 / 2 ^ 68) (by decide +kernel)
  push_cast at hc
  rw [abs_le] at hp hc ⊢
  constructor <;> nlinarith [hp.1, hp.2, hc.1, hc.2]

/-- `atanhi[2] + atanlo[2]` against `arctan 1.5 = π/2 - arctan (2/3)`. -/
theorem atan_three_halves :
    |value 0x3FEF730BD281F69B + value 0x3C7007887AF0CBBD - Real.arctan (3 / 2)| ≤ 1 / 2 ^ 64 := by
  have hinv := Real.arctan_inv_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)
  rw [show ((2 : ℝ) / 3)⁻¹ = 3 / 2 by norm_num] at hinv
  rw [hinv]
  have hp := pi_close
  have ht := atan_two_thirds
  have hc := words_close 0x3FEF730BD281F69B 0x3C7007887AF0CBBD
    (3141592653589793238465 / 10 ^ 21 / 2 - (2 / 3) * evalQ (atanCoeffs 64) (4 / 9)) (1 / 2 ^ 68)
    (by decide +kernel)
  push_cast at hc ht
  rw [abs_le] at hp hc ht ⊢
  constructor <;> nlinarith [hp.1, hp.2, hc.1, hc.2, ht.1, ht.2]

#print axioms arctan_lipschitz
#print axioms abs_arctan_le
#print axioms atan_half
#print axioms atan_one
#print axioms atan_inf
#print axioms atan_three_halves

end Library.Numerics.Float64.Atan.AtanTheoremConst
