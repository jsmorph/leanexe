import LeanExe.ProofKit.TaylorCheck
import LeanExe.ProofKit.GammaThresholds
import Verified.Examples.TgammaFactsBase
import Verified.Examples.GammaPi

/-!
The definitions of the tables and kernel polynomials of `cr_tgamma`'s helpers `as_logd`, `as_expd`,
and `as_sinpid` (`tgamma.c` lines 858-1056, commit `ff2f71f6`), read from the port's
`Tgamma.logdTable`, `Tgamma.expdTable`, and `Tgamma.sinpidTable` in the forms of the floating-point
proof's statements, and the kernel checks that enclose a logarithm (`logClose`) and an exponential
(`expClose`) by Taylor sums of the exponential at rational points, and the bounds on a sine kernel
(`sin_kernel`) and a cosine kernel (`cos_kernel`) in `d²` from kernel checks of Taylor models.
`TgammaLogTables`, `TgammaExpTables`, and `TgammaSinTables` bound the tables and kernels, with one
kernel check per table entry.
-/

namespace Verified.Examples.TgammaKernelBase

open Real LeanExe.ProofKit PolyBound TaylorModel TaylorRemainder TaylorCheck RatExpLog
  GammaThresholds TgammaFactsBase

/-! ### Definitions in the forms of the statements -/

/-- The kernel of `asLogd`: `log (1 + z) ≈ z + z² logPoly z`. -/
def logPolyList : List ℚ := coeffs Tgamma.logdTable 260 1 4

/-- `asLogd`'s reciprocals `r1` and `r2`. -/
def r1 (i : ℕ) : ℚ := q Tgamma.logdTable (64 + i)

def r2 (i : ℕ) : ℚ := q Tgamma.logdTable (97 + i)

/-- `asLogd`'s logarithms `l1 ≈ -log r1` and `l2 ≈ -log r2`, as double-doubles. -/
def l1 (i : ℕ) : ℚ := q Tgamma.logdTable (130 + 2 * i) + q Tgamma.logdTable (131 + 2 * i)

def l2 (i : ℕ) : ℚ := q Tgamma.logdTable (196 + 2 * i) + q Tgamma.logdTable (197 + 2 * i)

/-- `asLogd`'s `ln 2`. -/
def ln2 : ℚ := ratOfWord 0x3FE62E42FEF80000 + ratOfWord 0x3DB1CF79ABC9E3B4

/-- The kernel of `asExpd`: `exp (X ln 2/1024) ≈ 1 + X expPoly X`. -/
def expPolyList : List ℚ :=
  (q Tgamma.expdTable 128 + q Tgamma.expdTable 129) :: coeffs Tgamma.expdTable 130 2 4

/-- `asExpd`'s tables `E0 ≈ 2 ^ (i/32)` and `E1 ≈ 2 ^ (i/1024)`, as double-doubles. -/
def e0 (i : ℕ) : ℚ := q Tgamma.expdTable (2 * i) + q Tgamma.expdTable (2 * i + 1)

def e1 (i : ℕ) : ℚ := q Tgamma.expdTable (64 + 2 * i) + q Tgamma.expdTable (65 + 2 * i)

/-- `asExpd`'s `1024/ln 2`. -/
def invLn2 : ℚ := ratOfWord 0x40971547652B82FE + ratOfWord 0x3D1777D0FFDA0D24

/-- `asSinpid`'s table `st k ≈ sin (k π/128)`, as double-doubles. -/
def st (k : ℕ) : ℚ := q Tgamma.sinpidTable (2 * k) + q Tgamma.sinpidTable (2 * k + 1)

/-- The kernels of `asSinpid` in `u = d²`, with the code's corrections `s0` and `c0`. -/
def sinPolyList : List ℚ :=
  (q Tgamma.sinpidTable 134 + ratOfWord 0x3C31A624B88C9448) :: coeffs Tgamma.sinpidTable 135 1 3

def cosPolyList : List ℚ :=
  (q Tgamma.sinpidTable 130 + ratOfWord 0xBBD692B66E3CF6E8) :: coeffs Tgamma.sinpidTable 131 1 3

/-- `tgammaWith`'s `π`. -/
def piDD : ℚ := ratOfWord 0x400921FB54442D18 + ratOfWord 0x3CA1A62633145C07

/-! ### Enclosures of logarithms and exponentials -/

/-- The kernel check that `lo ≤ log a ≤ hi`. -/
def logEncOk (a lo hi : ℚ) : Bool :=
  decide (0 < a) && decide (qabs lo ≤ 1) && decide (qabs hi ≤ 1) &&
    decide (qeval (expCoeffs 40) lo + expRem 40 ≤ a) &&
    decide (a ≤ qeval (expCoeffs 40) hi - expRem 40)

theorem logEnc {a lo hi : ℚ} (h : logEncOk a lo hi = true) :
    (lo : ℝ) ≤ Real.log a ∧ Real.log a ≤ hi := by
  simp only [logEncOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ha, hlo⟩, hhi⟩, h1⟩, h2⟩ := h
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hlo' : |(lo : ℝ)| ≤ 1 := by rw [← qabs_cast]; exact_mod_cast hlo
  have hhi' : |(hi : ℝ)| ≤ 1 := by rw [← qabs_cast]; exact_mod_cast hhi
  have e1 := (abs_le.mp (exp_qeval_le lo hlo' 40 (by norm_num))).2
  have e2 := (abs_le.mp (exp_qeval_le hi hhi' 40 (by norm_num))).1
  have h1r : (((qeval (expCoeffs 40) lo + expRem 40 : ℚ)) : ℝ) ≤ a := by exact_mod_cast h1
  have h2r : (a : ℝ) ≤ ((qeval (expCoeffs 40) hi - expRem 40 : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h1r h2r
  constructor
  · rw [le_log_iff_exp_le har]
    linarith
  · rw [log_le_iff_le_exp har]
    linarith

/-- The kernel check that `|l + log a| ≤ ε` through `lo ≤ log a ≤ hi`. -/
def logCloseOk (a l lo hi ε : ℚ) : Bool :=
  logEncOk a lo hi && decide (qabs (l + lo) ≤ ε) && decide (qabs (l + hi) ≤ ε)

theorem logClose {a l lo hi ε : ℚ} (h : logCloseOk a l lo hi ε = true) :
    |(l : ℝ) + Real.log a| ≤ ε := by
  simp only [logCloseOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨he, h1⟩, h2⟩ := h
  obtain ⟨hlo, hhi⟩ := logEnc he
  have h1r : |((l + lo : ℚ) : ℝ)| ≤ ε := by rw [← qabs_cast]; exact_mod_cast h1
  have h2r : |((l + hi : ℚ) : ℝ)| ≤ ε := by rw [← qabs_cast]; exact_mod_cast h2
  push_cast at h1r h2r
  rw [abs_le] at h1r h2r ⊢
  constructor <;> linarith

/-- The kernel check that `|e - exp x| ≤ ε` for `xlo ≤ x ≤ xhi`. -/
def expCloseOk (e xlo xhi ε : ℚ) : Bool :=
  decide (qabs xlo ≤ 1) && decide (qabs xhi ≤ 1) &&
    decide (e - ε ≤ qeval (expCoeffs 40) xlo - expRem 40) &&
    decide (qeval (expCoeffs 40) xhi + expRem 40 ≤ e + ε)

theorem expClose {e xlo xhi ε : ℚ} (h : expCloseOk e xlo xhi ε = true) {x : ℝ}
    (hlo : (xlo : ℝ) ≤ x) (hhi : x ≤ xhi) : |(e : ℝ) - Real.exp x| ≤ ε := by
  simp only [expCloseOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hlo' : |(xlo : ℝ)| ≤ 1 := by rw [← qabs_cast]; exact_mod_cast h1
  have hhi' : |(xhi : ℝ)| ≤ 1 := by rw [← qabs_cast]; exact_mod_cast h2
  have e1 := (abs_le.mp (exp_qeval_le xlo hlo' 40 (by norm_num))).1
  have e2 := (abs_le.mp (exp_qeval_le xhi hhi' 40 (by norm_num))).2
  have h3r : ((e - ε : ℚ) : ℝ) ≤ ((qeval (expCoeffs 40) xlo - expRem 40 : ℚ) : ℝ) := by
    exact_mod_cast h3
  have h4r : ((qeval (expCoeffs 40) xhi + expRem 40 : ℚ) : ℝ) ≤ ((e + ε : ℚ) : ℝ) := by
    exact_mod_cast h4
  push_cast at h3r h4r
  have m1 := Real.exp_le_exp.mpr hlo
  have m2 := Real.exp_le_exp.mpr hhi
  rw [abs_le]
  constructor <;> linarith

theorem eval_zero_lin (b : ℚ) (t : ℝ) : eval [0, b] t = b * t := by
  simp only [eval_cons, eval_nil, Rat.cast_zero, zero_add, mul_zero, add_zero]
  ring

theorem eval_sq (t : ℝ) : eval [0, 0, 1] t = t ^ 2 := by
  simp only [eval_cons, eval_nil, Rat.cast_zero, Rat.cast_one, zero_add, mul_zero, add_zero,
    mul_one]
  ring

/-- `(π/128) · sin (π d/128)/(π d/128) - P (d²)`. -/
def sinErrExpr (P : List ℚ) : TaylorModel.Expr :=
  .add (.mul (.mul (.const (1 / 128)) .pi) (.sinc (.mul .pi (.poly [0, 1 / 128]))))
    (.neg (.polyOf P (.poly [0, 0, 1])))

/-- `-2 (π/256)² (sin (π d/256)/(π d/256))² - P (d²)`. -/
def cosErrExpr (P : List ℚ) : TaylorModel.Expr :=
  .add (.mul (.const (-2 / (256 * 256))) (.mul (.mul .pi .pi)
    (.mul (.sinc (.mul .pi (.poly [0, 1 / 256]))) (.sinc (.mul .pi (.poly [0, 1 / 256]))))))
    (.neg (.polyOf P (.poly [0, 0, 1])))

/-- A kernel check of `sinErrExpr P` on `|d| ≤ 1/2` bounds the sine kernel `P` relative to `d`. -/
theorem sin_kernel (c : Cfg) (hpi : (c.piLo : ℝ) ≤ Real.pi ∧ Real.pi ≤ c.piHi)
    (hr : ((c.r : ℚ) : ℝ) = 1 / 2) (P : List ℚ) (ε : ℚ) (depth : ℕ)
    (hc : exprOk c (sinErrExpr P) ε depth = true) : ∀ d : ℝ, |d| ≤ 1 / 2 →
    |Real.sin (Real.pi * d / 128) - d * eval P (d ^ 2)| ≤ ε * |d| := by
  intro d hd
  have h := exprOk_sound c (sinErrExpr P) _ _ hpi hc (t := d) (by rw [hr]; exact hd)
  simp only [sinErrExpr, TaylorModel.Expr.eval, eval_zero_lin, eval_sq] at h
  push_cast at h
  rcases eq_or_ne d 0 with h0 | h0
  · subst h0
    simp
  · have hπ := Real.pi_ne_zero
    have hne : Real.pi * (1 / 128 * d) ≠ 0 := mul_ne_zero hπ (mul_ne_zero (by norm_num) h0)
    rw [ite_eq_right hne] at h
    have hk : 1 / 128 * Real.pi * (Real.sin (Real.pi * (1 / 128 * d)) / (Real.pi * (1 / 128 * d))) =
        Real.sin (Real.pi * d / 128) / d := by
      rw [show Real.pi * (1 / 128 * d) = Real.pi * d / 128 by ring]
      field_simp
    rw [hk] at h
    have he : Real.sin (Real.pi * d / 128) - d * eval P (d ^ 2) =
        d * (Real.sin (Real.pi * d / 128) / d + -eval P (d ^ 2)) := by
      field_simp
      ring
    rw [he, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg d)

/-- A kernel check of `cosErrExpr P` on `|d| ≤ 1/2` bounds the cosine kernel `P` relative to
`d²`. -/
theorem cos_kernel (c : Cfg) (hpi : (c.piLo : ℝ) ≤ Real.pi ∧ Real.pi ≤ c.piHi)
    (hr : ((c.r : ℚ) : ℝ) = 1 / 2) (P : List ℚ) (ε : ℚ) (depth : ℕ)
    (hc : exprOk c (cosErrExpr P) ε depth = true) : ∀ d : ℝ, |d| ≤ 1 / 2 →
    |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * eval P (d ^ 2))| ≤ ε * d ^ 2 := by
  intro d hd
  have h := exprOk_sound c (cosErrExpr P) _ _ hpi hc (t := d) (by rw [hr]; exact hd)
  simp only [cosErrExpr, TaylorModel.Expr.eval, eval_zero_lin, eval_sq] at h
  push_cast at h
  rcases eq_or_ne d 0 with h0 | h0
  · subst h0
    simp
  · have hπ := Real.pi_ne_zero
    have hne : Real.pi * (1 / 256 * d) ≠ 0 := mul_ne_zero hπ (mul_ne_zero (by norm_num) h0)
    rw [ite_eq_right hne] at h
    have hc : Real.cos (Real.pi * d / 128) = 1 - 2 * Real.sin (Real.pi * (1 / 256 * d)) ^ 2 := by
      rw [show Real.pi * d / 128 = 2 * (Real.pi * (1 / 256 * d)) by ring, Real.cos_two_mul,
        Real.cos_sq']
      ring
    have hk : -2 / (256 * 256) * (Real.pi * Real.pi *
        (Real.sin (Real.pi * (1 / 256 * d)) / (Real.pi * (1 / 256 * d)) *
          (Real.sin (Real.pi * (1 / 256 * d)) / (Real.pi * (1 / 256 * d))))) =
        (Real.cos (Real.pi * d / 128) - 1) / d ^ 2 := by
      rw [hc]
      field_simp
      ring
    rw [hk] at h
    have he : Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * eval P (d ^ 2)) =
        d ^ 2 * ((Real.cos (Real.pi * d / 128) - 1) / d ^ 2 + -eval P (d ^ 2)) := by
      field_simp
      ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg d), mul_comm]
    exact mul_le_mul_of_nonneg_right h (sq_nonneg d)

#print axioms logClose
#print axioms expClose
#print axioms sin_kernel
#print axioms cos_kernel

end Verified.Examples.TgammaKernelBase
