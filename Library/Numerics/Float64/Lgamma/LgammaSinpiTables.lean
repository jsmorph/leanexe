import Library.Numerics.Float64.Tgamma.TgammaKernelBase
import Library.Numerics.Float64.Lgamma.Compiled

/-!
Bounds on the table and kernels of `as_sinpipid` (`lgamma.c` lines 1249-1328, commit
`ff2f71f6`), read from the port's `Lgamma.sinpiTable`: the double-double table
`stpi k ≈ sin (k π/128)/π` for `k ≤ 64` within `2 ^ -100`, by Taylor models of
`2 sin (k π/256) cos (k π/256)/π` with `π` within `2 ^ -128`; the sine and cosine kernels in `d²`
within `2 ^ -73 |d|` and `2 ^ -76 d²` (`Library.Numerics.Float64.Tgamma.TgammaKernelBase.sin_kernel`, `cos_kernel`); and the
polynomial of the branch next to an integer, `sin (π z)/π ≈ z + z³ P (z²)` for `|z| ≤ 1/80`, within
`2 ^ -76 |z|`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaSinpiTables

open Real LeanExe.ProofKit PolyBound TaylorModel TaylorRemainder TaylorCheck RatExpLog
  GammaThresholds TgammaFactsBase TgammaKernelBase

/-- `as_sinpipid`'s table `stpi k ≈ sin (k π/128)/π`, as double-doubles. -/
def stpi (k : ℕ) : ℚ := q Lgamma.sinpiTable (2 * k) + q Lgamma.sinpiTable (2 * k + 1)

/-- The sine and cosine kernels in `d²`, with the code's corrections `s0` and `c0`. -/
def sinKernelList : List ℚ :=
  (q Lgamma.sinpiTable 134 + ratOfWord 0x3C31A624B88C9448) :: coeffs Lgamma.sinpiTable 135 1 3

def cosKernelList : List ℚ :=
  (q Lgamma.sinpiTable 130 + ratOfWord 0xBBD692B66E3CF6E8) :: coeffs Lgamma.sinpiTable 131 1 3

/-- The polynomial of the branch next to an integer: `sin (π z)/π ≈ z + z³ P (z²)`. -/
def nearList : List ℚ :=
  (q Lgamma.sinpiTable 138 + q Lgamma.sinpiTable 139) :: coeffs Lgamma.sinpiTable 140 1 3

/-- `2 sin (k π/256) cos (k π/256)/π - stpi k`, which is `sin (k π/128)/π - stpi k`. -/
def stpiExpr (k : ℕ) : TaylorModel.Expr :=
  .add (.mul (.mul (.const 2) (.mul (.sin (.mul .pi (.const (k / 256))))
    (.cos (.mul .pi (.const (k / 256)))))) (.inv .pi)) (.const (-stpi k))

/-- The parameters for the table: radius 0, 130 bits, at most 60 series terms with factor below
`2 ^ -130`, and `π` within `2 ^ -128`. -/
def cfgP : Cfg := ⟨0, 4, 130, 60, 1 / 2 ^ 130, Library.Numerics.Float64.Tgamma.GammaPi.piLo128, Library.Numerics.Float64.Tgamma.GammaPi.piHi128⟩

theorem stpi_checked_0 : exprOk cfgP (stpiExpr (0 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_1 : exprOk cfgP (stpiExpr (1 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_2 : exprOk cfgP (stpiExpr (2 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_3 : exprOk cfgP (stpiExpr (3 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_4 : exprOk cfgP (stpiExpr (4 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_5 : exprOk cfgP (stpiExpr (5 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_6 : exprOk cfgP (stpiExpr (6 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_7 : exprOk cfgP (stpiExpr (7 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_8 : exprOk cfgP (stpiExpr (8 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_9 : exprOk cfgP (stpiExpr (9 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_10 : exprOk cfgP (stpiExpr (10 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_11 : exprOk cfgP (stpiExpr (11 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_12 : exprOk cfgP (stpiExpr (12 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_13 : exprOk cfgP (stpiExpr (13 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_14 : exprOk cfgP (stpiExpr (14 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_15 : exprOk cfgP (stpiExpr (15 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_16 : exprOk cfgP (stpiExpr (16 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_17 : exprOk cfgP (stpiExpr (17 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_18 : exprOk cfgP (stpiExpr (18 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_19 : exprOk cfgP (stpiExpr (19 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_20 : exprOk cfgP (stpiExpr (20 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_21 : exprOk cfgP (stpiExpr (21 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_22 : exprOk cfgP (stpiExpr (22 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_23 : exprOk cfgP (stpiExpr (23 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_24 : exprOk cfgP (stpiExpr (24 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_25 : exprOk cfgP (stpiExpr (25 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_26 : exprOk cfgP (stpiExpr (26 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_27 : exprOk cfgP (stpiExpr (27 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_28 : exprOk cfgP (stpiExpr (28 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_29 : exprOk cfgP (stpiExpr (29 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_30 : exprOk cfgP (stpiExpr (30 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_31 : exprOk cfgP (stpiExpr (31 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_32 : exprOk cfgP (stpiExpr (32 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_33 : exprOk cfgP (stpiExpr (33 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_34 : exprOk cfgP (stpiExpr (34 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_35 : exprOk cfgP (stpiExpr (35 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_36 : exprOk cfgP (stpiExpr (36 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_37 : exprOk cfgP (stpiExpr (37 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_38 : exprOk cfgP (stpiExpr (38 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_39 : exprOk cfgP (stpiExpr (39 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_40 : exprOk cfgP (stpiExpr (40 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_41 : exprOk cfgP (stpiExpr (41 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_42 : exprOk cfgP (stpiExpr (42 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_43 : exprOk cfgP (stpiExpr (43 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_44 : exprOk cfgP (stpiExpr (44 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_45 : exprOk cfgP (stpiExpr (45 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_46 : exprOk cfgP (stpiExpr (46 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_47 : exprOk cfgP (stpiExpr (47 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_48 : exprOk cfgP (stpiExpr (48 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_49 : exprOk cfgP (stpiExpr (49 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_50 : exprOk cfgP (stpiExpr (50 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_51 : exprOk cfgP (stpiExpr (51 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_52 : exprOk cfgP (stpiExpr (52 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_53 : exprOk cfgP (stpiExpr (53 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_54 : exprOk cfgP (stpiExpr (54 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_55 : exprOk cfgP (stpiExpr (55 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_56 : exprOk cfgP (stpiExpr (56 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_57 : exprOk cfgP (stpiExpr (57 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_58 : exprOk cfgP (stpiExpr (58 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_59 : exprOk cfgP (stpiExpr (59 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_60 : exprOk cfgP (stpiExpr (60 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_61 : exprOk cfgP (stpiExpr (61 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_62 : exprOk cfgP (stpiExpr (62 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_63 : exprOk cfgP (stpiExpr (63 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked_64 : exprOk cfgP (stpiExpr (64 : ℕ)) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem stpi_checked : ∀ k < 65, exprOk cfgP (stpiExpr k) (1 / 2 ^ 100) 0 = true := by
  intro k hk
  interval_cases k
  exacts [stpi_checked_0, stpi_checked_1, stpi_checked_2, stpi_checked_3, stpi_checked_4,
    stpi_checked_5, stpi_checked_6, stpi_checked_7, stpi_checked_8, stpi_checked_9, stpi_checked_10,
    stpi_checked_11, stpi_checked_12, stpi_checked_13, stpi_checked_14, stpi_checked_15,
    stpi_checked_16, stpi_checked_17, stpi_checked_18, stpi_checked_19, stpi_checked_20,
    stpi_checked_21, stpi_checked_22, stpi_checked_23, stpi_checked_24, stpi_checked_25,
    stpi_checked_26, stpi_checked_27, stpi_checked_28, stpi_checked_29, stpi_checked_30,
    stpi_checked_31, stpi_checked_32, stpi_checked_33, stpi_checked_34, stpi_checked_35,
    stpi_checked_36, stpi_checked_37, stpi_checked_38, stpi_checked_39, stpi_checked_40,
    stpi_checked_41, stpi_checked_42, stpi_checked_43, stpi_checked_44, stpi_checked_45,
    stpi_checked_46, stpi_checked_47, stpi_checked_48, stpi_checked_49, stpi_checked_50,
    stpi_checked_51, stpi_checked_52, stpi_checked_53, stpi_checked_54, stpi_checked_55,
    stpi_checked_56, stpi_checked_57, stpi_checked_58, stpi_checked_59, stpi_checked_60,
    stpi_checked_61, stpi_checked_62, stpi_checked_63, stpi_checked_64]

theorem stpi_close : ∀ k ≤ 64,
    |(stpi k : ℝ) - Real.sin (k * Real.pi / 128) / Real.pi| ≤ 1 / 2 ^ 100 := by
  intro k hk
  have h := exprOk_sound cfgP (stpiExpr k) _ _ Library.Numerics.Float64.Tgamma.GammaPi.pi_bounds128 (stpi_checked k (by omega))
    (t := 0) (by simp [cfgP])
  simp only [stpiExpr, TaylorModel.Expr.eval] at h
  push_cast at h
  have hs : 2 * (Real.sin (Real.pi * (k / 256)) * Real.cos (Real.pi * (k / 256))) * Real.pi⁻¹ =
      Real.sin (k * Real.pi / 128) / Real.pi := by
    rw [← mul_assoc, ← Real.sin_two_mul, div_eq_mul_inv]
    congr 2
    ring
  rw [hs] at h
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The parameters for the kernels on `|d| ≤ 1/2`. -/
def cfgK : Cfg := ⟨1 / 2, 16, 120, 60, 1 / 2 ^ 120, Library.Numerics.Float64.Tgamma.GammaPi.piLo128, Library.Numerics.Float64.Tgamma.GammaPi.piHi128⟩

theorem sinK_checked : exprOk cfgK (sinErrExpr sinKernelList) (1 / 2 ^ 73) 2 = true := by
  decide +kernel

theorem cosK_checked : exprOk cfgK (cosErrExpr cosKernelList) (1 / 2 ^ 76) 2 = true := by
  decide +kernel

theorem sin_kernel_fact : ∀ d : ℝ, |d| ≤ 1 / 2 →
    |Real.sin (Real.pi * d / 128) - d * eval sinKernelList (d ^ 2)| ≤ 1 / 2 ^ 73 * |d| := by
  intro d hd
  have h := sin_kernel cfgK Library.Numerics.Float64.Tgamma.GammaPi.pi_bounds128 (by norm_num [cfgK]) _ _ _ sinK_checked d hd
  push_cast at h
  exact h

theorem cos_kernel_fact : ∀ d : ℝ, |d| ≤ 1 / 2 →
    |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * eval cosKernelList (d ^ 2))| ≤
      1 / 2 ^ 76 * d ^ 2 := by
  intro d hd
  have h := cos_kernel cfgK Library.Numerics.Float64.Tgamma.GammaPi.pi_bounds128 (by norm_num [cfgK]) _ _ _ cosK_checked d hd
  push_cast at h
  exact h

/-- `sin (π z)/(π z) - (1 + z² P (z²))`. -/
def nearErrExpr : TaylorModel.Expr :=
  .add (.sinc (.mul .pi .var))
    (.neg (.add (.const 1) (.mul (.poly [0, 0, 1]) (.polyOf nearList (.poly [0, 0, 1])))))

/-- The parameters for the branch next to an integer: radius `1/80`. -/
def cfgN : Cfg := ⟨1 / 80, 12, 120, 60, 1 / 2 ^ 120, Library.Numerics.Float64.Tgamma.GammaPi.piLo128, Library.Numerics.Float64.Tgamma.GammaPi.piHi128⟩

theorem near_checked : exprOk cfgN nearErrExpr (1 / 2 ^ 76) 2 = true := by
  decide +kernel

theorem near_fact : ∀ z : ℝ, |z| ≤ 1 / 80 →
    |Real.sin (Real.pi * z) / Real.pi - (z + z ^ 3 * eval nearList (z ^ 2))| ≤
      1 / 2 ^ 76 * |z| := by
  intro z hz
  have h := exprOk_sound cfgN nearErrExpr _ _ Library.Numerics.Float64.Tgamma.GammaPi.pi_bounds128 near_checked (t := z)
    (by simp only [cfgN]; push_cast; exact hz)
  simp only [nearErrExpr, TaylorModel.Expr.eval, eval_sq] at h
  push_cast at h
  rcases eq_or_ne z 0 with h0 | h0
  · subst h0
    simp
  · have hπ := Real.pi_ne_zero
    simp only [mul_ne_zero hπ h0, ↓reduceIte] at h
    have he : Real.sin (Real.pi * z) / Real.pi - (z + z ^ 3 * eval nearList (z ^ 2)) =
        z * (Real.sin (Real.pi * z) / (Real.pi * z) + -(1 + z ^ 2 * eval nearList (z ^ 2))) := by
      field_simp
      ring
    rw [he, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg z)

#print axioms stpi_close
#print axioms sin_kernel_fact
#print axioms cos_kernel_fact
#print axioms near_fact

end Library.Numerics.Float64.Lgamma.LgammaSinpiTables
