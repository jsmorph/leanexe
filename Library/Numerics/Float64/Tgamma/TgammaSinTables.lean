import Library.Numerics.Float64.Tgamma.TgammaKernelBase

/-!
Bounds on `as_sinpid`'s table and kernels (`tgamma.c`, commit `ff2f71f6`): `sin (k π/128)`
for `k ≤ 64` by Taylor models of `2 sin (k π/256) cos (k π/256)` with `π` within `2 ^ -128`
(`GammaPi`), the kernels `sin (π d/128) ≈ d P (d²)` and `cos (π d/128) ≈ 1 + d² Q (d²)` on
`|d| ≤ 1/2` through `sin a/a`, and the split `π`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaSinTables

open Real LeanExe.ProofKit PolyBound TaylorModel TaylorRemainder TaylorCheck RatExpLog
  GammaThresholds TgammaFactsBase TgammaKernelBase

/-! ### `asSinpid` -/

/-- `2 sin (k π/256) cos (k π/256) - st k`, which is `sin (k π/128) - st k`. -/
def stExpr (k : ℕ) : TaylorModel.Expr :=
  .add (.mul (.const 2) (.mul (.sin (.mul .pi (.const (k / 256))))
    (.cos (.mul .pi (.const (k / 256)))))) (.const (-st k))

/-- The parameters for the constants: radius 0. -/
def cfgPoint : Cfg := ⟨0, 4, 120, 40, 1 / 2 ^ 110, GammaPi.piLo128, GammaPi.piHi128⟩

theorem st_checked_0 : exprOk cfgPoint (stExpr (0 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_1 : exprOk cfgPoint (stExpr (1 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_2 : exprOk cfgPoint (stExpr (2 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_3 : exprOk cfgPoint (stExpr (3 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_4 : exprOk cfgPoint (stExpr (4 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_5 : exprOk cfgPoint (stExpr (5 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_6 : exprOk cfgPoint (stExpr (6 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_7 : exprOk cfgPoint (stExpr (7 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_8 : exprOk cfgPoint (stExpr (8 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_9 : exprOk cfgPoint (stExpr (9 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_10 : exprOk cfgPoint (stExpr (10 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_11 : exprOk cfgPoint (stExpr (11 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_12 : exprOk cfgPoint (stExpr (12 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_13 : exprOk cfgPoint (stExpr (13 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_14 : exprOk cfgPoint (stExpr (14 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_15 : exprOk cfgPoint (stExpr (15 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_16 : exprOk cfgPoint (stExpr (16 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_17 : exprOk cfgPoint (stExpr (17 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_18 : exprOk cfgPoint (stExpr (18 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_19 : exprOk cfgPoint (stExpr (19 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_20 : exprOk cfgPoint (stExpr (20 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_21 : exprOk cfgPoint (stExpr (21 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_22 : exprOk cfgPoint (stExpr (22 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_23 : exprOk cfgPoint (stExpr (23 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_24 : exprOk cfgPoint (stExpr (24 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_25 : exprOk cfgPoint (stExpr (25 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_26 : exprOk cfgPoint (stExpr (26 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_27 : exprOk cfgPoint (stExpr (27 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_28 : exprOk cfgPoint (stExpr (28 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_29 : exprOk cfgPoint (stExpr (29 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_30 : exprOk cfgPoint (stExpr (30 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_31 : exprOk cfgPoint (stExpr (31 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_32 : exprOk cfgPoint (stExpr (32 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_33 : exprOk cfgPoint (stExpr (33 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_34 : exprOk cfgPoint (stExpr (34 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_35 : exprOk cfgPoint (stExpr (35 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_36 : exprOk cfgPoint (stExpr (36 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_37 : exprOk cfgPoint (stExpr (37 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_38 : exprOk cfgPoint (stExpr (38 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_39 : exprOk cfgPoint (stExpr (39 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_40 : exprOk cfgPoint (stExpr (40 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_41 : exprOk cfgPoint (stExpr (41 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_42 : exprOk cfgPoint (stExpr (42 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_43 : exprOk cfgPoint (stExpr (43 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_44 : exprOk cfgPoint (stExpr (44 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_45 : exprOk cfgPoint (stExpr (45 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_46 : exprOk cfgPoint (stExpr (46 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_47 : exprOk cfgPoint (stExpr (47 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_48 : exprOk cfgPoint (stExpr (48 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_49 : exprOk cfgPoint (stExpr (49 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_50 : exprOk cfgPoint (stExpr (50 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_51 : exprOk cfgPoint (stExpr (51 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_52 : exprOk cfgPoint (stExpr (52 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_53 : exprOk cfgPoint (stExpr (53 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_54 : exprOk cfgPoint (stExpr (54 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_55 : exprOk cfgPoint (stExpr (55 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_56 : exprOk cfgPoint (stExpr (56 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_57 : exprOk cfgPoint (stExpr (57 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_58 : exprOk cfgPoint (stExpr (58 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_59 : exprOk cfgPoint (stExpr (59 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_60 : exprOk cfgPoint (stExpr (60 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_61 : exprOk cfgPoint (stExpr (61 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_62 : exprOk cfgPoint (stExpr (62 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_63 : exprOk cfgPoint (stExpr (63 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked_64 : exprOk cfgPoint (stExpr (64 : ℕ)) (1 / 2 ^ 80) 0 = true := by
  decide +kernel

theorem st_checked :
    ∀ k < 65, exprOk cfgPoint (stExpr k) (1 / 2 ^ 80) 0 = true := by
  intro k hk
  interval_cases k
  exacts [st_checked_0, st_checked_1, st_checked_2, st_checked_3, st_checked_4, st_checked_5,
    st_checked_6, st_checked_7, st_checked_8, st_checked_9, st_checked_10, st_checked_11,
    st_checked_12, st_checked_13, st_checked_14, st_checked_15, st_checked_16, st_checked_17,
    st_checked_18, st_checked_19, st_checked_20, st_checked_21, st_checked_22, st_checked_23,
    st_checked_24, st_checked_25, st_checked_26, st_checked_27, st_checked_28, st_checked_29,
    st_checked_30, st_checked_31, st_checked_32, st_checked_33, st_checked_34, st_checked_35,
    st_checked_36, st_checked_37, st_checked_38, st_checked_39, st_checked_40, st_checked_41,
    st_checked_42, st_checked_43, st_checked_44, st_checked_45, st_checked_46, st_checked_47,
    st_checked_48, st_checked_49, st_checked_50, st_checked_51, st_checked_52, st_checked_53,
    st_checked_54, st_checked_55, st_checked_56, st_checked_57, st_checked_58, st_checked_59,
    st_checked_60, st_checked_61, st_checked_62, st_checked_63, st_checked_64]

theorem st_close : ∀ k ≤ 64, |(st k : ℝ) - Real.sin (k * Real.pi / 128)| ≤ 1 / 2 ^ 80 := by
  intro k hk
  have h := exprOk_sound cfgPoint (stExpr k) _ _ GammaPi.pi_bounds128 (st_checked k (by omega))
    (t := 0) (by simp [cfgPoint])
  simp only [stExpr, TaylorModel.Expr.eval] at h
  push_cast at h
  have hs : 2 * (Real.sin (Real.pi * (k / 256)) * Real.cos (Real.pi * (k / 256))) =
      Real.sin (k * Real.pi / 128) := by
    rw [← mul_assoc, ← Real.sin_two_mul]
    congr 1
    ring
  rw [hs] at h
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The parameters for the kernel polynomials on `|d| ≤ 1/2`. -/
def cfgSin : Cfg := ⟨1 / 2, 14, 110, 40, 1 / 2 ^ 110, GammaPi.piLo128, GammaPi.piHi128⟩

theorem sinErr_checked : exprOk cfgSin (sinErrExpr sinPolyList) (1 / 2 ^ 71) 2 = true := by
  decide +kernel

theorem cosErr_checked : exprOk cfgSin (cosErrExpr cosPolyList) (1 / 2 ^ 78) 2 = true := by
  decide +kernel

theorem sin_poly : ∀ d : ℝ, |d| ≤ 1 / 2 →
    |Real.sin (Real.pi * d / 128) - d * eval sinPolyList (d ^ 2)| ≤ 1 / 2 ^ 71 * |d| := by
  intro d hd
  have h := sin_kernel cfgSin GammaPi.pi_bounds128 (by norm_num [cfgSin]) _ _ _ sinErr_checked d hd
  push_cast at h
  exact h

theorem cos_poly : ∀ d : ℝ, |d| ≤ 1 / 2 →
    |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * eval cosPolyList (d ^ 2))| ≤
      1 / 2 ^ 78 * d ^ 2 := by
  intro d hd
  have h := cos_kernel cfgSin GammaPi.pi_bounds128 (by norm_num [cfgSin]) _ _ _ cosErr_checked d hd
  push_cast at h
  exact h

theorem piDD_checked :
    qabs (piDD - GammaPi.piLo128) ≤ 1 / 2 ^ 80 ∧ qabs (piDD - GammaPi.piHi128) ≤ 1 / 2 ^ 80 := by
  decide +kernel

theorem piDD_close : |(piDD : ℝ) - Real.pi| ≤ 1 / 2 ^ 80 := by
  obtain ⟨h1, h2⟩ := piDD_checked
  obtain ⟨hl, hh⟩ := GammaPi.pi_bounds128
  have h1r : |((piDD - GammaPi.piLo128 : ℚ) : ℝ)| ≤ ((1 / 2 ^ 80 : ℚ) : ℝ) := by
    rw [← qabs_cast]; exact_mod_cast h1
  have h2r : |((piDD - GammaPi.piHi128 : ℚ) : ℝ)| ≤ ((1 / 2 ^ 80 : ℚ) : ℝ) := by
    rw [← qabs_cast]; exact_mod_cast h2
  push_cast at h1r h2r
  rw [abs_le] at h1r h2r ⊢
  constructor <;> linarith

#print axioms st_close
#print axioms sin_poly
#print axioms cos_poly
#print axioms piDD_close

end Library.Numerics.Float64.Tgamma.TgammaSinTables
