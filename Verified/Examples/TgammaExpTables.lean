import Verified.Examples.TgammaKernelBase

/-!
Bounds on `as_expd`'s tables and kernel (`tgamma.c`, commit `ff2f71f6`): the split
`1024/ln 2`, the double-double tables `2 ^ (i/32)` and `2 ^ (i/1024)` by Taylor sums of the
exponential at the ends of an enclosure of the argument, and the kernel
`exp (X ln 2/1024) ≈ 1 + X P (X)` on `|X| ≤ 5/8` by a Taylor model.  The interval contains the
kernel arguments that `as_logd`'s unnormalized low part can produce, beyond `513/1024`.
-/

namespace Verified.Examples.TgammaExpTables

open Real LeanExe.ProofKit PolyBound TaylorModel TaylorRemainder TaylorCheck RatExpLog
  GammaThresholds TgammaFactsBase TgammaKernelBase

/-! ### `asExpd` -/

theorem invLn2_checked :
    qabs (invLn2 - 1024 / log2Lo) ≤ 1 / 2 ^ 80 ∧ qabs (invLn2 - 1024 / log2Hi) ≤ 1 / 2 ^ 80 := by
  decide +kernel

theorem invLn2_close : |(invLn2 : ℝ) - 1024 / Real.log 2| ≤ 1 / 2 ^ 80 := by
  obtain ⟨h1, h2⟩ := invLn2_checked
  have h1r : |((invLn2 - 1024 / log2Lo : ℚ) : ℝ)| ≤ ((1 / 2 ^ 80 : ℚ) : ℝ) := by
    rw [← qabs_cast]; exact_mod_cast h1
  have h2r : |((invLn2 - 1024 / log2Hi : ℚ) : ℝ)| ≤ ((1 / 2 ^ 80 : ℚ) : ℝ) := by
    rw [← qabs_cast]; exact_mod_cast h2
  have hl := log_two_lo
  have hh := log_two_hi
  have hlp : (0 : ℝ) < log2Lo := by
    have : (0 : ℚ) < log2Lo := by decide +kernel
    exact_mod_cast this
  have hd1 : 1024 / Real.log 2 ≤ 1024 / (log2Lo : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hlp hl
  have hd2 : 1024 / (log2Hi : ℝ) ≤ 1024 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) hh
  push_cast at h1r h2r
  rw [abs_le] at h1r h2r ⊢
  constructor <;> linarith

theorem e0_checked_0 :
    expCloseOk (e0 (0 : ℕ)) ((0 : ℕ) * log2Lo / 32) ((0 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_1 :
    expCloseOk (e0 (1 : ℕ)) ((1 : ℕ) * log2Lo / 32) ((1 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_2 :
    expCloseOk (e0 (2 : ℕ)) ((2 : ℕ) * log2Lo / 32) ((2 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_3 :
    expCloseOk (e0 (3 : ℕ)) ((3 : ℕ) * log2Lo / 32) ((3 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_4 :
    expCloseOk (e0 (4 : ℕ)) ((4 : ℕ) * log2Lo / 32) ((4 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_5 :
    expCloseOk (e0 (5 : ℕ)) ((5 : ℕ) * log2Lo / 32) ((5 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_6 :
    expCloseOk (e0 (6 : ℕ)) ((6 : ℕ) * log2Lo / 32) ((6 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_7 :
    expCloseOk (e0 (7 : ℕ)) ((7 : ℕ) * log2Lo / 32) ((7 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_8 :
    expCloseOk (e0 (8 : ℕ)) ((8 : ℕ) * log2Lo / 32) ((8 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_9 :
    expCloseOk (e0 (9 : ℕ)) ((9 : ℕ) * log2Lo / 32) ((9 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_10 :
    expCloseOk (e0 (10 : ℕ)) ((10 : ℕ) * log2Lo / 32) ((10 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_11 :
    expCloseOk (e0 (11 : ℕ)) ((11 : ℕ) * log2Lo / 32) ((11 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_12 :
    expCloseOk (e0 (12 : ℕ)) ((12 : ℕ) * log2Lo / 32) ((12 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_13 :
    expCloseOk (e0 (13 : ℕ)) ((13 : ℕ) * log2Lo / 32) ((13 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_14 :
    expCloseOk (e0 (14 : ℕ)) ((14 : ℕ) * log2Lo / 32) ((14 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_15 :
    expCloseOk (e0 (15 : ℕ)) ((15 : ℕ) * log2Lo / 32) ((15 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_16 :
    expCloseOk (e0 (16 : ℕ)) ((16 : ℕ) * log2Lo / 32) ((16 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_17 :
    expCloseOk (e0 (17 : ℕ)) ((17 : ℕ) * log2Lo / 32) ((17 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_18 :
    expCloseOk (e0 (18 : ℕ)) ((18 : ℕ) * log2Lo / 32) ((18 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_19 :
    expCloseOk (e0 (19 : ℕ)) ((19 : ℕ) * log2Lo / 32) ((19 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_20 :
    expCloseOk (e0 (20 : ℕ)) ((20 : ℕ) * log2Lo / 32) ((20 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_21 :
    expCloseOk (e0 (21 : ℕ)) ((21 : ℕ) * log2Lo / 32) ((21 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_22 :
    expCloseOk (e0 (22 : ℕ)) ((22 : ℕ) * log2Lo / 32) ((22 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_23 :
    expCloseOk (e0 (23 : ℕ)) ((23 : ℕ) * log2Lo / 32) ((23 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_24 :
    expCloseOk (e0 (24 : ℕ)) ((24 : ℕ) * log2Lo / 32) ((24 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_25 :
    expCloseOk (e0 (25 : ℕ)) ((25 : ℕ) * log2Lo / 32) ((25 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_26 :
    expCloseOk (e0 (26 : ℕ)) ((26 : ℕ) * log2Lo / 32) ((26 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_27 :
    expCloseOk (e0 (27 : ℕ)) ((27 : ℕ) * log2Lo / 32) ((27 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_28 :
    expCloseOk (e0 (28 : ℕ)) ((28 : ℕ) * log2Lo / 32) ((28 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_29 :
    expCloseOk (e0 (29 : ℕ)) ((29 : ℕ) * log2Lo / 32) ((29 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_30 :
    expCloseOk (e0 (30 : ℕ)) ((30 : ℕ) * log2Lo / 32) ((30 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked_31 :
    expCloseOk (e0 (31 : ℕ)) ((31 : ℕ) * log2Lo / 32) ((31 : ℕ) * log2Hi / 32)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e0_checked :
    ∀ i < 32, expCloseOk (e0 i) (i * log2Lo / 32) (i * log2Hi / 32) (1 / 2 ^ 80) = true := by
  intro i hi
  interval_cases i
  exacts [e0_checked_0, e0_checked_1, e0_checked_2, e0_checked_3, e0_checked_4, e0_checked_5,
    e0_checked_6, e0_checked_7, e0_checked_8, e0_checked_9, e0_checked_10, e0_checked_11,
    e0_checked_12, e0_checked_13, e0_checked_14, e0_checked_15, e0_checked_16, e0_checked_17,
    e0_checked_18, e0_checked_19, e0_checked_20, e0_checked_21, e0_checked_22, e0_checked_23,
    e0_checked_24, e0_checked_25, e0_checked_26, e0_checked_27, e0_checked_28, e0_checked_29,
    e0_checked_30, e0_checked_31]

theorem e1_checked_0 :
    expCloseOk (e1 (0 : ℕ)) ((0 : ℕ) * log2Lo / 1024) ((0 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_1 :
    expCloseOk (e1 (1 : ℕ)) ((1 : ℕ) * log2Lo / 1024) ((1 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_2 :
    expCloseOk (e1 (2 : ℕ)) ((2 : ℕ) * log2Lo / 1024) ((2 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_3 :
    expCloseOk (e1 (3 : ℕ)) ((3 : ℕ) * log2Lo / 1024) ((3 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_4 :
    expCloseOk (e1 (4 : ℕ)) ((4 : ℕ) * log2Lo / 1024) ((4 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_5 :
    expCloseOk (e1 (5 : ℕ)) ((5 : ℕ) * log2Lo / 1024) ((5 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_6 :
    expCloseOk (e1 (6 : ℕ)) ((6 : ℕ) * log2Lo / 1024) ((6 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_7 :
    expCloseOk (e1 (7 : ℕ)) ((7 : ℕ) * log2Lo / 1024) ((7 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_8 :
    expCloseOk (e1 (8 : ℕ)) ((8 : ℕ) * log2Lo / 1024) ((8 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_9 :
    expCloseOk (e1 (9 : ℕ)) ((9 : ℕ) * log2Lo / 1024) ((9 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_10 :
    expCloseOk (e1 (10 : ℕ)) ((10 : ℕ) * log2Lo / 1024) ((10 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_11 :
    expCloseOk (e1 (11 : ℕ)) ((11 : ℕ) * log2Lo / 1024) ((11 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_12 :
    expCloseOk (e1 (12 : ℕ)) ((12 : ℕ) * log2Lo / 1024) ((12 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_13 :
    expCloseOk (e1 (13 : ℕ)) ((13 : ℕ) * log2Lo / 1024) ((13 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_14 :
    expCloseOk (e1 (14 : ℕ)) ((14 : ℕ) * log2Lo / 1024) ((14 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_15 :
    expCloseOk (e1 (15 : ℕ)) ((15 : ℕ) * log2Lo / 1024) ((15 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_16 :
    expCloseOk (e1 (16 : ℕ)) ((16 : ℕ) * log2Lo / 1024) ((16 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_17 :
    expCloseOk (e1 (17 : ℕ)) ((17 : ℕ) * log2Lo / 1024) ((17 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_18 :
    expCloseOk (e1 (18 : ℕ)) ((18 : ℕ) * log2Lo / 1024) ((18 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_19 :
    expCloseOk (e1 (19 : ℕ)) ((19 : ℕ) * log2Lo / 1024) ((19 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_20 :
    expCloseOk (e1 (20 : ℕ)) ((20 : ℕ) * log2Lo / 1024) ((20 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_21 :
    expCloseOk (e1 (21 : ℕ)) ((21 : ℕ) * log2Lo / 1024) ((21 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_22 :
    expCloseOk (e1 (22 : ℕ)) ((22 : ℕ) * log2Lo / 1024) ((22 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_23 :
    expCloseOk (e1 (23 : ℕ)) ((23 : ℕ) * log2Lo / 1024) ((23 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_24 :
    expCloseOk (e1 (24 : ℕ)) ((24 : ℕ) * log2Lo / 1024) ((24 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_25 :
    expCloseOk (e1 (25 : ℕ)) ((25 : ℕ) * log2Lo / 1024) ((25 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_26 :
    expCloseOk (e1 (26 : ℕ)) ((26 : ℕ) * log2Lo / 1024) ((26 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_27 :
    expCloseOk (e1 (27 : ℕ)) ((27 : ℕ) * log2Lo / 1024) ((27 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_28 :
    expCloseOk (e1 (28 : ℕ)) ((28 : ℕ) * log2Lo / 1024) ((28 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_29 :
    expCloseOk (e1 (29 : ℕ)) ((29 : ℕ) * log2Lo / 1024) ((29 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_30 :
    expCloseOk (e1 (30 : ℕ)) ((30 : ℕ) * log2Lo / 1024) ((30 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked_31 :
    expCloseOk (e1 (31 : ℕ)) ((31 : ℕ) * log2Lo / 1024) ((31 : ℕ) * log2Hi / 1024)
      (1 / 2 ^ 80) = true := by
  decide +kernel

theorem e1_checked :
    ∀ i < 32, expCloseOk (e1 i) (i * log2Lo / 1024) (i * log2Hi / 1024) (1 / 2 ^ 80) = true := by
  intro i hi
  interval_cases i
  exacts [e1_checked_0, e1_checked_1, e1_checked_2, e1_checked_3, e1_checked_4, e1_checked_5,
    e1_checked_6, e1_checked_7, e1_checked_8, e1_checked_9, e1_checked_10, e1_checked_11,
    e1_checked_12, e1_checked_13, e1_checked_14, e1_checked_15, e1_checked_16, e1_checked_17,
    e1_checked_18, e1_checked_19, e1_checked_20, e1_checked_21, e1_checked_22, e1_checked_23,
    e1_checked_24, e1_checked_25, e1_checked_26, e1_checked_27, e1_checked_28, e1_checked_29,
    e1_checked_30, e1_checked_31]

theorem e0_close : ∀ i < 32, |(e0 i : ℝ) - Real.exp (i * Real.log 2 / 32)| ≤ 1 / 2 ^ 80 := by
  intro i hi
  have hl := log_two_lo
  have hh := log_two_hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h := expClose (e0_checked i hi) (x := i * Real.log 2 / 32) (by push_cast; nlinarith)
    (by push_cast; nlinarith)
  push_cast at h
  exact h

theorem e1_close : ∀ i < 32, |(e1 i : ℝ) - Real.exp (i * Real.log 2 / 1024)| ≤ 1 / 2 ^ 80 := by
  intro i hi
  have hl := log_two_lo
  have hh := log_two_hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have h := expClose (e1_checked i hi) (x := i * Real.log 2 / 1024) (by push_cast; nlinarith)
    (by push_cast; nlinarith)
  push_cast at h
  exact h

/-- The parameters for `exp (X log 2/1024)` on `|X| ≤ 5/8`. -/
def cfgExp : Cfg := ⟨5 / 8, 12, 100, 40, 1 / 2 ^ 100, GammaPi.piLo128, GammaPi.piHi128⟩

/-- `exp (X log 2/1024) - (1 + X P X)`. -/
def expErrExpr : TaylorModel.Expr :=
  .add (.exp (.mul .var (.mul (.logC 2 log2Lo log2Hi) (.const (1 / 1024)))))
    (.neg (.poly (onePlusX expPolyList)))

theorem expErr_checked : exprOk cfgExp expErrExpr (1 / 2 ^ 74) 0 = true := by
  decide +kernel

theorem exp_poly : ∀ X : ℝ, |X| ≤ 5 / 8 →
    |Real.exp (X * Real.log 2 / 1024) - (1 + X * eval expPolyList X)| ≤ 1 / 2 ^ 74 := by
  intro X hX
  have h := exprOk_sound cfgExp expErrExpr _ _ GammaPi.pi_bounds128 expErr_checked (t := X)
    (by simp only [cfgExp]; push_cast; exact hX)
  simp only [expErrExpr, TaylorModel.Expr.eval, eval_onePlusX] at h
  push_cast at h
  convert h using 2
  ring_nf

#print axioms invLn2_close
#print axioms e0_close
#print axioms e1_close
#print axioms exp_poly

end Verified.Examples.TgammaExpTables
