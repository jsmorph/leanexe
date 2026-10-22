import Library.Numerics.Float64.Lgamma.LgammaReflTail
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
`FastSpec` for the reflection of `Lgamma.lgammaWith` from `x = -6` to `-1/2`, where the positive
leaf at `a = -x` is a piece of `LgammaFastPiece` with `eps = |fh| · 8.7 · 10^-20 + 10^-24` and the
margin `|fh|/2^65` (`piece_iface`).  `refl_abs` gives the absolute form of `FastSpec` when
`ln Γ a ≥ λ ≥ 1/8` and the sine's error `1.14 · 2^-71/σ`, for a lower bound `σ` on `s` away from
the integers, fits in that margin.  `refl_rel` gives the relative form when `|ln |Γ x||` is at
least `M/128 + 1/256` for a bound `M` on `|fh|`.  From -6 to -4 the absolute form holds with
`λ = 1.7` and `σ = 0.0117` (`refl_six`).  From -2 to -1/2 the relative form holds, since
`|ln |Γ x|| ≥ 0.3` there by the convexity of `ln Γ` (`refl_two`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaReflMid
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaWords LgammaFastSmall
  LgammaPiecePoly TgammaFloor LgammaWalk LgammaReflCore LgammaReflTail

set_option exponentiation.threshold 4096

/-- A piece's double-double and the code's `eps` in the form of `refl_abs` and `refl_rel`. -/
theorem piece_iface (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hPF : LgammaApprox.PieceFact) (ax : Float)
    (hax : Finite ax.toBits) (k : ℕ) (hk : k < 19) (jj : UInt64) (hjj : jj.toNat = k)
    (hb0 : (LgammaApprox.border k : ℝ) ≤ value ax.toBits)
    (hb1 : value ax.toBits ≤ (LgammaApprox.border (k + 1) : ℝ))
    (hv1 : value ax.toBits ≠ 1) (hv2 : value ax.toBits ≠ 2) (P Q R : Float × Float)
    (hP : P = Lgamma.piecePoly Lgamma.mainTable jj (ax - entry Lgamma.mainTable (20 + jj)))
    (hQ : Q = if jj == 4 then mulDDD (1.0 - ax) P.1 P.2 else (P.1, P.2))
    (hR : R = if jj == 10 then mulDDD (ax - 2.0) Q.1 Q.2 else (Q.1, Q.2)) :
    Finite R.1.toBits ∧ Finite R.2.toBits ∧
      Finite (R.1.abs * Float.ofBits 0x3BF9AD88BDABDB20 + Float.ofBits 0x3AF357C299A88EA7).toBits ∧
      |value R.1.toBits| ≤ 16 ∧ |value R.2.toBits| ≤ 1 / 2 ^ 38 ∧
      |value R.1.toBits| * (869 / 10 ^ 22) + 98 / 10 ^ 26 ≤
        value (R.1.abs * Float.ofBits 0x3BF9AD88BDABDB20 + Float.ofBits 0x3AF357C299A88EA7).toBits ∧
      value (R.1.abs * Float.ofBits 0x3BF9AD88BDABDB20 + Float.ofBits 0x3AF357C299A88EA7).toBits ≤
        |value R.1.toBits| / 2 ^ 63 + 1 / 2 ^ 78 ∧
      |GammaBasic.lgamma (value ax.toBits) - (value R.1.toBits + value R.2.toBits)| +
          |value R.1.toBits| / 2 ^ 65 ≤
        2 * value (R.1.abs * Float.ofBits 0x3BF9AD88BDABDB20 +
          Float.ofBits 0x3AF357C299A88EA7).toBits := by
  obtain ⟨hr1, hr2, hr2b, hr1b, hmain⟩ :=
    LgammaFastPiece.piece_leaf hF hPF ax hax k hk jj hjj hb0 hb1 hv1 hv2 P Q R hP hQ hR
  obtain ⟨hef, hev⟩ := LgammaFastPiece.eps_value R.1 hr1 hr1b
  have hc1 := qcast_le LgammaFastPiece.c1_bounds.1
  have hc1' := qcast_le LgammaFastPiece.c1_bounds.2
  have hc2 := qcast_le LgammaFastPiece.c2_bounds.1
  have hc2' := qcast_le LgammaFastPiece.c2_bounds.2
  push_cast at hc1 hc1' hc2 hc2'
  have hp1 : |value R.1.toBits| * (869 / 10 ^ 22) ≤
      |value R.1.toBits| * ((PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
  have hp2 : |value R.1.toBits| * ((PolyBound.ratOfWord 0x3BF9AD88BDABDB20 : ℚ) : ℝ) ≤
      |value R.1.toBits| * (1 / 2 ^ 63) :=
    mul_le_mul_of_nonneg_left hc1' (abs_nonneg _)
  have hev' := abs_le.mp hev
  refine ⟨hr1, hr2, hef, hr1b, hr2b, ?_, ?_, ?_⟩
  · linarith [(by norm_num : (98 : ℝ) / 10 ^ 26 + 1 / 2 ^ 105 ≤ 99 / 10 ^ 26)]
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 79 + 1 / 2 ^ 105 ≤ 1 / 2 ^ 78)]
  · linarith [(by norm_num : (2 : ℝ) * (1 / 2 ^ 105) ≤ 1 / 2 ^ 100)]

/-- `s ≥ φ'/2` for `φ' = 1/2 - |φ - 1/2|`, from Jordan's inequality and `π < 4`. -/
theorem s_jordan (φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ ≤ 1) :
    (1 / 2 - |φ - 1 / 2|) / 2 ≤ Real.sin (Real.pi * φ) / Real.pi := by
  have hz0 : 0 ≤ 1 / 2 - |φ - 1 / 2| := by
    rw [sub_nonneg, abs_le]; constructor <;> linarith
  have hsin := Real.mul_le_sin (x := Real.pi * (1 / 2 - |φ - 1 / 2|))
    (mul_nonneg Real.pi_pos.le hz0) (by
      have : 1 / 2 - |φ - 1 / 2| ≤ 1 / 2 := by linarith [abs_nonneg (φ - 1 / 2)]
      have := mul_le_mul_of_nonneg_left this Real.pi_pos.le
      linarith)
  rw [← mul_assoc, div_mul_cancel₀ 2 Real.pi_ne_zero, ← LgammaSinpi.sin_eq_near] at hsin
  rw [le_div_iff₀ Real.pi_pos]
  have := Real.pi_lt_four
  nlinarith

/-- `sin (π φ) ≥ π p - (π p)³/6` for `0 < p ≤ φ' = 1/2 - |φ - 1/2|`. -/
theorem s_cube (φ p : ℝ) (hp : 0 < p) (hpz : p ≤ 1 / 2 - |φ - 1 / 2|) :
    Real.pi * p - (Real.pi * p) ^ 3 / 6 ≤ Real.sin (Real.pi * φ) := by
  rw [LgammaSinpi.sin_eq_near φ]
  have hpi := Real.pi_pos
  have h1 := Real.sin_gt_sub_cube (x := Real.pi * p) (by positivity)
  have hz : 1 / 2 - |φ - 1 / 2| ≤ 1 / 2 := by linarith [abs_nonneg (φ - 1 / 2)]
  have h2 : Real.sin (Real.pi * p) ≤ Real.sin (Real.pi * (1 / 2 - |φ - 1 / 2|)) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · have : 0 < Real.pi * p := by positivity
      linarith
    · have := mul_le_mul_of_nonneg_left hz hpi.le
      linarith
    · exact mul_le_mul_of_nonneg_left hpz hpi.le
  linarith

/-- The sine's error `ρ` of `refl_core` against a lower bound `σ ≤ 1` on `s` away from the
integers. -/
theorem rho_le (φ σ ρ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hσ : 3 / 256 ≤ 1 / 2 - |φ - 1 / 2| → σ ≤ Real.sin (Real.pi * φ) / Real.pi)
    (hρ : ρ = 1 / 2 ^ 72 ∨ (3 / 256 ≤ 1 / 2 - |φ - 1 / 2| ∧
      ρ = 114 / 100 / 2 ^ 71 / (Real.sin (Real.pi * φ) / Real.pi))) :
    ρ ≤ 114 / 100 / 2 ^ 71 / σ := by
  rcases hρ with h | ⟨hf, h⟩
  · rw [h, le_div_iff₀ hσ0]
    have : 1 / 2 ^ 72 * σ ≤ 1 / 2 ^ 72 * 1 := mul_le_mul_of_nonneg_left hσ1 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 72 * 1 ≤ 114 / 100 / 2 ^ 71)]
  · rw [h]
    exact div_le_div_of_nonneg_left (by norm_num) hσ0 (hσ hf)

set_option maxHeartbeats 2000000 in
/-- **The absolute form** of `FastSpec` for the reflection from -6 to -1/2, when `ln Γ (-x) ≥ λ`
and the sine's error against `s ≥ σ` fits in the piece's margin `|fh|/2^65`. -/
theorem refl_abs (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (x : Float) (hx : Finite x.toBits)
    (h6 : -6 < value x.toBits) (h2 : value x.toBits ≤ -1 / 2)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (fh fl eps : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (he : Finite eps.toBits) (hfhb : |value fh.toBits| ≤ 16)
    (hflb : |value fl.toBits| ≤ 1 / 2 ^ 38)
    (helo : |value fh.toBits| * (869 / 10 ^ 22) + 98 / 10 ^ 26 ≤ value eps.toBits)
    (hehi : value eps.toBits ≤ |value fh.toBits| / 2 ^ 63 + 1 / 2 ^ 78)
    (hpos : |GammaBasic.lgamma (-value x.toBits) - (value fh.toBits + value fl.toBits)| +
      |value fh.toBits| / 2 ^ 65 ≤ 2 * value eps.toBits)
    (lam σ : ℝ) (hlam : lam ≤ GammaBasic.lgamma (-value x.toBits)) (hlam0 : 1 / 8 ≤ lam)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hσ : 3 / 256 ≤ 1 / 2 - |Int.fract (value x.toBits) - 1 / 2| →
      σ ≤ Real.sin (Real.pi * Int.fract (value x.toBits)) / Real.pi)
    (hbud : 114 / 100 / 2 ^ 71 / σ + 24 / 10 ^ 22 ≤ lam * (27 / 10 ^ 21))
    (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD fh fl C.1 (C.2 + B.2 / B.1)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  obtain ⟨hC1, hD1, hD2, hlh, hD1b, -, hD2b, ρ, hρ, hcore⟩ := refl_core hF hL hS x hx
    (by linarith) h2 hint fh fl hfh hfl (by linarith [(by norm_num : (16 : ℝ) ≤ 2 ^ 897)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 38 ≤ 2 ^ 700)]) A B C D hA hB hC hD
  have hρσ := rho_le _ σ ρ hσ0 hσ1 hσ hρ
  have he0 : 0 ≤ value eps.toBits := by
    have := mul_nonneg (abs_nonneg (value fh.toBits)) (by norm_num : (0 : ℝ) ≤ 869 / 10 ^ 22)
    linarith
  obtain ⟨he'f, he'v⟩ := eps8_value eps C.1 he hC1
    (by rw [abs_of_nonneg he0]; linarith [(by norm_num : (16 : ℝ) / 2 ^ 63 + 1 / 2 ^ 78 ≤ 2 ^ 900)])
    hlh
  rw [abs_of_nonneg he0] at he'v
  have hLr := refl_L (value x.toBits) (by linarith) hint
  set v := value x.toBits with hvdef
  set φ := Int.fract v with hφdef
  set s := Real.sin (Real.pi * φ) / Real.pi with hsdef
  set a := -v with hadef
  set lg := GammaBasic.lgamma a with hlgdef
  set F := value fh.toBits with hFdef
  set c8 := ((PolyBound.ratOfWord 0x3B8E392010175EE6 : ℚ) : ℝ) with hc8def
  have hc8 := qcast_le c8_bounds.1
  have hc8' := qcast_le c8_bounds.2
  push_cast at hc8 hc8'
  rw [← hc8def] at hc8 hc8'
  set e' := eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6 with he'def
  have hlhc : 0 ≤ |value C.1.toBits| * c8 := mul_nonneg (abs_nonneg _) (by linarith)
  have hlhc' : |value C.1.toBits| * c8 ≤ 43 * (801 / 10 ^ 24) :=
    mul_le_mul hlh hc8' (by linarith) (by norm_num)
  have he'lo : value eps.toBits - (value eps.toBits + 1 / 2 ^ 60) / 2 ^ 52 ≤ value e'.toBits := by
    have := abs_le.mp he'v; linarith
  have he'hi : value e'.toBits ≤ value eps.toBits + 43 * (801 / 10 ^ 24) +
      (value eps.toBits + 1 / 2 ^ 60) / 2 ^ 52 := by
    have := abs_le.mp he'v; linarith
  obtain ⟨hn1f, hn1v⟩ := LgammaFastTiny.neg_float D.1 hD1
  obtain ⟨hn2f, hn2v⟩ := LgammaFastTiny.neg_float D.2 hD2
  have hFlam : lam - 1 / 2 ^ 37 ≤ |F| := by
    have h1 : lg - (F + value fl.toBits) ≤ 2 * value eps.toBits := by
      have := le_abs_self (lg - (F + value fl.toBits))
      have : 0 ≤ |F| / 2 ^ 65 := by positivity
      linarith
    have h3 : |F| / 2 ^ 62 ≤ 16 / 2 ^ 62 := div_le_div_of_nonneg_right hfhb (by norm_num)
    have h4 := le_abs_self F
    have h5 := le_abs_self (value fl.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 38 + 2 / 2 ^ 78 + 16 / 2 ^ 62 ≤ 1 / 2 ^ 37)]
  have hD1b' : |value D.1.toBits| ≤ 60 := by
    linarith [(by norm_num : ((16 : ℝ) + 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 60)]
  have hsum : (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 +
      1 / 2 ^ 1074) / 2 ^ 53 ≤ 318 / 10 ^ 24 := by
    have h1 : (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 +
        1 / 2 ^ 1074) / 2 ^ 53 ≤ (3 * (1 / 2 ^ 38 + 1 / 2 ^ 20) + 60 / 2 ^ 52 + 1 / 2 ^ 1074) /
          2 ^ 53 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have : |value D.1.toBits| / 2 ^ 52 ≤ 60 / 2 ^ 52 :=
        div_le_div_of_nonneg_right hD1b' (by norm_num)
      linarith
    exact h1.trans (by norm_num)
  have hd2 : |value D.2.toBits| ≤ 1 / 2 ^ 19 := by
    have h1 : |value D.1.toBits| / 2 ^ 51 ≤ 60 / 2 ^ 51 :=
      div_le_div_of_nonneg_right hD1b' (by norm_num)
    have h2 : (|value fl.toBits| + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) ≤
        (1 / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : ((1 : ℝ) / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) + 60 / 2 ^ 51 +
      1 / 2 ^ 1073 ≤ 1 / 2 ^ 19)]
  have hLL : Real.log (Real.Gamma v) = -(lg + Real.log (a * s)) := hLr
  have hcore' : |-(lg + Real.log (a * s)) - (-value D.1.toBits + -value D.2.toBits)| ≤
      |lg - (F + value fl.toBits)| + ρ + 2 / 10 ^ 21 +
        (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) /
          2 ^ 53 := by
    rw [show -(lg + Real.log (a * s)) - (-value D.1.toBits + -value D.2.toBits) =
      -(lg + Real.log (a * s) - (value D.1.toBits + value D.2.toBits)) by ring, abs_neg]
    exact hcore
  have heps : (1 / 8 - 1 / 2 ^ 37) * (869 / 10 ^ 22) ≤ value eps.toBits := by
    have := mul_le_mul_of_nonneg_right hFlam (by norm_num : (0 : ℝ) ≤ 869 / 10 ^ 22)
    have : (1 / 8 - 1 / 2 ^ 37) * (869 / 10 ^ 22) ≤ (lam - 1 / 2 ^ 37) * (869 / 10 ^ 22) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have hepsu : value eps.toBits ≤ 16 / 2 ^ 63 + 1 / 2 ^ 78 := by
    have : |F| / 2 ^ 63 ≤ 16 / 2 ^ 63 := div_le_div_of_nonneg_right hfhb (by norm_num)
    linarith
  unfold FastSpec
  dsimp only
  rw [hn1v, hn2v, hLL]
  simp only [abs_neg]
  refine ⟨hn1f, hn2f, he'f, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤
      (1 / 8 - 1 / 2 ^ 37) * (869 / 10 ^ 22) / 2 - 1 / 2 ^ 112)]
  · have h1 : (1 : ℝ) / 2 ^ 19 ≤
        2 ^ 48 * ((1 / 8 - 1 / 2 ^ 37) * (869 / 10 ^ 22) * (1 - 1 / 2 ^ 50) - 1 / 2 ^ 112) := by
      norm_num
    linarith
  · linarith [(by norm_num : (60 : ℝ) + 2 ^ 49 * (16 / 2 ^ 63 + 1 / 2 ^ 78 + 43 * (801 / 10 ^ 24) +
      (16 / 2 ^ 63 + 1 / 2 ^ 78 + 1 / 2 ^ 60) / 2 ^ 52) ≤ 2 ^ 1020)]
  · have hlam65 : lam * (27 / 10 ^ 21 + 1 / 10 ^ 23) ≤ lam / 2 ^ 65 := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
    have hF65 : (lam - 1 / 2 ^ 37) / 2 ^ 65 ≤ |F| / 2 ^ 65 :=
      div_le_div_of_nonneg_right hFlam (by norm_num)
    have hr : (value eps.toBits + 1 / 2 ^ 60) / 2 ^ 52 ≤
        (16 / 2 ^ 63 + 1 / 2 ^ 78 + 1 / 2 ^ 60) / 2 ^ 52 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 8 * (1 / 10 ^ 23) ≥ 1 / 2 ^ 37 / 2 ^ 65 +
      2 * ((16 / 2 ^ 63 + 1 / 2 ^ 78 + 1 / 2 ^ 60) / 2 ^ 52)),
      (by norm_num : (24 : ℝ) / 10 ^ 22 ≥ 2 / 10 ^ 21 + 318 / 10 ^ 24)]

set_option maxHeartbeats 2000000 in
/-- **The relative form** of `FastSpec` for the reflection from -6 to -1/2, when
`|ln |Γ x|| ≥ M/128 + 1/256` for a bound `M` on `|fh|`. -/
theorem refl_rel (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (x : Float) (hx : Finite x.toBits)
    (h6 : -6 < value x.toBits) (h2 : value x.toBits ≤ -1 / 2)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (fh fl eps : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (he : Finite eps.toBits) (M : ℝ) (hfhb : |value fh.toBits| ≤ M)
    (hM : M ≤ 16) (hflb : |value fl.toBits| ≤ 1 / 2 ^ 38)
    (helo : |value fh.toBits| * (869 / 10 ^ 22) + 98 / 10 ^ 26 ≤ value eps.toBits)
    (hehi : value eps.toBits ≤ |value fh.toBits| / 2 ^ 63 + 1 / 2 ^ 78)
    (hpos : |GammaBasic.lgamma (-value x.toBits) - (value fh.toBits + value fl.toBits)| +
      |value fh.toBits| / 2 ^ 65 ≤ 2 * value eps.toBits)
    (hLb : M / 128 + 1 / 256 ≤ |Real.log (Real.Gamma (value x.toBits))|)
    (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD fh fl C.1 (C.2 + B.2 / B.1)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  obtain ⟨hC1, hD1, hD2, hlh, hD1b, hlhL, hD2b, ρ, hρ, hcore⟩ := refl_core hF hL hS x hx
    (by linarith) h2 hint fh fl hfh hfl (by linarith [(by norm_num : (16 : ℝ) ≤ 2 ^ 897)])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 38 ≤ 2 ^ 700)]) A B C D hA hB hC hD
  have hφ0 := Int.fract_nonneg (value x.toBits)
  have hφ1 := (Int.fract_lt_one (value x.toBits)).le
  have hρσ := rho_le _ (3 / 512) ρ (by norm_num) (by norm_num)
    (fun hf => by have := s_jordan _ hφ0 hφ1; linarith) hρ
  have he0 : 0 ≤ value eps.toBits := by
    have := mul_nonneg (abs_nonneg (value fh.toBits)) (by norm_num : (0 : ℝ) ≤ 869 / 10 ^ 22)
    linarith
  obtain ⟨he'f, he'v⟩ := eps8_value eps C.1 he hC1
    (by rw [abs_of_nonneg he0]; linarith [(by norm_num : (16 : ℝ) / 2 ^ 63 + 1 / 2 ^ 78 ≤ 2 ^ 900)])
    hlh
  rw [abs_of_nonneg he0] at he'v
  have hLr := refl_L (value x.toBits) (by linarith) hint
  rw [hLr, abs_neg] at hLb
  set v := value x.toBits with hvdef
  set φ := Int.fract v with hφdef
  set s := Real.sin (Real.pi * φ) / Real.pi with hsdef
  set a := -v with hadef
  set lg := GammaBasic.lgamma a with hlgdef
  set F := value fh.toBits with hFdef
  set c8 := ((PolyBound.ratOfWord 0x3B8E392010175EE6 : ℚ) : ℝ) with hc8def
  have hc8 := qcast_le c8_bounds.1
  have hc8' := qcast_le c8_bounds.2
  push_cast at hc8 hc8'
  rw [← hc8def] at hc8 hc8'
  set e' := eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6 with he'def
  have hlhc : 0 ≤ |value C.1.toBits| * c8 := mul_nonneg (abs_nonneg _) (by linarith)
  have hlhc' : |value C.1.toBits| * c8 ≤ 43 * (801 / 10 ^ 24) :=
    mul_le_mul hlh hc8' (by linarith) (by norm_num)
  have he'lo : value eps.toBits - (value eps.toBits + 1 / 2 ^ 60) / 2 ^ 52 ≤ value e'.toBits := by
    have := abs_le.mp he'v; linarith
  have he'hi : value e'.toBits ≤ value eps.toBits + 43 * (801 / 10 ^ 24) +
      (value eps.toBits + 1 / 2 ^ 60) / 2 ^ 52 := by
    have := abs_le.mp he'v; linarith
  obtain ⟨hn1f, hn1v⟩ := LgammaFastTiny.neg_float D.1 hD1
  obtain ⟨hn2f, hn2v⟩ := LgammaFastTiny.neg_float D.2 hD2
  have hD1b' : |value D.1.toBits| ≤ 60 := by
    linarith [(by norm_num : ((16 : ℝ) + 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 60)]
  have hsum : (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 +
      1 / 2 ^ 1074) / 2 ^ 53 ≤ 318 / 10 ^ 24 := by
    have h1 : (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 +
        1 / 2 ^ 1074) / 2 ^ 53 ≤ (3 * (1 / 2 ^ 38 + 1 / 2 ^ 20) + 60 / 2 ^ 52 + 1 / 2 ^ 1074) /
          2 ^ 53 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have : |value D.1.toBits| / 2 ^ 52 ≤ 60 / 2 ^ 52 :=
        div_le_div_of_nonneg_right hD1b' (by norm_num)
      linarith
    exact h1.trans (by norm_num)
  have hd2 : |value D.2.toBits| ≤ 1 / 2 ^ 19 := by
    have h1 : |value D.1.toBits| / 2 ^ 51 ≤ 60 / 2 ^ 51 :=
      div_le_div_of_nonneg_right hD1b' (by norm_num)
    have h2 : (|value fl.toBits| + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) ≤
        (1 / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : ((1 : ℝ) / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) + 60 / 2 ^ 51 +
      1 / 2 ^ 1073 ≤ 1 / 2 ^ 19)]
  have hLL : Real.log (Real.Gamma v) = -(lg + Real.log (a * s)) := hLr
  have hcore' : |-(lg + Real.log (a * s)) - (-value D.1.toBits + -value D.2.toBits)| ≤
      |lg - (F + value fl.toBits)| + ρ + 2 / 10 ^ 21 +
        (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) /
          2 ^ 53 := by
    rw [show -(lg + Real.log (a * s)) - (-value D.1.toBits + -value D.2.toBits) =
      -(lg + Real.log (a * s) - (value D.1.toBits + value D.2.toBits)) by ring, abs_neg]
    exact hcore
  have hepsu : value eps.toBits ≤ M / 2 ^ 63 + 1 / 2 ^ 78 := by
    have : |F| / 2 ^ 63 ≤ M / 2 ^ 63 := div_le_div_of_nonneg_right hfhb (by norm_num)
    linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hfhb
  -- `|ln |Γ x|| ≤ 61`
  have hLu : |lg + Real.log (a * s)| ≤ 61 := by
    have h1 : |lg| ≤ |F| + |value fl.toBits| + 2 * value eps.toBits := by
      have := abs_sub_abs_le_abs_sub lg (F + value fl.toBits)
      have := abs_add_le F (value fl.toBits)
      have : 0 ≤ |F| / 2 ^ 65 := by positivity
      linarith
    have h2 : |Real.log (a * s)| ≤ 44 := by
      have := abs_sub_abs_le_abs_sub (Real.log (a * s)) (value C.1.toBits)
      rw [abs_sub_comm] at hlhL
      linarith [(by norm_num : (43 : ℝ) + 1 / 2 ^ 19 ≤ 44)]
    have := abs_add_le lg (Real.log (a * s))
    linarith [(by norm_num : (16 : ℝ) + 1 / 2 ^ 38 + 2 * (16 / 2 ^ 63 + 1 / 2 ^ 78) + 44 ≤ 61)]
  unfold FastSpec
  dsimp only
  rw [hn1v, hn2v, hLL]
  simp only [abs_neg]
  refine ⟨hn1f, hn2f, he'f, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · have := mul_nonneg (abs_nonneg F) (by norm_num : (0 : ℝ) ≤ 869 / 10 ^ 22)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 98 / 10 ^ 26 / 2 - 1 / 2 ^ 112)]
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 2 ^ 1000)]
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 256)]
  · linarith [(by norm_num : (61 : ℝ) ≤ 2 ^ 1020)]
  · have h1 : |lg - (F + value fl.toBits)| ≤ 2 * value eps.toBits := by
      have : 0 ≤ |F| / 2 ^ 65 := by positivity
      linarith
    have hr : (value eps.toBits + 1 / 2 ^ 60) / 2 ^ 52 ≤
        (16 / 2 ^ 63 + 1 / 2 ^ 78 + 1 / 2 ^ 60) / 2 ^ 52 :=
      div_le_div_of_nonneg_right (by
        have : M / 2 ^ 63 ≤ 16 / 2 ^ 63 := div_le_div_of_nonneg_right hM (by norm_num)
        linarith) (by norm_num)
    have hd2e : (|value D.2.toBits| + value e'.toBits) / 2 ^ 52 ≤
        (1 / 2 ^ 19 + (16 / 2 ^ 63 + 1 / 2 ^ 78 + 43 * (801 / 10 ^ 24) +
          (16 / 2 ^ 63 + 1 / 2 ^ 78 + 1 / 2 ^ 60) / 2 ^ 52)) / 2 ^ 52 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have : M / 2 ^ 63 ≤ 16 / 2 ^ 63 := div_le_div_of_nonneg_right hM (by norm_num)
      linarith
    have hL54 : (M / 128 + 1 / 256) / 2 ^ 54 ≤ |lg + Real.log (a * s)| / 2 ^ 54 :=
      div_le_div_of_nonneg_right hLb (by norm_num)
    have hρ' : 114 / 100 / 2 ^ 71 / (3 / 512 : ℝ) ≤ 825 / 10 ^ 22 := by norm_num
    linarith [(by norm_num : (4 : ℝ) / 2 ^ 78 + 2 * (43 * (801 / 10 ^ 24)) + 825 / 10 ^ 22 +
      2 / 10 ^ 21 + 318 / 10 ^ 24 + 3 * ((16 / 2 ^ 63 + 1 / 2 ^ 78 + 1 / 2 ^ 60) / 2 ^ 52) +
      (1 / 2 ^ 19 + (16 / 2 ^ 63 + 1 / 2 ^ 78 + 43 * (801 / 10 ^ 24) +
        (16 / 2 ^ 63 + 1 / 2 ^ 78 + 1 / 2 ^ 60) / 2 ^ 52)) / 2 ^ 52 ≤ 1 / 256 / 2 ^ 54),
      (by norm_num : (1 : ℝ) / 128 / 2 ^ 54 = 4 / 2 ^ 63)]

/-- `ln 6 ≥ 1.7`. -/
theorem lgamma_four : (17 / 10 : ℝ) ≤ GammaBasic.lgamma 4 := by
  have h6 : GammaBasic.lgamma 4 = Real.log 6 := by
    rw [GammaBasic.lgamma, show (4 : ℝ) = (3 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [h6, show (6 : ℝ) = 4 * (3 / 2) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h1 := log_bounds.1
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  norm_num at h2
  linarith

/-- **The reflection from -6 to -4**: the absolute form of `FastSpec` with `λ = 1.7`, from
`ln Γ a ≥ ln 6`, and `σ = 0.0117`, from `sin y ≥ y - y³/6`. -/
theorem refl_six (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (x : Float) (hx : Finite x.toBits)
    (h6 : -6 < value x.toBits) (h4 : value x.toBits < -4)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (fh fl eps : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (he : Finite eps.toBits) (hfhb : |value fh.toBits| ≤ 16)
    (hflb : |value fl.toBits| ≤ 1 / 2 ^ 38)
    (helo : |value fh.toBits| * (869 / 10 ^ 22) + 98 / 10 ^ 26 ≤ value eps.toBits)
    (hehi : value eps.toBits ≤ |value fh.toBits| / 2 ^ 63 + 1 / 2 ^ 78)
    (hpos : |GammaBasic.lgamma (-value x.toBits) - (value fh.toBits + value fl.toBits)| +
      |value fh.toBits| / 2 ^ 65 ≤ 2 * value eps.toBits)
    (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD fh fl C.1 (C.2 + B.2 / B.1)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  refine refl_abs hF hL hS x hx h6 (by linarith) hint fh fl eps hfh hfl he hfhb hflb helo hehi hpos
    (17 / 10) (117 / 10 ^ 4) ?_ (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num)
    A B C D hA hB hC hD sign
  · exact lgamma_four.trans (GammaThresholds.lgamma_mono (by norm_num) (by linarith))
  · intro hf
    rw [le_div_iff₀ Real.pi_pos]
    have hc := s_cube (Int.fract (value x.toBits)) (3 / 256) (by norm_num) hf
    have hpi := Real.pi_pos
    have hpi' := Real.pi_lt_d2
    have hpi2 : Real.pi ^ 2 ≤ 99225 / 10 ^ 4 := by nlinarith
    have hcube : (Real.pi * (3 / 256)) ^ 3 / 6 ≤ Real.pi * (3 / 256 - 117 / 10 ^ 4) := by
      rw [show (Real.pi * (3 / 256)) ^ 3 / 6 = Real.pi * (Real.pi ^ 2 * ((3 / 256) ^ 3 / 6)) by
        ring]
      apply mul_le_mul_of_nonneg_left _ hpi.le
      nlinarith
    linarith

/-- `1 < ln π`. -/
theorem one_lt_log_pi : 1 < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have := Real.exp_one_lt_d9
  have := Real.pi_gt_three
  linarith

/-- `ln Γ a ≤ (ln π)/2` from 1/2 to 1 and `ln Γ a ≤ 0` from 1 to 2, by the convexity of `ln Γ`. -/
theorem lgamma_le_half (a : ℝ) (h0 : 1 / 2 ≤ a) (h1 : a ≤ 1) :
    GammaBasic.lgamma a ≤ Real.log Real.pi / 2 := by
  have hm := Real.convexOn_log_Gamma.le_on_segment (x := 1 / 2) (y := 1) (z := a)
    (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr (by norm_num))
    (by rw [segment_eq_Icc (by norm_num)]; exact ⟨h0, h1⟩)
  simp only [Function.comp] at hm
  rw [Real.Gamma_one_half_eq, Real.Gamma_one, Real.log_one, Real.log_sqrt Real.pi_pos.le] at hm
  have : 0 ≤ Real.log Real.pi / 2 := by linarith [one_lt_log_pi]
  exact hm.trans (max_le le_rfl this)

theorem lgamma_le_zero (a : ℝ) (h1 : 1 ≤ a) (h2 : a ≤ 2) : GammaBasic.lgamma a ≤ 0 := by
  have hm := Real.convexOn_log_Gamma.le_on_segment (x := 1) (y := 2) (z := a)
    (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr (by norm_num))
    (by rw [segment_eq_Icc (by norm_num)]; exact ⟨h1, h2⟩)
  simp only [Function.comp] at hm
  rw [Real.Gamma_one, Real.Gamma_two, Real.log_one, max_self] at hm
  exact hm

/-- **The reflection from -2 to -1/2**: the relative form of `FastSpec`, from
`ln |Γ x| = -(ln Γ a + ln (a s)) ≥ 0.3`. -/
theorem refl_two (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (x : Float) (hx : Finite x.toBits)
    (h2' : -2 < value x.toBits) (h2 : value x.toBits ≤ -1 / 2)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (fh fl eps : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (he : Finite eps.toBits) (hfhb : |value fh.toBits| ≤ 16)
    (hflb : |value fl.toBits| ≤ 1 / 2 ^ 38)
    (helo : |value fh.toBits| * (869 / 10 ^ 22) + 98 / 10 ^ 26 ≤ value eps.toBits)
    (hehi : value eps.toBits ≤ |value fh.toBits| / 2 ^ 63 + 1 / 2 ^ 78)
    (hpos : |GammaBasic.lgamma (-value x.toBits) - (value fh.toBits + value fl.toBits)| +
      |value fh.toBits| / 2 ^ 65 ≤ 2 * value eps.toBits)
    (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD fh fl C.1 (C.2 + B.2 / B.1)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  refine refl_rel hF hL hS x hx (by linarith) h2 hint fh fl eps hfh hfl he 16 hfhb le_rfl hflb helo
    hehi hpos ?_ A B C D hA hB hC hD sign
  rw [refl_L (value x.toBits) (by linarith) hint]
  set v := value x.toBits with hvdef
  have hsin := GammaBasic.sin_pi_fract_pos hint
  have hs0 : 0 < Real.sin (Real.pi * Int.fract v) / Real.pi := div_pos hsin Real.pi_pos
  have hs1 : Real.sin (Real.pi * Int.fract v) / Real.pi ≤ 1 / Real.pi :=
    div_le_div_of_nonneg_right (Real.sin_le_one _) Real.pi_pos.le
  have hlp := one_lt_log_pi
  have hm1 : v ≠ -1 := by have := hint (-1); push_cast at this; exact this
  have hl2 : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  rcases lt_or_gt_of_ne hm1 with h | h
  · -- `a` from 1 to 2
    have hlg := lgamma_le_zero (-v) (by linarith) (by linarith)
    have has : -v * (Real.sin (Real.pi * Int.fract v) / Real.pi) ≤ 2 / Real.pi := by
      have := mul_le_mul (show -v ≤ 2 by linarith) hs1 hs0.le (by norm_num)
      rw [mul_one_div] at this
      exact this
    have hlog := Real.log_le_log (mul_pos (by linarith) hs0) has
    rw [Real.log_div (by norm_num) Real.pi_pos.ne'] at hlog
    rw [abs_of_pos (by linarith)]
    linarith
  · -- `a` from 1/2 to 1
    have hlg := lgamma_le_half (-v) (by linarith) (by linarith)
    have has : -v * (Real.sin (Real.pi * Int.fract v) / Real.pi) ≤ 1 / Real.pi := by
      have := mul_le_mul (show -v ≤ 1 by linarith) hs1 hs0.le (by norm_num)
      rw [one_mul] at this
      exact this
    have hlog := Real.log_le_log (mul_pos (by linarith) hs0) has
    rw [one_div, Real.log_inv] at hlog
    rw [abs_of_pos (by linarith)]
    linarith

#print axioms piece_iface
#print axioms refl_abs
#print axioms refl_rel
#print axioms refl_six
#print axioms refl_two

end Library.Numerics.Float64.Lgamma.LgammaReflMid
