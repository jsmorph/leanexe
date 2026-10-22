import Library.Numerics.Float64.Erfc.ErfcTrack4
import Library.Numerics.Float64.Erfc.ErfcExpBits
import LeanExe.ProofKit.F64DivBounds
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
`1/x` and `1/x²` as double-doubles in `erfc_asympt_fast` and `erfc_asympt_accurate`.  The code
takes `yh = 1/x` rounded and `yl = yh (1 - x yh)` with the residual by one `fma`, a step of
Newton's iteration, so that `yh + yl - 1/x = -(1 - x yh)²/x` up to two roundings (`recip_pr`).
Then `uh + ul = yh² + 2 yh yl` from `Erfc.aMul` and one `fma`, within about `10 u²/x²` of `1/x²`
(`usq_pr`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcRecip

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft ErfcEft2 ErfcOps ErfcTrack ErfcRound ErfcExpBits Library.Numerics.Arithmetic.Fma.FmaSpec PolyBound

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

theorem one_two_vals : ff (1.0 : Float) ∧ fv (1.0 : Float) = 1 ∧ ff (2.0 : Float) ∧
    fv (2.0 : Float) = 2 ∧ Wasm.IEEE64.scaledMagnitude (2.0 : Float).toBits = 2 ^ 1075 := by
  obtain ⟨a, b⟩ := one_val
  have h2 : (2.0 : Float).toBits = 0x4000000000000000 := rfl
  have f2 : Finite (0x4000000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  refine ⟨a, b, ?_, ?_, ?_⟩
  · unfold ff; rw [h2]; exact f2
  · unfold fv; rw [h2, ← ratOfWord_cast, show ratOfWord 0x4000000000000000 = 2 by decide +kernel]
    norm_num
  · rw [h2]; decide +kernel

/-- The double-double `1/x` of the asymptotic paths, for `3/2 ≤ x ≤ 32`. -/
theorem recip_pr (hF : FmaNearest) (x : Float) (hx : ff x) (h1 : 3 / 2 ≤ fv x) (h2 : fv x ≤ 32) :
    ff (1.0 / x) ∧ ff ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0) ∧
      |fv (1.0 / x) + fv ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0) - 1 / fv x| ≤
        4 * u * u / fv x ∧
      |fv ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0)| ≤ 11 / 10 * u / fv x ∧
      |fv (1.0 / x) - 1 / fv x| ≤ u / fv x + η := by
  obtain ⟨of, ov, -, -, -⟩ := one_two_vals
  have hx0 : 0 < fv x := by linarith
  have hmag : Wasm.IEEE64.scaledMagnitude x.toBits ≠ 0 := by
    intro h0
    have : fv x = 0 := by simp [fv, value, Wasm.IEEE64.scaledValue, h0]
    linarith
  obtain ⟨df, derr⟩ := F64DivBounds.div_real_mixed (1.0 : Float).toBits x.toBits of hx hmag (by
    show |fv (1.0 : Float) / fv x| < 2 ^ 1022
    rw [ov, abs_of_pos (by positivity)]
    calc 1 / fv x ≤ 1 / (3 / 2) := by gcongr
      _ < 2 ^ 1022 := by norm_num)
  rw [← F64Bits.toBits_div] at df derr
  set t := 1 / fv x with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hxt : fv x * t = 1 := by rw [ht]; field_simp
  have ht1 : t ≤ 2 / 3 := by rw [ht, div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have ht2 : 1 / 32 ≤ t := by rw [ht, div_le_div_iff₀ (by norm_num) hx0]; linarith
  have hy : |fv (1.0 / x) - t| ≤ u * t + η := by
    have h' : |fv (1.0 / x) - fv (1.0 : Float) / fv x| ≤
        unitRoundoff64 * |fv (1.0 : Float) / fv x| + multiplicationUnderflowEpsilon := derr
    rw [ov, ← ht, show unitRoundoff64 = 1 / 2 ^ 53 from rfl,
      show multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 from rfl, abs_of_pos ht0] at h'
    exact h'
  set yh := 1.0 / x with hyh
  obtain ⟨nf, nv⟩ := neg_f x hx
  have hyb : |fv yh| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (fv yh) t
    rw [abs_of_pos ht0] at this
    have : u * t + η ≤ 1 / 4 := by
      have : u * t ≤ u := mul_le_of_le_one_right (by norm_num) (by linarith)
      linarith [show u + η ≤ 1 / 4 by norm_num]
    linarith
  set ρ := 1 - fv x * fv yh with hρ
  have hρe : ρ = -(fv x * (fv yh - t)) := by rw [hρ]; linear_combination (-1 : ℝ) * hxt
  have hρx : |ρ| ≤ u + fv x * η := by
    rw [hρe, abs_neg, abs_mul, abs_of_pos hx0]
    calc fv x * |fv yh - t| ≤ fv x * (u * t + η) := mul_le_mul_of_nonneg_left hy hx0.le
      _ = u + fv x * η := by linear_combination u * hxt
  have hρb : |ρ| ≤ u + 32 * η := by
    have : fv x * η ≤ 32 * η := by gcongr
    linarith
  have hab : |fv (-x) * fv yh + fv (1.0 : Float)| ≤ 2 ^ 1021 := by
    rw [nv, ov, show -fv x * fv yh + 1 = ρ by rw [hρ]; ring]
    exact hρb.trans (by norm_num)
  obtain ⟨rf, rerr⟩ := fma_f hF (-x) yh 1.0 nf df of hab
  rw [nv, ov, show -fv x * fv yh + 1 = ρ by rw [hρ]; ring] at rerr
  set r := Library.Numerics.Arithmetic.Fma.Fma.fma (-x) yh 1.0 with hr
  have hrb1 : |fv r| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub (fv r) ρ
    have : u * |ρ| ≤ u * (u + 32 * η) := by gcongr
    linarith [show u * (u + 32 * η) + η + (u + 32 * η) ≤ 2 by norm_num]
  have hyr1 : |fv yh * fv r| ≤ 2 := by
    rw [abs_mul]
    calc |fv yh| * |fv r| ≤ 1 * 2 := mul_le_mul hyb hrb1 (abs_nonneg _) (by norm_num)
      _ = 2 := by ring
  obtain ⟨lf, lerr⟩ := mul_f yh r df rf (hyr1.trans (by norm_num))
  set yl := yh * r with hyl
  -- the rounding errors in terms of `U = u` and `E = η`, which become opaque below
  have hE : η ≤ u * u * t / 1000 := by
    calc η ≤ u * u * (1 / 32) / 1000 := by norm_num
      _ ≤ u * u * t / 1000 := by gcongr
  have hU : u ≤ 1 / 10 ^ 15 := by norm_num
  have hU0 : (0 : ℝ) < u := by norm_num
  have hE0 : (0 : ℝ) ≤ η := by norm_num
  have e1 : fv yh + fv yl - t = -(ρ * ρ) * t + fv yh * (fv r - ρ) + (fv yl - fv yh * fv r) := by
    rw [hρ]; linear_combination (fv x * fv yh ^ 2 - 2 * fv yh) * hxt
  have g1 : 4 * u * u / fv x = 4 * u * u * t := by rw [ht]; ring
  have g2 : 11 / 10 * u / fv x = 11 / 10 * u * t := by rw [ht]; ring
  have g3 : u / fv x = u * t := by rw [ht]; ring
  rw [g1, g2, g3]
  set U : ℝ := 1 / 2 ^ 53 with hUdef
  set E : ℝ := 1 / 2 ^ 1075 with hEdef
  clear_value U E
  have f1 : U * t ≤ 1 / 10 ^ 15 * t := mul_le_mul_of_nonneg_right hU ht0.le
  have hUUt : U * (U * t) ≤ 1 / 10 ^ 15 * (U * t) :=
    mul_le_mul_of_nonneg_right hU (mul_nonneg hU0.le ht0.le)
  have hUU : U * U ≤ 1 / 10 ^ 15 * U := mul_le_mul_of_nonneg_right hU hU0.le
  have hUUt' : U * U * t ≤ U * U := mul_le_of_le_one_right (mul_nonneg hU0.le hU0.le) (by linarith)
  have hρ1 : |ρ| ≤ 101 / 100 * U := by linarith
  have hyh1 : |fv yh| ≤ 101 / 100 * t := by
    have := abs_sub_abs_le_abs_sub (fv yh) t
    rw [abs_of_pos ht0] at this
    linarith
  have hrρ : |fv r - ρ| ≤ 102 / 100 * (U * U) := by
    refine rerr.trans ?_
    have : U * |ρ| ≤ U * (101 / 100 * U) := mul_le_mul_of_nonneg_left hρ1 hU0.le
    linarith
  have hr1 : |fv r| ≤ 102 / 100 * U := by
    have := abs_sub_abs_le_abs_sub (fv r) ρ
    linarith
  have hyr : |fv yh * fv r| ≤ 101 / 100 * t * (102 / 100 * U) := by
    rw [abs_mul]
    exact mul_le_mul hyh1 hr1 (abs_nonneg _) (mul_nonneg (by norm_num) ht0.le)
  have hl1 : |fv yl - fv yh * fv r| ≤ U * (101 / 100 * t * (102 / 100 * U)) + E :=
    lerr.trans (by linarith [mul_le_mul_of_nonneg_left hyr hU0.le])
  refine ⟨df, lf, ?_, ?_, hy⟩
  · rw [e1]
    have k1 : |-(ρ * ρ) * t| ≤ (101 / 100 * U) * (101 / 100 * U) * t := by
      rw [abs_mul, abs_neg, abs_mul, abs_of_pos ht0]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hρ1 hρ1 (abs_nonneg _)
        (mul_nonneg (by norm_num) hU0.le)) ht0.le
    have k2 : |fv yh * (fv r - ρ)| ≤ 101 / 100 * t * (102 / 100 * (U * U)) := by
      rw [abs_mul]; exact mul_le_mul hyh1 hrρ (abs_nonneg _) (mul_nonneg (by norm_num) ht0.le)
    have k3 := abs_add3 (-(ρ * ρ) * t) (fv yh * (fv r - ρ)) (fv yl - fv yh * fv r)
    linarith
  · have k1 := abs_sub_abs_le_abs_sub (fv yl) (fv yh * fv r)
    linarith

#print axioms recip_pr

/-- The double-double `1/x²` of the asymptotic paths, for `3/2 ≤ x ≤ 32`: `uh + ul` from
`Erfc.aMul yh yh` and `ul + 2 yh yl` by one `fma`. -/
theorem usq_pr (hF : FmaNearest) (x : Float) (hx : ff x) (h1 : 3 / 2 ≤ fv x) (h2 : fv x ≤ 32) :
    ff (Erfc.aMul (1.0 / x) (1.0 / x)).1 ∧
      ff (Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * (1.0 / x)) ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0)
        (Erfc.aMul (1.0 / x) (1.0 / x)).2) ∧
      |fv (Erfc.aMul (1.0 / x) (1.0 / x)).1 + fv (Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * (1.0 / x))
        ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0) (Erfc.aMul (1.0 / x) (1.0 / x)).2) -
          (1 / fv x) ^ 2| ≤ 14 * u * u * (1 / fv x) ^ 2 ∧
      |fv (Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * (1.0 / x)) ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0)
        (Erfc.aMul (1.0 / x) (1.0 / x)).2)| ≤ 4 * u * (1 / fv x) ^ 2 := by
  obtain ⟨-, -, tf, tv, tm⟩ := one_two_vals
  obtain ⟨df, lf, hY, hyl, hy⟩ := recip_pr hF x hx h1 h2
  have hx0 : 0 < fv x := by linarith
  set t := 1 / fv x with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 2 / 3 := by rw [ht, div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have ht2 : 1 / 32 ≤ t := by rw [ht, div_le_div_iff₀ (by norm_num) hx0]; linarith
  have hY' : |fv (1.0 / x) + fv ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0) - t| ≤ 4 * u * u * t := by
    refine hY.trans (le_of_eq ?_); rw [ht]; ring
  have hyl' : |fv ((1.0 / x) * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) (1.0 / x) 1.0)| ≤ 11 / 10 * u * t := by
    refine hyl.trans (le_of_eq ?_); rw [ht]; ring
  have hy' : |fv (1.0 / x) - t| ≤ u * t + η := by
    refine hy.trans (le_of_eq ?_); rw [ht]; ring
  set yh := 1.0 / x with hyh
  set yl := yh * Library.Numerics.Arithmetic.Fma.Fma.fma (-x) yh 1.0 with hyl
  have hyb : |fv yh| < 1 := by
    have := abs_sub_abs_le_abs_sub (fv yh) t
    rw [abs_of_pos ht0] at this
    have : u * t ≤ u := mul_le_of_le_one_right (by norm_num) (by linarith)
    linarith [show u + η < 1 / 4 by norm_num]
  have hylb : |fv yl| ≤ 1 := by
    have : 11 / 10 * u * t ≤ 11 / 10 * u := by
      have := mul_le_of_le_one_right (show (0 : ℝ) ≤ 11 / 10 * u by norm_num) (show t ≤ 1 by linarith)
      linarith
    linarith [show 11 / 10 * u ≤ (1 : ℝ) by norm_num]
  have hyy1 : |fv yh * fv yh| ≤ 1 := by
    rw [abs_mul]
    calc |fv yh| * |fv yh| ≤ 1 * 1 := mul_le_mul hyb.le hyb.le (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  obtain ⟨a1, a2, ae1, ae2⟩ := aMul_f hF yh yh df df (hyy1.trans (by norm_num))
  set uh := (Erfc.aMul yh yh).1 with huh
  set ul0 := (Erfc.aMul yh yh).2 with hul0
  have hgx : gx yh.toBits ≤ 1021 := by
    apply gx_le_of_lt
    show |fv yh| < _
    rw [show (2 : ℝ) ^ (53 + 1021) / 2 ^ 1074 = 1 by norm_num]
    exact hyb
  obtain ⟨tf2, tv2⟩ := mul_pow2 2.0 yh tf df 1075 tm (by omega) (by omega)
  rw [tv] at tv2
  have hul0b : |fv ul0| ≤ 3 := by
    have e : fv ul0 = (fv uh + fv ul0 - fv yh * fv yh) - (fv uh - fv yh * fv yh) := by ring
    rw [e]
    refine (abs_sub_le' _ _).trans ?_
    have : u * u * |fv yh * fv yh| ≤ u * u * 1 := by gcongr
    have : u * |fv yh * fv yh| ≤ u * 1 := by gcongr
    linarith [show u * u * 1 + 2 * η + (u * 1 + η) ≤ 3 by norm_num]
  have hfab : |fv (2.0 * yh) * fv yl + fv ul0| ≤ 2 ^ 1021 := by
    rw [tv2]
    have : |2 * fv yh * fv yl| ≤ 2 := by
      rw [show 2 * fv yh * fv yl = 2 * (fv yh * fv yl) by ring, abs_mul, abs_two, abs_mul]
      have : |fv yh| * |fv yl| ≤ 1 * 1 := mul_le_mul hyb.le hylb (abs_nonneg _) (by norm_num)
      linarith
    have := abs_add_le (2 * fv yh * fv yl) (fv ul0)
    linarith [show (5 : ℝ) ≤ 2 ^ 1021 by norm_num]
  obtain ⟨lf2, le2⟩ := fma_f hF (2.0 * yh) yl ul0 tf2 lf a2 hfab
  rw [tv2] at le2
  set ul := Library.Numerics.Arithmetic.Fma.Fma.fma (2.0 * yh) yl ul0 with hul
  have hE : η ≤ u * u * (t * t) / 1000 := by
    have : (1 / 32 : ℝ) * (1 / 32) ≤ t * t := mul_le_mul ht2 ht2 (by norm_num) ht0.le
    calc η ≤ u * u * ((1 / 32) * (1 / 32)) / 1000 := by norm_num
      _ ≤ u * u * (t * t) / 1000 := by gcongr
  have hU : u ≤ 1 / 10 ^ 15 := by norm_num
  have hU0 : (0 : ℝ) < u := by norm_num
  have hE0 : (0 : ℝ) ≤ η := by norm_num
  have e1 : fv uh + fv ul - t ^ 2 = (fv uh + fv ul0 - fv yh * fv yh) +
      (fv ul - (2 * fv yh * fv yl + fv ul0)) +
      ((fv yh + fv yl - t) * (fv yh + fv yl + t) - fv yl * fv yl) := by ring
  rw [e1, show 14 * u * u * t ^ 2 = 14 * u * u * (t * t) by ring,
    show 4 * u * t ^ 2 = 4 * u * (t * t) by ring]
  set U : ℝ := 1 / 2 ^ 53 with hUdef
  set E : ℝ := 1 / 2 ^ 1075 with hEdef
  clear_value U E
  have htt0 : 0 < t * t := mul_pos ht0 ht0
  have hUtt : U * (t * t) ≥ 0 := mul_nonneg hU0.le htt0.le
  have f1 : U * t ≤ 1 / 10 ^ 15 * t := mul_le_mul_of_nonneg_right hU ht0.le
  have g1 : U * (t * t) ≤ U * t :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_left ht0.le (by linarith)) hU0.le
  have g2 : U * U * (t * t) ≤ 1 / 10 ^ 15 * (U * (t * t)) := by
    have := mul_le_mul_of_nonneg_right hU hUtt; linarith
  have hyh1 : |fv yh| ≤ 101 / 100 * t := by
    have := abs_sub_abs_le_abs_sub (fv yh) t
    rw [abs_of_pos ht0] at this
    linarith
  have hyy : |fv yh * fv yh| ≤ 10201 / 10000 * (t * t) := by
    rw [abs_mul]
    calc |fv yh| * |fv yh| ≤ (101 / 100 * t) * (101 / 100 * t) :=
          mul_le_mul hyh1 hyh1 (abs_nonneg _) (mul_nonneg (by norm_num) ht0.le)
      _ = 10201 / 10000 * (t * t) := by ring
  have hul0' : |fv ul0| ≤ 104 / 100 * U * (t * t) := by
    have e : fv ul0 = (fv uh + fv ul0 - fv yh * fv yh) - (fv uh - fv yh * fv yh) := by ring
    rw [e]
    refine (abs_sub_le' _ _).trans ?_
    have k1 : U * U * |fv yh * fv yh| ≤ U * U * (10201 / 10000 * (t * t)) :=
      mul_le_mul_of_nonneg_left hyy (mul_nonneg hU0.le hU0.le)
    have k2 : U * |fv yh * fv yh| ≤ U * (10201 / 10000 * (t * t)) :=
      mul_le_mul_of_nonneg_left hyy hU0.le
    have k3 : U * U * (t * t) ≤ 1 / 10 ^ 15 * (U * (t * t)) := by
      have := mul_le_mul_of_nonneg_right hU hUtt; linarith
    linarith
  have h2yl : |fv yh * fv yl| ≤ 1111 / 1000 * U * (t * t) := by
    rw [abs_mul]
    calc |fv yh| * |fv yl| ≤ (101 / 100 * t) * (11 / 10 * U * t) :=
          mul_le_mul hyh1 hyl' (abs_nonneg _) (mul_nonneg (by norm_num) ht0.le)
      _ = 1111 / 1000 * U * (t * t) := by ring
  have hsum : |2 * fv yh * fv yl + fv ul0| ≤ 33 / 10 * U * (t * t) := by
    have : |2 * fv yh * fv yl| = 2 * |fv yh * fv yl| := by
      rw [show 2 * fv yh * fv yl = 2 * (fv yh * fv yl) by ring, abs_mul, abs_two]
    have := abs_add_le (2 * fv yh * fv yl) (fv ul0)
    linarith
  have hle2 : |fv ul - (2 * fv yh * fv yl + fv ul0)| ≤ 34 / 10 * (U * U * (t * t)) := by
    refine le2.trans ?_
    have k : U * |2 * fv yh * fv yl + fv ul0| ≤ U * (33 / 10 * U * (t * t)) :=
      mul_le_mul_of_nonneg_left hsum hU0.le
    have : U * (33 / 10 * U * (t * t)) = 33 / 10 * (U * U * (t * t)) := by ring
    linarith
  have hUUtt : U * U * (t * t) ≤ 1 / 10 ^ 15 * (U * (t * t)) := by
    have := mul_le_mul_of_nonneg_right hU hUtt; linarith
  refine ⟨a1, lf2, ?_, ?_⟩
  · have k1 : |fv uh + fv ul0 - fv yh * fv yh| ≤ 10201 / 10000 * (U * U * (t * t)) + 2 * E := by
      refine ae2.trans ?_
      have := mul_le_mul_of_nonneg_left hyy (mul_nonneg hU0.le hU0.le)
      linarith
    have hYt : |fv yh + fv yl + t| ≤ 201 / 100 * t := by
      have := abs_add_le (fv yh + fv yl - t) (2 * t)
      rw [show fv yh + fv yl - t + 2 * t = fv yh + fv yl + t by ring,
        abs_of_pos (by linarith : (0 : ℝ) < 2 * t)] at this
      have f2 : U * (U * t) ≤ 1 / 10 ^ 15 * (U * t) :=
        mul_le_mul_of_nonneg_right hU (mul_nonneg hU0.le ht0.le)
      linarith
    have k3 : |(fv yh + fv yl - t) * (fv yh + fv yl + t)| ≤ 805 / 100 * (U * U * (t * t)) := by
      rw [abs_mul]
      calc _ ≤ (4 * U * U * t) * (201 / 100 * t) :=
            mul_le_mul hY' hYt (abs_nonneg _)
              (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hU0.le) hU0.le) ht0.le)
        _ = 804 / 100 * (U * U * (t * t)) := by ring
        _ ≤ 805 / 100 * (U * U * (t * t)) := by
          have := mul_nonneg (mul_nonneg hU0.le hU0.le) htt0.le; linarith
    have k4 : |fv yl * fv yl| ≤ 121 / 100 * (U * U * (t * t)) := by
      rw [abs_mul]
      calc |fv yl| * |fv yl| ≤ (11 / 10 * U * t) * (11 / 10 * U * t) :=
            mul_le_mul hyl' hyl' (abs_nonneg _)
              (mul_nonneg (mul_nonneg (by norm_num) hU0.le) ht0.le)
        _ = 121 / 100 * (U * U * (t * t)) := by ring
    have k5 := abs_sub_le' ((fv yh + fv yl - t) * (fv yh + fv yl + t)) (fv yl * fv yl)
    have k6 := abs_add3 (fv uh + fv ul0 - fv yh * fv yh) (fv ul - (2 * fv yh * fv yl + fv ul0))
      ((fv yh + fv yl - t) * (fv yh + fv yl + t) - fv yl * fv yl)
    have hE' : E ≤ U * U * (t * t) / 1000 := hE
    linarith
  · have := abs_sub_abs_le_abs_sub (fv ul) (2 * fv yh * fv yl + fv ul0)
    linarith

#print axioms usq_pr

end Library.Numerics.Float64.Erfc.ErfcRecip
