import Library.Numerics.Float64.Bessel.BesselSmallY0
import Library.Numerics.Float64.Bessel.BesselJ0Small
import Library.Numerics.Float64.Bessel.BesselModSmall
import Library.Numerics.Float64.Log.LogNearAll
import Library.Numerics.Float64.Bessel.BesselSpecial

/-!
`Bessel.y0 x` for `0 < x < 2`: the result lies within `11 · 2^-53 · √(J₀(x)² + Y₀(x)²)` of
`Y₀(x)` (`y0_small`).  Up to the high word `0x3e400000`, about `2^-27`, the code returns
`u₀₀ + tpi · ln x`, whose error `tiny_chain` bounds as `2.41 u ℓ + 0.1 u` with `ℓ = |ln x|`;
`Y₀(x)` lies within `0.16 u ℓ + 0.18 u` of `u₀₀ + (2/π) ln x` there (`tiny_close`), and
`BesselModSmall.Y0_log` gives `|Y₀| ≥ 0.597 ℓ`.  Above, the code returns
`U(z)/V(z) + tpi (j0 x · ln x)`, which `BesselSmallY0.log_piece` bounds up to 1/2 and
`BesselSmallY0.piece_0` to `piece_6` from 1/2 to 2, with `j0` from `BesselJ0Small.j0_small`,
`ln x` from `Library.Numerics.Float64.Log.LogNearAll.log_near`, and `BesselSmallApprox.y0_approx` for fdlibm's approximation;
`BesselModSmall.modulus0_half` bounds the modulus below by 1/2 there.
-/

namespace Library.Numerics.Float64.Bessel.BesselY0Small
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound F64Approx F64Horner BesselPQEval BesselSmallApprox
  BesselJ0Large BesselSmallJ0 BesselJ0Small BesselModSmall BesselSmallY0 BesselCombine LogNearAll Real
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- A positive double is at least `2^-1074`. -/
theorem value_ge_min (w : UInt64) (hs : w.toNat < 2 ^ 63) (hpos : 0 < value w) :
    1 / 2 ^ 1074 ≤ value w := by
  have hsg : Wasm.IEEE64.sign w = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]; omega
  have hv : value w = (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hsg]
  rw [hv] at hpos ⊢
  have hm : 1 ≤ Wasm.IEEE64.scaledMagnitude w := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude w) with h | h
    · rw [h, Nat.cast_zero, zero_div] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h
  have : (1 : ℝ) ≤ Wasm.IEEE64.scaledMagnitude w := by exact_mod_cast hm
  exact div_le_div_of_nonneg_right this (by positivity)

/-- `|ln v| = -ln v ≥ ln 2` for `0 < v ≤ 1/2`, and at most 745 from `v ≥ 2^-1074`. -/
theorem log_facts (v : ℝ) (h0 : 1 / 2 ^ 1074 ≤ v) (h1 : v ≤ 1 / 2) :
    |Real.log v| = -Real.log v ∧ 6931 / 10000 ≤ -Real.log v ∧ -Real.log v ≤ 745 := by
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) h0
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have ha : Real.log v ≤ -Real.log 2 := by
    have := Real.log_le_log hv0 h1
    rwa [one_div, Real.log_inv] at this
  have hb : -(1074 * Real.log 2) ≤ Real.log v := by
    have := Real.log_le_log (by positivity) h0
    rwa [one_div, Real.log_inv, Real.log_pow] at this
  refine ⟨abs_of_neg (by linarith), by linarith, ?_⟩
  nlinarith

/-- `√(J² + Y²) ≥ a` from `|Y| ≥ a ≥ 0`. -/
theorem mod_ge_Y {J Y a : ℝ} (ha : 0 ≤ a) (h : a ≤ |Y|) : a ≤ √(J ^ 2 + Y ^ 2) := by
  rw [show a = √(a ^ 2) by rw [Real.sqrt_sq ha]]
  apply Real.sqrt_le_sqrt
  have := sq_abs Y
  nlinarith [sq_nonneg J, abs_nonneg Y]

theorem u00_bound : |value (0xBFB2E4D699CBD01F : UInt64)| ≤ (74 / 1000 : ℚ) :=
  abs_value_le _ _ (by decide +kernel)

/-- `u₀₀ + tpi · ln x` for a positive finite `x`, with `ℓ = |ln x|`. -/
theorem tiny_chain (x : Float) (hf : Finite x.toBits) (hpos : 0 < value x.toBits) (ℓ : ℝ)
    (hℓ : |Real.log (value x.toBits)| = ℓ) (hℓ1 : ℓ ≤ 745) :
    FApprox (Float.ofBits 0xBFB2E4D699CBD01F + Bessel.tpi * Log.log x)
      (value (0xBFB2E4D699CBD01F : UInt64) + 2 / π * Real.log (value x.toBits))
      (241 / 100 * 𝐮 * ℓ + 1 / 10 * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hℓ0 : 0 ≤ ℓ := by rw [← hℓ]; exact abs_nonneg _
  have hL := log_near x hf hpos
  have hL' : FApprox (Log.log x) (Real.log (value x.toBits)) (6 / 5 * 𝐮 * ℓ + 1 / 2 ^ 59) := by
    have e : logErr (Real.log (value x.toBits)) = 6 / 5 * 𝐮 * ℓ + 1 / 2 ^ 59 := by
      unfold logErr; rw [hℓ]
    rw [e] at hL
    exact hL
  have ht := fapprox_mul tpi_near hL' (6367 / 10000) ℓ tpi_le (le_of_eq hℓ) _ le_rfl
    (by rw [hu]; nlinarith)
  have ht' : FApprox (Bessel.tpi * Log.log x) (2 / π * Real.log (value x.toBits))
      (1762 / 1000 * 𝐮 * ℓ + 11 / 1000 * 𝐮) := fmono ht (by rw [hu]; nlinarith)
  have htm : |2 / π * Real.log (value x.toBits)| ≤ 6367 / 10000 * ℓ := by
    rw [abs_mul, hℓ]; exact mul_le_mul_of_nonneg_right tpi_le hℓ0
  have hc := fapprox_ofBits 0xBFB2E4D699CBD01F (by unfold CodeLib.IEEE64.Finite; decide)
  have hcm := u00_bound
  push_cast at hcm
  have hres := fapprox_add hc ht'
    (74 / 1000 + 6367 / 10000 * ℓ + (0 + (1762 / 1000 * 𝐮 * ℓ + 11 / 1000 * 𝐮))) (by
      have := abs_add_le (value (0xBFB2E4D699CBD01F : UInt64)) (2 / π * Real.log (value x.toBits))
      linarith) (by rw [hu]; nlinarith)
  exact fmono hres (by rw [hu]; nlinarith)

theorem uv_check :
    check (subP U0 (scaleP (ratOfWord 0xBFB2E4D699CBD01F) V0)) 0 (1 / 2 ^ 53)
      (18 / 100 / 2 ^ 53) 0 = true := by
  decide +kernel

/-- `U(z)/V(z)` within `0.18 u` of `u₀₀` for `0 ≤ z ≤ 2^-53`. -/
theorem uv_tiny (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2 ^ 53) :
    |eval U0 z / eval V0 z - value (0xBFB2E4D699CBD01F : UInt64)| ≤ 18 / 100 * 𝐮 := by
  obtain ⟨-, -, hV0, -⟩ := coeff_facts
  have hV : 1 ≤ eval V0 z := one_le_eval V0 rfl hV0 z h0
  have hc := check_sound _ _ _ _ _ uv_check z (by push_cast; exact h0) (by push_cast; exact h1)
  rw [eval_subP, eval_scaleP] at hc
  have hq : (value (0xBFB2E4D699CBD01F : UInt64)) = (ratOfWord 0xBFB2E4D699CBD01F : ℝ) :=
    (ratOfWord_cast _).symm
  rw [hq]
  have e : eval U0 z / eval V0 z - (ratOfWord 0xBFB2E4D699CBD01F : ℝ) =
      (eval U0 z - (ratOfWord 0xBFB2E4D699CBD01F : ℝ) * eval V0 z) / eval V0 z := by
    field_simp
  have hV0p : 0 < eval V0 z := by linarith
  rw [e, abs_div, abs_of_pos hV0p, div_le_iff₀ hV0p]
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  push_cast at hc
  rw [hu]
  have : (18 / 100 / 2 ^ 53 : ℝ) ≤ 18 / 100 * (1 / 2 ^ 53) * eval V0 z := by
    have h := mul_le_mul_of_nonneg_left hV (show (0 : ℝ) ≤ 18 / 100 * (1 / 2 ^ 53) by positivity)
    linarith
  linarith

/-- `Y₀` within `0.16 u ℓ + 0.18 u + 0.21 u + 2^-60` of `u₀₀ + (2/π) ln v` for
`0 < v ≤ 2^-27 (1 + 2^-20)`. -/
theorem tiny_close (v : ℝ) (h0 : 0 < v) (h1 : v ≤ 1 / 2 ^ 27 * (1 + 1 / 2 ^ 20)) :
    |Y0 v - (value (0xBFB2E4D699CBD01F : UInt64) + 2 / π * Real.log v)| ≤
      16 / 100 * 𝐮 * |Real.log v| + (39 / 100 * 𝐮 + 1 / 2 ^ 60) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hv2 : v ^ 2 ≤ 1 / 2 ^ 53 := by
    have := pow_le_pow_left₀ h0.le h1 2
    have e : (1 / 2 ^ 27 * (1 + 1 / 2 ^ 20) : ℝ) ^ 2 ≤ 1 / 2 ^ 53 := by norm_num
    linarith
  have hy := y0_approx v h0 (by norm_num at h1 ⊢; linarith)
  have hq := j0_quad v (by rw [abs_of_pos h0]; norm_num at h1 ⊢; linarith)
  have huv := uv_tiny (v ^ 2) (by positivity) hv2
  have hv4 : v ^ 4 ≤ 1 / 2 ^ 106 := by
    have := pow_le_pow_left₀ (by positivity) hv2 2
    rw [← pow_mul] at this
    norm_num at this ⊢
    linarith
  have hJ1 : |J0 v - 1| ≤ 1 / 2 ^ 55 + 1 / 2 ^ 111 := by
    have := abs_sub_le (J0 v) (1 - v ^ 2 / 4) 1
    rw [show |1 - v ^ 2 / 4 - 1| = v ^ 2 / 4 by
      rw [show 1 - v ^ 2 / 4 - 1 = -(v ^ 2 / 4) by ring, abs_neg, abs_of_nonneg (by positivity)]]
      at this
    have : v ^ 2 / 4 ≤ 1 / 2 ^ 55 := by norm_num at hv2 ⊢; linarith
    have : v ^ 4 / 32 ≤ 1 / 2 ^ 111 := by norm_num at hv4 ⊢; linarith
    linarith
  have hp := tpi_le
  have hlog : |2 / π * Real.log v * (J0 v - 1)| ≤ 6367 / 10000 * |Real.log v| * (1 / 2 ^ 55 + 1 / 2 ^ 111) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hp (abs_nonneg _)) hJ1 (abs_nonneg _)
      (by positivity)
  have e : Y0 v - (value (0xBFB2E4D699CBD01F : UInt64) + 2 / π * Real.log v) =
      (Y0 v - 2 / π * Real.log v * J0 v - eval U0 (v ^ 2) / eval V0 (v ^ 2)) +
      2 / π * Real.log v * (J0 v - 1) +
      (eval U0 (v ^ 2) / eval V0 (v ^ 2) - value (0xBFB2E4D699CBD01F : UInt64)) := by ring
  rw [e]
  have t1 := abs_add_le (Y0 v - 2 / π * Real.log v * J0 v - eval U0 (v ^ 2) / eval V0 (v ^ 2) +
      2 / π * Real.log v * (J0 v - 1)) (eval U0 (v ^ 2) / eval V0 (v ^ 2) -
      value (0xBFB2E4D699CBD01F : UInt64))
  have t2 := abs_add_le (Y0 v - 2 / π * Real.log v * J0 v - eval U0 (v ^ 2) / eval V0 (v ^ 2))
    (2 / π * Real.log v * (J0 v - 1))
  have hl0 := abs_nonneg (Real.log v)
  have h3 : 6367 / 10000 * |Real.log v| * (1 / 2 ^ 55 + 1 / 2 ^ 111) ≤
      16 / 100 * 𝐮 * |Real.log v| := by
    rw [hu]
    nlinarith
  have h4 : 21 / 100 * 𝐮 + 1 / 2 ^ 60 + 18 / 100 * 𝐮 ≤ 39 / 100 * 𝐮 + 1 / 2 ^ 60 := by
    rw [hu]; norm_num
  linarith

/-- A result within `E` of `U(z)/V(z) + (2/π) J₀ ln x` lies within `E + 0.21 u + 2^-60` of `Y₀`. -/
theorem main_close {T : Float} {v E : ℝ} (hv0 : 0 < v) (hv2 : v ≤ 2)
    (h : FApprox T (eval U0 (v ^ 2) / eval V0 (v ^ 2) + 2 / π * (J0 v * Real.log v)) E) :
    Finite T.toBits ∧ |value T.toBits - Y0 v| ≤ E + (21 / 100 * 𝐮 + 1 / 2 ^ 60) := by
  refine ⟨h.1, ?_⟩
  have h1 := h.2
  have h2 := y0_approx v hv0 hv2
  have h3 := abs_sub_le (value T.toBits)
    (eval U0 (v ^ 2) / eval V0 (v ^ 2) + 2 / π * (J0 v * Real.log v)) (Y0 v)
  have h4 : |eval U0 (v ^ 2) / eval V0 (v ^ 2) + 2 / π * (J0 v * Real.log v) - Y0 v| =
      |Y0 v - 2 / π * Real.log v * J0 v - eval U0 (v ^ 2) / eval V0 (v ^ 2)| := by
    rw [abs_sub_comm]; congr 1; ring
  linarith

/-- `|J₀| ≤ Jm` on a piece of `[3/2, 2]` from a check of the series. -/
theorem J0_upper (v a b : ℝ) (c lo hi r : ℚ) (d : ℕ)
    (h : check (subP (a0List 18) [c]) lo hi r d = true) (ha0 : 0 ≤ a) (hav : a ≤ v) (hvb : v ≤ b)
    (hb2 : b ≤ 2) (hlo : (lo : ℝ) ≤ a ^ 2 / 4) (hhi : b ^ 2 / 4 ≤ (hi : ℝ)) (Jm : ℝ)
    (hJm : (c : ℝ) + r + 1 / 2 ^ 99 ≤ Jm) (hpos : 0 ≤ (c : ℝ) - r - 1 / 2 ^ 99) : |J0 v| ≤ Jm := by
  have hs := (series_close v (by rw [abs_of_nonneg (by linarith)]; linarith)).1
  obtain ⟨z1, z2⟩ := zeta_mono ha0 hav hvb
  have rr := range_of_check _ _ _ _ _ _ h _ (by linarith) (by linarith) _ hs
  rw [abs_le]
  constructor <;> linarith [rr.1, rr.2]

/-- `|J₀| ≤ 1 - a²/4 + b⁴/32` on `[a, b]` with `0 ≤ a` and `b ≤ 3/2`. -/
theorem J0_upper_quad (v a b : ℝ) (ha0 : 0 ≤ a) (hav : a ≤ v) (hvb : v ≤ b) (hb : b ≤ 3 / 2)
    (Jm : ℝ) (hJm : 1 - a ^ 2 / 4 + b ^ 4 / 32 ≤ Jm) : |J0 v| ≤ Jm := by
  have hq := j0_quad v (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h2 : a ^ 2 ≤ v ^ 2 := by nlinarith
  have h4 : v ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ (by linarith) hvb 4
  have hb4 : b ^ 4 ≤ 81 / 16 := by
    have := pow_le_pow_left₀ (by linarith) hb 4
    norm_num at this ⊢; linarith
  have hv2 : v ^ 2 ≤ 9 / 4 := by nlinarith
  rw [abs_le] at hq ⊢
  constructor <;> nlinarith

/-- `|J₀| ≤ 1` for `|x| ≤ 2`. -/
theorem J0_le_one (v : ℝ) (hv : |v| ≤ 2) : |J0 v| ≤ 1 := by
  have hq := j0_quad v hv
  have h2 : v ^ 2 ≤ 4 := by nlinarith [abs_nonneg v, sq_abs v]
  have h4 : v ^ 4 ≤ 8 * v ^ 2 := by nlinarith [sq_nonneg v]
  have h0 : 0 ≤ v ^ 2 := sq_nonneg v
  rw [abs_le] at hq ⊢
  constructor <;> nlinarith

/-- `|ln v| ≤ 0.6932` for `1/2 ≤ v ≤ 2`. -/
theorem log_mid (v : ℝ) (h1 : 1 / 2 ≤ v) (h2 : v ≤ 2) : |Real.log v| ≤ 1733 / 2500 := by
  have hl := Real.log_two_lt_d9
  have hv0 : 0 < v := by linarith
  have ha := Real.log_le_log hv0 h2
  have hb := Real.log_le_log (by norm_num) h1
  rw [one_div, Real.log_inv] at hb
  rw [abs_le]
  constructor <;> linarith

/-- `y0` for `0 < x < 2`. -/
theorem y0_small (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnz : x.toBits.toNat ≠ 0) (h2 : x.toBits.toNat < 0x4000000000000000) :
    |value (Bessel.y0 x).toBits - Y0 (value x.toBits)| ≤
      11 * 𝐮 * √(J0 (value x.toBits) ^ 2 + Y0 (value x.toBits) ^ 2) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  have hN : x.toBits.toNat % 2 ^ 63 = x.toBits.toNat := Nat.mod_eq_of_lt hpos
  have hixN := Library.Numerics.Float64.Trig.TrigSinCos.high_word x.toBits
  set v := value x.toBits with hvdef
  have hv0 : 0 < v := by
    have h := F64PositiveOrder.value_strict (left := (0 : UInt64)) (right := x.toBits) hpos
      (by simp only [UInt64.toNat_zero]; omega)
    rwa [F64Magnitude.value_zero] at h
  have hv2 : v < 2 := by
    have h := F64PositiveOrder.value_strict (left := x.toBits)
      (right := (0x4000000000000000 : UInt64)) (by decide) h2
    rwa [value_two] at h
  have hmin := value_ge_min x.toBits hpos hv0
  have hj0 : FApprox (Bessel.j0 x) (J0 v) (235 / 100 * 𝐮) :=
    j0_small x hxf (by rw [hN]; exact h2)
  unfold Bessel.y0 Bessel.y0With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_right (show ¬ (x.toBits <<< 1 == 0) = true by
      rw [BesselSpecial.double_zero, decide_eq_true_iff]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 63 == 1) = true by
      rw [BesselSpecial.sign_bit, decide_eq_true_iff]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 1073741824) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  by_cases ht : x.toBits >>> 32 &&& 2147483647 ≤ 1044381696
  · rw [ite_eq_left ht]
    have hsmall : v < 1 / 2 ^ 27 * (1 + 1 / 2 ^ 20) := by
      have h := F64PositiveOrder.value_strict (left := x.toBits)
        (right := (0x3E40000100000000 : UInt64)) (by decide) (by
          have := UInt64.le_iff_toNat_le.mp ht
          rw [hixN] at this
          simp only [UInt64.reduceToNat] at this
          simp only [UInt64.reduceToNat]
          omega)
      have e : value (0x3E40000100000000 : UInt64) = 1 / 2 ^ 27 * (1 + 1 / 2 ^ 20) := by
        rw [← ratOfWord_cast]
        have : ratOfWord 0x3E40000100000000 = 1 / 2 ^ 27 * (1 + 1 / 2 ^ 20) := by decide +kernel
        rw [this]; norm_num
      rwa [e] at h
    obtain ⟨hlabs, hl1, hl2⟩ := log_facts v hmin (by norm_num at hsmall ⊢; linarith)
    have hc := tiny_chain x hxf hv0 _ hlabs hl2
    have hcl := tiny_close v hv0 hsmall.le
    rw [hlabs] at hcl
    have hY := Y0_log v hv0 (by norm_num at hsmall ⊢; linarith)
    have hM : 597 / 1000 * -Real.log v ≤ √(J0 v ^ 2 + Y0 v ^ 2) :=
      mod_ge_Y (by linarith) (by rw [abs_of_neg (by linarith)]; linarith)
    have h3 := abs_sub_le (value (Float.ofBits 0xBFB2E4D699CBD01F + Bessel.tpi * Log.log x).toBits)
      (value (0xBFB2E4D699CBD01F : UInt64) + 2 / π * Real.log v) (Y0 v)
    rw [abs_sub_comm (value (0xBFB2E4D699CBD01F : UInt64) + 2 / π * Real.log v)] at h3
    have h4 := hc.2
    have hM' : 11 * 𝐮 * (597 / 1000 * -Real.log v) ≤ 11 * 𝐮 * √(J0 v ^ 2 + Y0 v ^ 2) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have h5 : 241 / 100 * 𝐮 * -Real.log v + 1 / 10 * 𝐮 +
        (16 / 100 * 𝐮 * -Real.log v + (39 / 100 * 𝐮 + 1 / 2 ^ 60)) ≤
        11 * 𝐮 * (597 / 1000 * -Real.log v) := by
      rw [hu]; nlinarith
    show |value (Float.ofBits 0xBFB2E4D699CBD01F + Bessel.tpi * Log.log x).toBits - Y0 v| ≤ _
    linarith
  · rw [ite_eq_right ht]
    have hn : ¬ (x.toBits >>> 32 &&& 2147483647).toNat ≤ (1044381696 : UInt64).toNat :=
      fun h => ht (UInt64.le_iff_toNat_le.mpr h)
    rw [hixN] at hn
    simp only [UInt64.reduceToNat] at hn
    have ha : 1 / 134217728 ≤ v := by
      have h := (F64PositiveOrder.value_le_iff (left := (0x3E40000000000000 : UInt64))
        (right := x.toBits) (by decide) hpos).mpr (by simp only [UInt64.reduceToNat]; omega)
      have e : value (0x3E40000000000000 : UInt64) = 1 / 134217728 := by
        rw [← ratOfWord_cast]
        have : ratOfWord 0x3E40000000000000 = 1 / 134217728 := by decide +kernel
        rw [this]; norm_num
      rwa [e] at h
    have hL := log_near x hxf hv0
    show |value (hornerF (u0w.map Float.ofBits) (x * x) / hornerF (1.0 :: v0w.map Float.ofBits) (x * x) +
        Bessel.tpi * (Bessel.j0 x * Log.log x)).toBits - Y0 v| ≤ _
    rcases le_or_gt v (1 / 2) with c0 | c0
    · obtain ⟨hlabs, hl1, hl2⟩ := log_facts v hmin c0
      have hl19 : -Real.log v ≤ 19 := by
        have hb := Real.log_le_log (by positivity) ha
        rw [show (1 / 134217728 : ℝ) = (2 ^ 27)⁻¹ by norm_num, Real.log_inv, Real.log_pow] at hb
        have := Real.log_two_lt_d9
        push_cast at hb
        linarith
      have hL' : FApprox (Log.log x) (Real.log v) (6 / 5 * 𝐮 * -Real.log v + 1 / 2 ^ 59) := by
        have e : logErr (Real.log v) = 6 / 5 * 𝐮 * -Real.log v + 1 / 2 ^ 59 := by
          unfold logErr; rw [hlabs]
        rw [e] at hL
        exact hL
      have hJm : |J0 v| ≤ 1 := J0_le_one v (by rw [abs_of_pos hv0]; linarith)
      have hp := log_piece x (Bessel.j0 x) (Log.log x) hxf v rfl ha c0 _ hlabs hl19 hj0 hJm hL'
      have hcl := main_close hv0 hv2.le hp
      have hY := Y0_log v hv0 c0
      have hM : 597 / 1000 * -Real.log v ≤ √(J0 v ^ 2 + Y0 v ^ 2) :=
        mod_ge_Y (by linarith) (by rw [abs_of_neg (by linarith)]; linarith)
      have hM' : 11 * 𝐮 * (597 / 1000 * -Real.log v) ≤ 11 * 𝐮 * √(J0 v ^ 2 + Y0 v ^ 2) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      have h5 : 1133 / 250 * 𝐮 * -Real.log v + 443 / 1000 * 𝐮 + (21 / 100 * 𝐮 + 1 / 2 ^ 60) ≤
          11 * 𝐮 * (597 / 1000 * -Real.log v) := by
        rw [hu]; nlinarith
      linarith [hcl.2]
    · have hLm := log_mid v c0.le hv2.le
      have hL' : FApprox (Log.log x) (Real.log v) (5199 / 6250 * 𝐮 + 1 / 2 ^ 59) := by
        refine fmono hL ?_
        unfold logErr
        have := mul_le_mul_of_nonneg_left hLm (show (0 : ℝ) ≤ 6 / 5 * 𝐮 by positivity)
        rw [hu] at this ⊢
        norm_num at this ⊢
        linarith
      have hM := modulus0_half v hv0.le hv2.le
      have hM' : 11 * 𝐮 * (1 / 2) ≤ 11 * 𝐮 * √(J0 v ^ 2 + Y0 v ^ 2) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      have fin : ∀ E : ℝ, E + (21 / 100 * 𝐮 + 1 / 2 ^ 60) ≤ 11 * 𝐮 * (1 / 2) →
          FApprox (hornerF (u0w.map Float.ofBits) (x * x) /
            hornerF (1.0 :: v0w.map Float.ofBits) (x * x) + Bessel.tpi * (Bessel.j0 x * Log.log x))
            (eval U0 (v ^ 2) / eval V0 (v ^ 2) + 2 / π * (J0 v * Real.log v)) E →
          |value (hornerF (u0w.map Float.ofBits) (x * x) /
            hornerF (1.0 :: v0w.map Float.ofBits) (x * x) +
            Bessel.tpi * (Bessel.j0 x * Log.log x)).toBits - Y0 v| ≤
            11 * 𝐮 * √(J0 v ^ 2 + Y0 v ^ 2) := by
        intro E hE hp
        have hcl := (main_close hv0 hv2.le hp).2
        linarith
      obtain ⟨-, k1, k2, k3, k4, -⟩ := checks_J0
      have e1 : (1 : ℝ) / 2 ^ 99 ≤ 1 / 10 ^ 20 := by norm_num
      rcases le_or_gt v 1 with c1 | c1
      · exact fin _ (by rw [hu]; norm_num) (piece_0 x (Bessel.j0 x) (Log.log x) hxf v rfl c0.le c1
          hj0 (J0_upper_quad v (1 / 2) 1 (by norm_num) c0.le c1 (by norm_num) 1 (by norm_num))
          hL' hLm)
      rcases le_or_gt v (5 / 4) with c2 | c2
      · exact fin _ (by rw [hu]; norm_num) (piece_1 x (Bessel.j0 x) (Log.log x) hxf v rfl c1.le c2
          hj0 (J0_upper_quad v 1 (5 / 4) (by norm_num) c1.le c2 (by norm_num) _ (by norm_num))
          hL' hLm)
      rcases le_or_gt v (3 / 2) with c3 | c3
      · exact fin _ (by rw [hu]; norm_num) (piece_2 x (Bessel.j0 x) (Log.log x) hxf v rfl c2.le c3
          hj0 (J0_upper_quad v (5 / 4) (3 / 2) (by norm_num) c2.le c3 (by norm_num) _ (by norm_num))
          hL' hLm)
      rcases le_or_gt v (13 / 8) with c4 | c4
      · exact fin _ (by rw [hu]; norm_num) (piece_3 x (Bessel.j0 x) (Log.log x) hxf v rfl c3.le c4
          hj0 (J0_upper v (3 / 2) (13 / 8) _ _ _ _ _ k1 (by norm_num) c3.le c4 (by norm_num)
            (by norm_num) (by norm_num) _ (by push_cast; linarith) (by push_cast; linarith))
          hL' hLm)
      rcases le_or_gt v (7 / 4) with c5 | c5
      · exact fin _ (by rw [hu]; norm_num) (piece_4 x (Bessel.j0 x) (Log.log x) hxf v rfl c4.le c5
          hj0 (J0_upper v (13 / 8) (7 / 4) _ _ _ _ _ k2 (by norm_num) c4.le c5 (by norm_num)
            (by norm_num) (by norm_num) _ (by push_cast; linarith) (by push_cast; linarith))
          hL' hLm)
      rcases le_or_gt v (15 / 8) with c6 | c6
      · exact fin _ (by rw [hu]; norm_num) (piece_5 x (Bessel.j0 x) (Log.log x) hxf v rfl c5.le c6
          hj0 (J0_upper v (7 / 4) (15 / 8) _ _ _ _ _ k3 (by norm_num) c5.le c6 (by norm_num)
            (by norm_num) (by norm_num) _ (by push_cast; linarith) (by push_cast; linarith))
          hL' hLm)
      exact fin _ (by rw [hu]; norm_num) (piece_6 x (Bessel.j0 x) (Log.log x) hxf v rfl c6.le hv2.le
        hj0 (J0_upper v (15 / 8) 2 _ _ _ _ _ k4 (by norm_num) c6.le hv2.le (by norm_num)
          (by norm_num) (by norm_num) _ (by push_cast; linarith) (by push_cast; linarith))
        hL' hLm)

#print axioms value_ge_min
#print axioms J0_le_one
#print axioms tiny_chain
#print axioms uv_tiny
#print axioms tiny_close
#print axioms main_close
#print axioms y0_small

end Library.Numerics.Float64.Bessel.BesselY0Small
