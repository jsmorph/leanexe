import Verified.Examples.BesselSmallY1
import Verified.Examples.BesselJ1Small
import Verified.Examples.BesselModSmall1
import Verified.Examples.BesselY0Small

/-!
`Bessel.y1 x` for `2^-1022 ≤ x < 2`: the result lies within `12 · 2^-53 · √(J₁(x)² + Y₁(x)²)` of
`Y₁(x)` (`y1_small`).  Up to the high word `0x3c900000`, about `2^-54`, the code returns
`-tpi/x`, within `u/x` of `-2/(π x)` once the quotient stays below `2^1022`, and `Y₁(x)` lies
within `300 x` of `-2/(π x)` there (`tiny_close`).  Above, the code returns
`x (U(z)/V(z)) + tpi (j1 x · ln x - 1/x)`, which `BesselSmallY1.small_piece` bounds up to 1 with
`x |ln x| ≤ 1/e` (`xlog_le`), and `BesselSmallY1.piece_0` to `piece_6` from 1 to 2, with `j1`
from `BesselJ1Small.j1_small`, `ln x` from `LogNearAll.log_near`, and
`BesselSmallApprox.y1_approx` for fdlibm's approximation.  The modulus is at least `2/(π x)` up to
1 (`BesselModSmall1.modulus1_small`) and at least `J₁` above, which `BesselModSmall1.J1_piece`
bounds on each piece.
-/

namespace Verified.Examples.BesselY1Small
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound F64Approx F64Horner BesselPQEval BesselSmallApprox
  BesselJ0Large BesselSmallJ0 BesselJ1Small BesselModSmall BesselModSmall1 BesselSmallY0
  BesselSmallY1 BesselCombine LogNearAll BesselY0Small Real
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- `-x ln x ≤ 0.3679` for `0 < x`, from `ln y ≤ y/e`. -/
theorem xlog_le (v : ℝ) (h0 : 0 < v) : v * -Real.log v ≤ 3679 / 10000 := by
  have he := Real.exp_one_gt_d9
  have hy : 0 < 1 / v / exp 1 := by positivity
  have h := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (by positivity) (by positivity), Real.log_exp, one_div, Real.log_inv] at h
  have h2 : -Real.log v ≤ v⁻¹ / exp 1 := by linarith
  have h3 : v * -Real.log v ≤ v * (v⁻¹ / exp 1) := mul_le_mul_of_nonneg_left h2 h0.le
  rw [show v * (v⁻¹ / exp 1) = 1 / exp 1 by rw [mul_div_assoc', mul_inv_cancel₀ h0.ne']] at h3
  have h4 : 1 / exp 1 ≤ 3679 / 10000 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith

/-- `|J₁(x)| ≤ 0.51 x` for `0 ≤ x ≤ 1`. -/
theorem J1_le_small (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1) : |J1 v| ≤ 51 / 100 * v := by
  obtain ⟨k0, -⟩ := checks_A1
  have hs := (series_close1 v (by rw [abs_of_nonneg h0]; linarith)).1
  obtain ⟨z1, z2⟩ := zeta_mono (le_refl 0) h0 h1
  have rr := range_of_check _ _ _ _ _ _ k0 _ (by push_cast; linarith) (by push_cast; linarith) _ hs
  push_cast at rr
  have e : (1 : ℝ) / 2 ^ 99 ≤ 1 / 10 ^ 20 := by norm_num
  have hA : |psum a1 (v ^ 2 / 4)| ≤ 102 / 100 := by
    rw [abs_le]; constructor <;> linarith [rr.1, rr.2]
  have hJ : J1 v = v / 2 * psum a1 (v ^ 2 / 4) := rfl
  rw [hJ, abs_mul, abs_of_nonneg (by positivity : 0 ≤ v / 2)]
  nlinarith

/-- `J₁ ≤ (b/2)(c + r + 2^-99)` and `J₁ ≥ 0` on `[a, b] ⊂ [0, 2]` from a check of `A₁` on `[a²/4, b²/4]`. -/
theorem J1_upper (v a b : ℝ) (c lo hi r : ℚ) (d : ℕ)
    (h : check (subP (a1List 18) [c]) lo hi r d = true) (ha0 : 0 ≤ a) (hav : a ≤ v) (hvb : v ≤ b)
    (hb2 : b ≤ 2) (hlo : (lo : ℝ) ≤ a ^ 2 / 4) (hhi : b ^ 2 / 4 ≤ (hi : ℝ)) (Jm : ℝ)
    (hJm : b / 2 * ((c : ℝ) + r + 1 / 2 ^ 99) ≤ Jm) (hpos : 0 ≤ (c : ℝ) - r - 1 / 2 ^ 99) :
    |J1 v| ≤ Jm ∧ 0 ≤ J1 v := by
  have hs := (series_close1 v (by rw [abs_of_nonneg (by linarith)]; linarith)).1
  obtain ⟨z1, z2⟩ := zeta_mono ha0 hav hvb
  have rr := range_of_check _ _ _ _ _ _ h _ (by linarith) (by linarith) _ hs
  have hJ : J1 v = v / 2 * psum a1 (v ^ 2 / 4) := rfl
  have hA0 : 0 ≤ psum a1 (v ^ 2 / 4) := by linarith [rr.1]
  have hJ0 : 0 ≤ J1 v := by rw [hJ]; exact mul_nonneg (by linarith) hA0
  refine ⟨?_, hJ0⟩
  rw [abs_of_nonneg hJ0, hJ]
  have : v / 2 * psum a1 (v ^ 2 / 4) ≤ b / 2 * ((c : ℝ) + r + 1 / 2 ^ 99) :=
    mul_le_mul (by linarith) rr.2 hA0 (by linarith)
  linarith

/-- `0 ≤ ln v ≤ ln 2 - (1 - b/2)` for `1 ≤ v ≤ b`. -/
theorem log_upper (v b : ℝ) (h1 : 1 ≤ v) (hb : v ≤ b) :
    0 ≤ Real.log v ∧ Real.log v ≤ 6931471808 / 10 ^ 10 - (1 - b / 2) := by
  have hl := Real.log_two_lt_d9
  refine ⟨Real.log_nonneg h1, ?_⟩
  have h2 := Real.log_le_log (by linarith) hb
  have h3 := Real.log_le_sub_one_of_pos (show 0 < b / 2 by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at h3
  linarith

/-- `Y₁(x)` within `300 x` of `-2/(π x)` for `0 < x ≤ 2^-53` with `|ln x| ≤ 745`. -/
theorem tiny_close (v : ℝ) (h0 : 0 < v) (h1 : v ≤ 1 / 2 ^ 53) (hl : |Real.log v| ≤ 745) :
    |Y1 v - -(2 / (π * v))| ≤ 300 * v := by
  have hJ := J1_le_small v h0.le (by norm_num at h1 ⊢; linarith)
  have hz0 : 0 ≤ v ^ 2 / 4 := by positivity
  have hz1 : v ^ 2 / 4 ≤ 1 := by nlinarith
  have hC := psum_c1_bound _ hz0 hz1
  have hg := gamma_sub_log_two.2
  have hg0 := gamma_ge
  simp only [ghi] at hg
  push_cast at hg
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hlog : |Real.log (v / 2) + eulerMascheroniConstant| ≤ 747 := by
    rw [Real.log_div h0.ne' two_ne_zero]
    rw [abs_le] at hl ⊢
    constructor <;> linarith
  have hp := tpi_le
  have hpi := Real.pi_gt_three
  have e : Y1 v - -(2 / (π * v)) =
      2 / π * (Real.log (v / 2) + eulerMascheroniConstant) * J1 v -
        v / (2 * π) * psum c1 (v ^ 2 / 4) := by
    unfold Y1; ring
  rw [e]
  have t1 : |2 / π * (Real.log (v / 2) + eulerMascheroniConstant) * J1 v| ≤
      6367 / 10000 * 747 * (51 / 100 * v) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hp hlog (abs_nonneg _) (by norm_num)) hJ (abs_nonneg _)
      (by positivity)
  have t2 : |v / (2 * π) * psum c1 (v ^ 2 / 4)| ≤ v / 6 * (7 / 2) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    apply mul_le_mul _ hC (abs_nonneg _) (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have := abs_sub (2 / π * (Real.log (v / 2) + eulerMascheroniConstant) * J1 v)
    (v / (2 * π) * psum c1 (v ^ 2 / 4))
  linarith

/-- The bound of `j1` on the ranges of `[1, 7/4]`. -/
theorem j1Err_at (v : ℝ) (h1 : 1 < v) :
    (v ≤ 5 / 4 → j1Err v ≤ 87 / 50 * 𝐮) ∧ (v ≤ 3 / 2 → j1Err v ≤ 113 / 50 * 𝐮) ∧
      (v ≤ 7 / 4 → j1Err v ≤ 149 / 50 * 𝐮) := by
  have hu0 : (0 : ℝ) ≤ 𝐮 := by unfold unitRoundoff64; positivity
  unfold j1Err
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> split_ifs <;> linarith

theorem J1_nonneg (v : ℝ) (h1 : 1 ≤ v) (h2 : v ≤ 2) : 0 ≤ J1 v :=
  le_trans (by have := J1lo_ge v; linarith) (J1lo_le v h1 h2)

/-- A result within `E` of `x U(z)/V(z) + (2/π)(J₁ ln x - 1/x)` lies within
`E + x (0.155 u + 2^-60)` of `Y₁`. -/
theorem main_close {T : Float} {v E : ℝ} (hv0 : 0 < v) (hv2 : v ≤ 2)
    (h : FApprox T (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) +
      2 / π * (J1 v * Real.log v - 1 / v)) E) :
    Finite T.toBits ∧ |value T.toBits - Y1 v| ≤ E + v * (155 / 1000 * 𝐮 + 1 / 2 ^ 60) := by
  refine ⟨h.1, ?_⟩
  have h1 := h.2
  have h2 := y1_approx v hv0 hv2
  have h3 := abs_sub_le (value T.toBits)
    (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v)) (Y1 v)
  have h4 : |v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v) - Y1 v| =
      |Y1 v - 2 / π * (Real.log v * J1 v - 1 / v) - v * (eval U1 (v ^ 2) / eval V1 (v ^ 2))| := by
    rw [abs_sub_comm]; congr 1; ring
  linarith

/-- `y1` for `2^-1022 ≤ x < 2`. -/
theorem y1_small (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (hnorm : 0x0010000000000000 ≤ x.toBits.toNat) (h2 : x.toBits.toNat < 0x4000000000000000) :
    |value (Bessel.y1 x).toBits - Y1 (value x.toBits)| ≤
      12 * 𝐮 * √(J1 (value x.toBits) ^ 2 + Y1 (value x.toBits) ^ 2) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  have hN : x.toBits.toNat % 2 ^ 63 = x.toBits.toNat := Nat.mod_eq_of_lt hpos
  have hixN := TrigSinCos.high_word x.toBits
  set v := value x.toBits with hvdef
  have hvn : 1 / 2 ^ 1022 ≤ v := by
    have h := (F64PositiveOrder.value_le_iff (left := (0x0010000000000000 : UInt64))
      (right := x.toBits) (by decide) hpos).mpr (by simp only [UInt64.reduceToNat]; omega)
    have e : value (0x0010000000000000 : UInt64) = 1 / 2 ^ 1022 := by
      rw [← ratOfWord_cast]
      have : ratOfWord 0x0010000000000000 = 1 / 2 ^ 1022 := by decide +kernel
      rw [this]; norm_num
    rwa [e] at h
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hvn
  have hv2 : v < 2 := by
    have h := F64PositiveOrder.value_strict (left := x.toBits)
      (right := (0x4000000000000000 : UInt64)) (by decide) h2
    rwa [value_two] at h
  have hmin := value_ge_min x.toBits hpos hv0
  have hj1 := j1_small x hxf (by rw [hN]; exact h2)
  rw [abs_of_pos hv0] at hj1
  unfold Bessel.y1 Bessel.y1With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_right (show ¬ (x.toBits <<< 1 == 0) = true by
      rw [BesselSpecial.double_zero, decide_eq_true_iff]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 63 == 1) = true by
      rw [BesselSpecial.sign_bit, decide_eq_true_iff]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 1073741824) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  by_cases ht : x.toBits >>> 32 &&& 2147483647 ≤ 1016070144
  · rw [ite_eq_left ht]
    have hsmall : v < 1 / 2 ^ 53 := by
      have h := F64PositiveOrder.value_strict (left := x.toBits)
        (right := (0x3CA0000000000000 : UInt64)) (by decide) (by
          have := UInt64.le_iff_toNat_le.mp ht
          rw [hixN] at this
          simp only [UInt64.reduceToNat] at this
          simp only [UInt64.reduceToNat]
          omega)
      have e : value (0x3CA0000000000000 : UInt64) = 1 / 2 ^ 53 := by
        rw [← ratOfWord_cast]
        have : ratOfWord 0x3CA0000000000000 = 1 / 2 ^ 53 := by decide +kernel
        rw [this]; norm_num
      rwa [e] at h
    obtain ⟨hlabs, -, hl2⟩ := log_facts v hmin (by norm_num at hsmall ⊢; linarith)
    have hx := fapprox_exact x hxf
    have hneg := fapprox_neg tpi_near
    have hy : (2 : ℝ) ^ 53 ≤ 1 / v := by
      rw [le_div_iff₀ hv0]; norm_num at hsmall ⊢; nlinarith
    have hq := fapprox_div hneg hx (6367 / 10000) v (by rw [abs_neg]; exact tpi_le)
      (le_of_eq (abs_of_pos hv0).symm) hv0 _ le_rfl (by
        rw [div_lt_iff₀ (by linarith)]
        have : (1 : ℝ) ≤ 2 ^ 1022 * v := by
          have h := mul_le_mul_of_nonneg_left hvn (show (0 : ℝ) ≤ 2 ^ 1022 by positivity)
          rwa [mul_one_div_cancel (by positivity)] at h
        rw [sub_zero, hu]; linarith)
    have hq' : FApprox (-Bessel.tpi / x) (-(2 / π) / v) (1 * 𝐮 * (1 / v)) := by
      refine fmono hq ?_
      calc _ = (36 / 100 * 𝐮 + (6367 / 10000 + 36 / 100 * 𝐮) / 2 ^ 53) * (1 / v) +
            1 / 2 ^ 1075 := by ring
        _ ≤ 1 * 𝐮 * (1 / v) := by rw [hu]; nlinarith
    have hcl := tiny_close v hv0 hsmall.le (by rw [hlabs]; exact hl2)
    have hM := modulus1_small v hv0 (by norm_num at hsmall ⊢; linarith)
    have hp := two_div_pi_ge
    have e2 : -(2 / π) / v = -(2 / (π * v)) := by ring
    rw [e2] at hq'
    have h3 := abs_sub_le (value (-Bessel.tpi / x).toBits) (-(2 / (π * v))) (Y1 v)
    rw [abs_sub_comm (-(2 / (π * v)))] at h3
    have h4 := hq'.2
    have hM' : 2 / (π * v) = 2 / π * (1 / v) := by ring
    rw [hM'] at hM
    have hM2 : 6366 / 10000 * (1 / v) ≤ √(J1 v ^ 2 + Y1 v ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_right hp (by positivity)) hM
    have h5 : 1 * 𝐮 * (1 / v) + 300 * v ≤ 12 * 𝐮 * (6366 / 10000 * (1 / v)) := by
      rw [hu]; nlinarith
    have h6 : 12 * 𝐮 * (6366 / 10000 * (1 / v)) ≤ 12 * 𝐮 * √(J1 v ^ 2 + Y1 v ^ 2) :=
      mul_le_mul_of_nonneg_left hM2 (by positivity)
    linarith
  · rw [ite_eq_right ht]
    have hn : ¬ (x.toBits >>> 32 &&& 2147483647).toNat ≤ (1016070144 : UInt64).toNat :=
      fun h => ht (UInt64.le_iff_toNat_le.mpr h)
    rw [hixN] at hn
    simp only [UInt64.reduceToNat] at hn
    have ha : 1 / 18014398509481984 ≤ v := by
      have h := (F64PositiveOrder.value_le_iff (left := (0x3C90000000000000 : UInt64))
        (right := x.toBits) (by decide) hpos).mpr (by simp only [UInt64.reduceToNat]; omega)
      have e : value (0x3C90000000000000 : UInt64) = 1 / 18014398509481984 := by
        rw [← ratOfWord_cast]
        have : ratOfWord 0x3C90000000000000 = 1 / 18014398509481984 := by decide +kernel
        rw [this]; norm_num
      rwa [e] at h
    have hL := log_near x hxf hv0
    rw [(code_eq (x * x)).1, (code_eq (x * x)).2]
    show |value (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) +
        Bessel.tpi * (Bessel.j1 x * Log.log x - 1.0 / x)).toBits - Y1 v| ≤ _
    rcases le_or_gt v 1 with c0 | c0
    · have hlv : Real.log v ≤ 0 := Real.log_nonpos hv0.le c0
      have hlabs : |Real.log v| = -Real.log v := abs_of_nonpos hlv
      have hvl := xlog_le v hv0
      have hL' : FApprox (Log.log x) (Real.log v) (6 / 5 * 𝐮 * -Real.log v + 1 / 2 ^ 59) := by
        have e : logErr (Real.log v) = 6 / 5 * 𝐮 * -Real.log v + 1 / 2 ^ 59 := by
          unfold logErr; rw [hlabs]
        rw [e] at hL
        exact hL
      have hJ : FApprox (Bessel.j1 x) (J1 v) (14 / 10 * 𝐮) := by
        refine ⟨hj1.1, hj1.2.trans (le_of_eq ?_)⟩
        unfold j1Err; rw [ite_eq_left c0]
      have hl38 : -Real.log v ≤ 38 := by
        have hb := Real.log_le_log (by positivity) ha
        rw [show (1 / 18014398509481984 : ℝ) = (2 ^ 54)⁻¹ by norm_num, Real.log_inv,
          Real.log_pow] at hb
        have := Real.log_two_lt_d9
        push_cast at hb
        linarith
      have hp := small_piece x (Bessel.j1 x) (Log.log x) hxf v rfl ha c0 _ hlabs hl38 hvl hJ
        (J1_le_small v hv0.le c0) hL'
      have hcl := (main_close hv0 hv2.le hp).2
      have hM := modulus1_small v hv0 c0
      have hpi := two_div_pi_ge
      have hM' : 2 / (π * v) = 2 / π * (1 / v) := by ring
      rw [hM'] at hM
      have hM2 : 6366 / 10000 * (1 / v) ≤ √(J1 v ^ 2 + Y1 v ^ 2) :=
        le_trans (mul_le_mul_of_nonneg_right hpi (by positivity)) hM
      have hy1 : 1 ≤ 1 / v := by rw [le_div_iff₀ hv0]; linarith
      have hlv' : -Real.log v ≤ 3679 / 10000 * (1 / v) := by
        rw [mul_one_div, le_div_iff₀ hv0]; linarith
      have h5 : 2909 / 1000 * 𝐮 * (1 / v) + 447 / 500 * 𝐮 * -Real.log v + 2581 / 1000 * 𝐮 +
          v * (155 / 1000 * 𝐮 + 1 / 2 ^ 60) ≤ 12 * 𝐮 * (6366 / 10000 * (1 / v)) := by
        rw [hu]; nlinarith
      have h6 : 12 * 𝐮 * (6366 / 10000 * (1 / v)) ≤ 12 * 𝐮 * √(J1 v ^ 2 + Y1 v ^ 2) :=
        mul_le_mul_of_nonneg_left hM2 (by positivity)
      linarith
    · obtain ⟨-, k1, k2, k3, k4, k5, k6, k7⟩ := checks_A1
      have e1 : (1 : ℝ) / 2 ^ 99 ≤ 1 / 10 ^ 20 := by norm_num
      have hJ0 := J1_nonneg v c0.le hv2.le
      have hJe : ∀ e : ℝ, j1Err v ≤ e → FApprox (Bessel.j1 x) (J1 v) e :=
        fun e he => ⟨hj1.1, hj1.2.trans he⟩
      have hLe : ∀ Lm : ℝ, |Real.log v| ≤ Lm → ∀ c : ℝ, 6 / 5 * Lm ≤ c →
          FApprox (Log.log x) (Real.log v) (c * 𝐮 + 1 / 2 ^ 59) := by
        intro Lm hLm c hc
        refine fmono hL ?_
        unfold logErr
        have h1 := mul_le_mul_of_nonneg_left hLm (show (0 : ℝ) ≤ 6 / 5 * 𝐮 by positivity)
        have h2 := mul_le_mul_of_nonneg_right hc hu0
        linarith
      have hj := j1Err_at v c0
      have fin : ∀ (E L : ℝ), 0 ≤ L → E + 2 * (155 / 1000 * 𝐮 + 1 / 2 ^ 60) ≤ 12 * 𝐮 * L →
          L ≤ J1 v →
          FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
            hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) +
            Bessel.tpi * (Bessel.j1 x * Log.log x - 1.0 / x))
            (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v)) E →
          |value (x * (hornerF (u1w.map Float.ofBits) (x * x) /
            hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) +
            Bessel.tpi * (Bessel.j1 x * Log.log x - 1.0 / x)).toBits - Y1 v| ≤
            12 * 𝐮 * √(J1 v ^ 2 + Y1 v ^ 2) := by
        intro E L hL1 hE hL0 hp
        have hcl := (main_close hv0 hv2.le hp).2
        have hk : v * (155 / 1000 * 𝐮 + 1 / 2 ^ 60) ≤ 2 * (155 / 1000 * 𝐮 + 1 / 2 ^ 60) :=
          mul_le_mul_of_nonneg_right hv2.le (by positivity)
        have hM : L ≤ √(J1 v ^ 2 + Y1 v ^ 2) := mod_ge_J hL1 hL0
        have := mul_le_mul_of_nonneg_left hM (show (0 : ℝ) ≤ 12 * 𝐮 by positivity)
        linarith
      rcases le_or_gt v (9 / 8) with c1 | c1
      · have hlu := log_upper v (9 / 8) c0.le c1
        have hLm : |Real.log v| ≤ 1 / 8 := by
          rw [abs_of_nonneg hlu.1]; have := Real.log_le_sub_one_of_pos hv0; linarith
        exact fin _ _ (by norm_num) (by rw [hu]; norm_num)
          (J1_piece v 1 (9 / 8) _ _ _ _ _ k1 (by norm_num) c0.le c1 (by norm_num) (by norm_num)
            (by norm_num) (4249 / 10000) (by push_cast; linarith) (by push_cast; linarith))
          (piece_0 x _ _ hxf v rfl c0.le c1 (hJe _ (hj.1 (by linarith)))
            (J1_upper v 1 (9 / 8) _ _ _ _ _ k1 (by norm_num) c0.le c1 (by norm_num) (by norm_num)
              (by norm_num) (619 / 1250) (by push_cast; linarith) (by push_cast; linarith)).1
            (hLe _ hLm _ (by norm_num)) hLm (mul_nonneg hJ0 hlu.1))
      rcases le_or_gt v (5 / 4) with c2 | c2
      · have hlu := log_upper v (5 / 4) c0.le c2
        have hLm : |Real.log v| ≤ 1 / 4 := by
          rw [abs_of_nonneg hlu.1]; have := Real.log_le_sub_one_of_pos hv0; linarith
        exact fin _ _ (by norm_num) (by rw [hu]; norm_num)
          (J1_piece v (9 / 8) (5 / 4) _ _ _ _ _ k2 (by norm_num) c1.le c2 (by norm_num)
            (by norm_num) (by norm_num) (919 / 2000) (by push_cast; linarith)
            (by push_cast; linarith))
          (piece_1 x _ _ hxf v rfl c1.le c2 (hJe _ (hj.1 c2))
            (J1_upper v (9 / 8) (5 / 4) _ _ _ _ _ k2 (by norm_num) c1.le c2 (by norm_num)
              (by norm_num) (by norm_num) (5313 / 10000) (by push_cast; linarith)
              (by push_cast; linarith)).1
            (hLe _ hLm _ (by norm_num)) hLm (mul_nonneg hJ0 hlu.1))
      rcases le_or_gt v (3 / 2) with c3 | c3
      · have hlu := log_upper v (3 / 2) c0.le c3
        have hLm : |Real.log v| ≤ 277 / 625 := by
          rw [abs_of_nonneg hlu.1]; linarith [hlu.2]
        exact fin _ _ (by norm_num) (by rw [hu]; norm_num)
          (J1_piece v (5 / 4) (3 / 2) _ _ _ _ _ k3 (by norm_num) c2.le c3 (by norm_num)
            (by norm_num) (by norm_num) (581 / 1250) (by push_cast; linarith)
            (by push_cast; linarith))
          (piece_2 x _ _ hxf v rfl c2.le c3 (hJe _ (hj.2.1 c3))
            (J1_upper v (5 / 4) (3 / 2) _ _ _ _ _ k3 (by norm_num) c2.le c3 (by norm_num)
              (by norm_num) (by norm_num) (6129 / 10000) (by push_cast; linarith)
              (by push_cast; linarith)).1
            (hLe _ hLm _ (by norm_num)) hLm (mul_nonneg hJ0 hlu.1))
      rcases le_or_gt v (7 / 4) with c4 | c4
      · have hlu := log_upper v (7 / 4) c0.le c4
        have hLm : |Real.log v| ≤ 2841 / 5000 := by
          rw [abs_of_nonneg hlu.1]; linarith [hlu.2]
        exact fin _ _ (by norm_num) (by rw [hu]; norm_num)
          (J1_piece v (3 / 2) (7 / 4) _ _ _ _ _ k4 (by norm_num) c3.le c4 (by norm_num)
            (by norm_num) (by norm_num) (1243 / 2500) (by push_cast; linarith)
            (by push_cast; linarith))
          (piece_3 x _ _ hxf v rfl c3.le c4 (hJe _ (hj.2.2 c4))
            (J1_upper v (3 / 2) (7 / 4) _ _ _ _ _ k4 (by norm_num) c3.le c4 (by norm_num)
              (by norm_num) (by norm_num) (6511 / 10000) (by push_cast; linarith)
              (by push_cast; linarith)).1
            (hLe _ hLm _ (by norm_num)) hLm (mul_nonneg hJ0 hlu.1))
      have hj7 : j1Err v ≤ 389 / 100 * 𝐮 := j1Err_le v
      rcases le_or_gt v (15 / 8) with c5 | c5
      · have hlu := log_upper v (15 / 8) c0.le c5
        have hLm : |Real.log v| ≤ 6307 / 10000 := by
          rw [abs_of_nonneg hlu.1]; linarith [hlu.2]
        exact fin _ _ (by norm_num) (by rw [hu]; norm_num)
          (J1_piece v (7 / 4) (15 / 8) _ _ _ _ _ k5 (by norm_num) c4.le c5 (by norm_num)
            (by norm_num) (by norm_num) (5427 / 10000) (by push_cast; linarith)
            (by push_cast; linarith))
          (piece_4 x _ _ hxf v rfl c4.le c5 (hJe _ hj7)
            (J1_upper v (7 / 4) (15 / 8) _ _ _ _ _ k5 (by norm_num) c4.le c5 (by norm_num)
              (by norm_num) (by norm_num) (6217 / 10000) (by push_cast; linarith)
              (by push_cast; linarith)).1
            (hLe _ hLm _ (by norm_num)) hLm (mul_nonneg hJ0 hlu.1))
      rcases le_or_gt v (31 / 16) with c6 | c6
      · have hlu := log_upper v (31 / 16) c0.le c6
        have hLm : |Real.log v| ≤ 331 / 500 := by
          rw [abs_of_nonneg hlu.1]; linarith [hlu.2]
        exact fin _ _ (by norm_num) (by rw [hu]; norm_num)
          (J1_piece v (15 / 8) (31 / 16) _ _ _ _ _ k6 (by norm_num) c5.le c6 (by norm_num)
            (by norm_num) (by norm_num) (5611 / 10000) (by push_cast; linarith)
            (by push_cast; linarith))
          (piece_5 x _ _ hxf v rfl c5.le c6 (hJe _ hj7)
            (J1_upper v (15 / 8) (31 / 16) _ _ _ _ _ k6 (by norm_num) c5.le c6 (by norm_num)
              (by norm_num) (by norm_num) (1503 / 2500) (by push_cast; linarith)
              (by push_cast; linarith)).1
            (hLe _ hLm _ (by norm_num)) hLm (mul_nonneg hJ0 hlu.1))
      have hlu := log_upper v 2 c0.le hv2.le
      have hLm : |Real.log v| ≤ 1733 / 2500 := by
        rw [abs_of_nonneg hlu.1]; linarith [hlu.2]
      exact fin _ _ (by norm_num) (by rw [hu]; norm_num)
        (J1_piece v (31 / 16) 2 _ _ _ _ _ k7 (by norm_num) c6.le hv2.le (by norm_num)
          (by norm_num) (by norm_num) (2793 / 5000) (by push_cast; linarith)
          (by push_cast; linarith))
        (piece_6 x _ _ hxf v rfl c6.le hv2.le (hJe _ hj7)
          (J1_upper v (31 / 16) 2 _ _ _ _ _ k7 (by norm_num) c6.le hv2.le (by norm_num)
            (by norm_num) (by norm_num) (1497 / 2500) (by push_cast; linarith)
            (by push_cast; linarith)).1
          (hLe _ hLm _ (by norm_num)) hLm (mul_nonneg hJ0 hlu.1))

#print axioms xlog_le
#print axioms j1Err_at
#print axioms J1_le_small
#print axioms tiny_close
#print axioms main_close
#print axioms y1_small

end Verified.Examples.BesselY1Small
