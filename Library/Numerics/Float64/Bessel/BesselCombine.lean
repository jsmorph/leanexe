import Library.Numerics.Float64.Bessel.BesselPQRange
import LeanExe.ProofKit.BesselPQ

/-!
The last steps of `j0`, `y0`, `j1`, and `y1` from 2 on: `invsqrtpi · (P̂ ĉc ∓ Q̂ ŝs) / √x` and
`invsqrtpi · (P̂ ŝs + Q̂ ĉc) / √x`.  `invsqrtpi_near` and `tpi_near` place fdlibm's constants within
`0.07 u` of `1/√π` and `0.36 u` of `2/π`, with `u = 2 ^ -53`, from Mathlib's 20-digit bounds on `π`.
`combine_sub` and `combine_add` bound the bracket from the errors and magnitudes of its four
factors, with `mulErr` the error form of `F64Approx.fapprox_mul` and a rounding of at most `u`
below 2.  `final_step` bounds the product with `invsqrtpi` and the quotient by the rounded `√x`,
and gives the error `finErr eT MT / √x + 2 ^ -1075`.  `J0_form` and its three companions rewrite
the large-argument forms of `BesselPQ` with `A = sin x ± cos x` and `B`, and `modulus_lower`
bounds the modulus below by `0.7978 Pl / √x` when `P ≥ Pl > 0`.
-/

namespace Library.Numerics.Float64.Bessel.BesselCombine
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64HalfUlp BesselPQEval BesselPQRange BesselCS
  BesselPQ PolyBound Real
open LeanExe.ProofKit.Bessel (J0 J1 Y0 Y1)

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The error form of `fapprox_mul`. -/
noncomputable def mulErr (ea eb Ma Mb : ℝ) : ℝ :=
  ea * Mb + Ma * eb + ea * eb + (Ma + ea) * (Mb + eb) / 2 ^ 53 + 1 / 2 ^ 1075

/-- A bound on `1/√π`, and the error of `invsqrtpi`. -/
noncomputable def Mis : ℝ := 5642 / 10000
noncomputable def eis : ℝ := 7 / 100 * 𝐮

/-- The error of `invsqrtpi · t / √x`, times `√x`. -/
noncomputable def finErr (eT MT : ℝ) : ℝ :=
  ((mulErr eis eT Mis MT + Mis * MT * 𝐮) + (Mis * MT + mulErr eis eT Mis MT) * 𝐮) / (1 - 𝐮)

theorem pi_bounds : (3.14159265358979323846 : ℝ) < π ∧ π < 3.14159265358979323847 :=
  ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩

theorem invsqrtpi_near : FApprox Bessel.invsqrtpi (1 / √π) eis := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hn : Wasm.IEEE64.isNaN 0x3FE20DD750429B6D = false := by decide
  unfold FApprox Approx Bessel.invsqrtpi
  rw [F64Bits.toBits_ofBits, hn]
  simp only [Bool.false_eq_true, ite_false]
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
  rw [← ratOfWord_cast]
  have hw : ratOfWord 0x3FE20DD750429B6D = 5081767996463981 / 2 ^ 53 := by decide +kernel
  rw [hw]
  obtain ⟨hp1, hp2⟩ := pi_bounds
  have hs0 : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hss : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  set s := √π
  have hlow : (5081767996463981 / 2 ^ 53 : ℝ) - 7 / 100 * (1 / 2 ^ 53) ≤ 1 / s := by
    rw [le_div_iff₀ hs0]
    by_contra hc
    push Not at hc
    have h0 : (0 : ℝ) ≤ 1 := by norm_num
    have hy : 1 < (((5081767996463981 / 2 ^ 53 : ℝ) - 7 / 100 * (1 / 2 ^ 53)) * s) ^ 2 := by
      nlinarith
    rw [mul_pow, hss] at hy
    linarith
  have hup : 1 / s ≤ (5081767996463981 / 2 ^ 53 : ℝ) + 7 / 100 * (1 / 2 ^ 53) := by
    rw [div_le_iff₀ hs0]
    by_contra hc
    push Not at hc
    have h0 : (0 : ℝ) ≤ ((5081767996463981 / 2 ^ 53 : ℝ) + 7 / 100 * (1 / 2 ^ 53)) * s := by
      positivity
    have hy : (((5081767996463981 / 2 ^ 53 : ℝ) + 7 / 100 * (1 / 2 ^ 53)) * s) ^ 2 < 1 := by
      nlinarith
    rw [mul_pow, hss] at hy
    linarith
  unfold eis
  rw [hu, abs_le]
  push_cast
  constructor <;> linarith

theorem tpi_near : FApprox Bessel.tpi (2 / π) (36 / 100 * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hn : Wasm.IEEE64.isNaN 0x3FE45F306DC9C883 = false := by decide
  unfold FApprox Approx Bessel.tpi
  rw [F64Bits.toBits_ofBits, hn]
  simp only [Bool.false_eq_true, ite_false]
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
  rw [← ratOfWord_cast]
  have hw : ratOfWord 0x3FE45F306DC9C883 = 5734161139222659 / 2 ^ 53 := by decide +kernel
  rw [hw]
  obtain ⟨hp1, hp2⟩ := pi_bounds
  have hp0 := Real.pi_pos
  have hlow : (5734161139222659 / 2 ^ 53 : ℝ) - 36 / 100 * (1 / 2 ^ 53) ≤ 2 / π := by
    rw [le_div_iff₀ hp0]
    nlinarith
  have hup : 2 / π ≤ (5734161139222659 / 2 ^ 53 : ℝ) + 36 / 100 * (1 / 2 ^ 53) := by
    rw [div_le_iff₀ hp0]
    nlinarith
  rw [hu, abs_le]
  push_cast
  constructor <;> linarith

theorem one_div_sqrt_pi_le : |1 / √π| ≤ Mis := by
  have hs0 : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hss : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  unfold Mis
  rw [abs_of_pos (by positivity), div_le_iff₀ hs0]
  by_contra hc
  push Not at hc
  have h0 : (0 : ℝ) ≤ 5642 / 10000 * √π := by positivity
  have hy : (5642 / 10000 * √π) ^ 2 < 1 := by nlinarith
  rw [mul_pow, hss] at hy
  have := Real.pi_gt_d20
  linarith

/-- The bracket `P A - Q B` from its rounded factors. -/
theorem combine_sub {p q c s : Float} {P Q A B eP eQ eA eB Pm Qm Am Bm : ℝ}
    (hp : FApprox p P eP) (hq : FApprox q Q eQ) (hc : FApprox c A eA) (hs : FApprox s B eB)
    (hPm : |P| ≤ Pm) (hQm : |Q| ≤ Qm) (hAm : |A| ≤ Am) (hBm : |B| ≤ Bm)
    (h1 : (Pm + eP) * (Am + eA) < 2 ^ 1022) (h2 : (Qm + eQ) * (Bm + eB) < 2 ^ 1022)
    (hlt : Pm * Am + Qm * Bm + (mulErr eP eA Pm Am + mulErr eQ eB Qm Bm) < 2) :
    FApprox (p * c - q * s) (P * A - Q * B) (mulErr eP eA Pm Am + mulErr eQ eB Qm Bm + 𝐮) := by
  have m1 := fapprox_mul hp hc Pm Am hPm hAm _ le_rfl h1
  have m2 := fapprox_mul hq hs Qm Bm hQm hBm _ le_rfl h2
  have hT : |P * A - Q * B| ≤ Pm * Am + Qm * Bm := by
    have := abs_sub (P * A) (Q * B)
    rw [abs_mul, abs_mul] at this
    have e1 := mul_le_mul hPm hAm (abs_nonneg _) ((abs_nonneg _).trans hPm)
    have e2 := mul_le_mul hQm hBm (abs_nonneg _) ((abs_nonneg _).trans hQm)
    linarith
  have h := fapprox_sub_half m1 m2 1022 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
    rw [e]
    unfold mulErr at hlt
    linarith)
  refine fmono h (le_of_eq ?_)
  unfold mulErr
  norm_num [unitRoundoff64]

/-- The bracket `P B + Q A` from its rounded factors. -/
theorem combine_add {p q c s : Float} {P Q A B eP eQ eA eB Pm Qm Am Bm : ℝ}
    (hp : FApprox p P eP) (hq : FApprox q Q eQ) (hc : FApprox c A eA) (hs : FApprox s B eB)
    (hPm : |P| ≤ Pm) (hQm : |Q| ≤ Qm) (hAm : |A| ≤ Am) (hBm : |B| ≤ Bm)
    (h1 : (Pm + eP) * (Bm + eB) < 2 ^ 1022) (h2 : (Qm + eQ) * (Am + eA) < 2 ^ 1022)
    (hlt : Pm * Bm + Qm * Am + (mulErr eP eB Pm Bm + mulErr eQ eA Qm Am) < 2) :
    FApprox (p * s + q * c) (P * B + Q * A) (mulErr eP eB Pm Bm + mulErr eQ eA Qm Am + 𝐮) := by
  have m1 := fapprox_mul hp hs Pm Bm hPm hBm _ le_rfl h1
  have m2 := fapprox_mul hq hc Qm Am hQm hAm _ le_rfl h2
  have hT : |P * B + Q * A| ≤ Pm * Bm + Qm * Am := by
    have := abs_add_le (P * B) (Q * A)
    rw [abs_mul, abs_mul] at this
    have e1 := mul_le_mul hPm hBm (abs_nonneg _) ((abs_nonneg _).trans hPm)
    have e2 := mul_le_mul hQm hAm (abs_nonneg _) ((abs_nonneg _).trans hQm)
    linarith
  have h := fapprox_add_half m1 m2 1022 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
    rw [e]
    unfold mulErr at hlt
    linarith)
  refine fmono h (le_of_eq ?_)
  unfold mulErr
  norm_num [unitRoundoff64]

/-- `invsqrtpi · t / √x` for `x ≥ 2`. -/
theorem final_step {t x : Float} {T eT MT : ℝ} (ht : FApprox t T eT) (hMT : |T| ≤ MT)
    (hsm : MT + eT ≤ 4) (hxf : Finite x.toBits) (hx2 : 2 ≤ value x.toBits) :
    FApprox (Bessel.invsqrtpi * t / x.sqrt) (T / √(π * value x.toBits))
      (finErr eT MT / √(value x.toBits) + 1 / 2 ^ 1075) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  set v := value x.toBits with hv
  have hv0 : 0 < v := by linarith
  have heT : 0 ≤ eT := (abs_nonneg _).trans ht.2
  have hMT0 : 0 ≤ MT := (abs_nonneg _).trans hMT
  have heis : 0 ≤ eis := by unfold eis; rw [hu]; norm_num
  have hF1 := fapprox_mul invsqrtpi_near ht Mis MT one_div_sqrt_pi_le hMT _ le_rfl (by
    unfold Mis eis; rw [hu]; nlinarith)
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv0
  have hF2 := fapprox_sqrt (fapprox_exact x hxf) v v hv0 le_rfl hv0 le_rfl (√v)
    (by rw [add_zero])
  simp only [zero_div, zero_add] at hF2
  have hval : |1 / √π * T| ≤ Mis * MT := by
    rw [abs_mul]
    exact mul_le_mul one_div_sqrt_pi_le hMT (abs_nonneg _) (by unfold Mis; norm_num)
  have he2 : √v / 2 ^ 53 < √v := by
    have : √v / 2 ^ 53 < √v / 1 := div_lt_div_of_pos_left hsv (by norm_num) (by norm_num)
    rwa [div_one] at this
  set eF := eis * MT + Mis * eT + eis * eT + (Mis + eis) * (MT + eT) / 2 ^ 53 + 1 / 2 ^ 1075
    with heF
  have heF0 : 0 ≤ eF := by rw [heF]; unfold Mis; positivity
  have hden : 0 < √v - √v / 2 ^ 53 := by linarith
  have hd := fapprox_div hF1 hF2 (Mis * MT) (√v) hval (le_of_eq (abs_of_pos hsv).symm) he2 _
    le_rfl (by
      rw [div_lt_iff₀ hden]
      have h1 : Mis * MT + eF ≤ 10 := by
        rw [heF]; unfold Mis eis; rw [hu]
        nlinarith [hsm, heT, hMT0]
      have h2 : (1 / 2 : ℝ) ≤ √v - √v / 2 ^ 53 := by
        have : (1 : ℝ) ≤ √v := by
          rw [show (1 : ℝ) = √1 by simp]
          exact Real.sqrt_le_sqrt (by linarith)
        have : √v / 2 ^ 53 ≤ √v / 2 := div_le_div_of_nonneg_left hsv.le (by norm_num) (by norm_num)
        linarith
      nlinarith [show (10 : ℝ) < 2 ^ 1022 by norm_num])
  have hT : 1 / √π * T / √v = T / √(π * v) := by
    rw [Real.sqrt_mul Real.pi_pos.le]
    field_simp
  refine fmono (fcongr hd hT) (le_of_eq ?_)
  have hsv' : √v ≠ 0 := hsv.ne'
  unfold finErr mulErr
  rw [← heF, hu]
  field_simp

/-- `J₀` in the form of the code: `(P (sin x + cos x) - Q (sin x - cos x)) / √(π x)`. -/
theorem trig_quarter (w : ℝ) : cos (w - π / 4) = (sin w + cos w) / √2 ∧
    sin (w - π / 4) = (sin w - cos w) / √2 := by
  have h2 : √2 ≠ 0 := by positivity
  have hh : √2 / 2 = 1 / √2 := by
    rw [eq_div_iff h2, div_mul_eq_mul_div, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [cos_sub, sin_sub, cos_pi_div_four, sin_pi_div_four, hh]
  constructor <;> ring

theorem trig_three_quarters (w : ℝ) : cos (w - 3 * π / 4) = (sin w - cos w) / √2 ∧
    sin (w - 3 * π / 4) = (-sin w - cos w) / √2 := by
  have h2 : √2 ≠ 0 := by positivity
  have hh : √2 / 2 = 1 / √2 := by
    rw [eq_div_iff h2, div_mul_eq_mul_div, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hc : cos (3 * π / 4) = -(√2 / 2) := by
    rw [show 3 * π / 4 = π - π / 4 by ring, cos_pi_sub, cos_pi_div_four]
  have hs : sin (3 * π / 4) = √2 / 2 := by
    rw [show 3 * π / 4 = π - π / 4 by ring, sin_pi_sub, sin_pi_div_four]
  rw [cos_sub, sin_sub, hc, hs, hh]
  constructor <;> ring

theorem scale (w : ℝ) (hw : 0 < w) : √(2 / (π * w)) * (1 / √2) = 1 / √(π * w) := by
  rw [Real.sqrt_div (by norm_num)]
  have h2 : √2 ≠ 0 := by positivity
  have h3 : √(π * w) ≠ 0 := by positivity
  field_simp

theorem J0_form (w : ℝ) (hw : 0 < w) :
    J0 w = (P0 w * (sin w + cos w) - Q0 w * (sin w - cos w)) / √(π * w) := by
  rw [J0_large w hw, (trig_quarter w).1, (trig_quarter w).2]
  have := scale w hw
  calc _ = √(2 / (π * w)) * (1 / √2) * (P0 w * (sin w + cos w) - Q0 w * (sin w - cos w)) := by ring
    _ = _ := by rw [this]; ring

theorem Y0_form (w : ℝ) (hw : 0 < w) :
    Y0 w = (P0 w * (sin w - cos w) + Q0 w * (sin w + cos w)) / √(π * w) := by
  rw [Y0_large w hw, (trig_quarter w).1, (trig_quarter w).2]
  have := scale w hw
  calc _ = √(2 / (π * w)) * (1 / √2) * (P0 w * (sin w - cos w) + Q0 w * (sin w + cos w)) := by ring
    _ = _ := by rw [this]; ring

theorem J1_form (w : ℝ) (hw : 0 < w) :
    J1 w = (P1 w * (sin w - cos w) - Q1 w * (-sin w - cos w)) / √(π * w) := by
  rw [J1_large w hw, (trig_three_quarters w).1, (trig_three_quarters w).2]
  have := scale w hw
  calc _ = √(2 / (π * w)) * (1 / √2) * (P1 w * (sin w - cos w) - Q1 w * (-sin w - cos w)) := by
        ring
    _ = _ := by rw [this]; ring

theorem Y1_form (w : ℝ) (hw : 0 < w) :
    Y1 w = (P1 w * (-sin w - cos w) + Q1 w * (sin w - cos w)) / √(π * w) := by
  rw [Y1_large w hw, (trig_three_quarters w).1, (trig_three_quarters w).2]
  have := scale w hw
  calc _ = √(2 / (π * w)) * (1 / √2) * (P1 w * (-sin w - cos w) + Q1 w * (sin w - cos w)) := by
        ring
    _ = _ := by rw [this]; ring

/-- `√(2/π) ≥ 0.7978`. -/
theorem sqrt_two_div_pi : (7978 / 10000 : ℝ) ≤ √(2 / π) := by
  rw [show (7978 / 10000 : ℝ) = √((7978 / 10000) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ Real.pi_pos]
  have := Real.pi_lt_d20
  nlinarith

/-- The modulus against `P ≥ Pl > 0`: `√(2/(π x)) √(P² + Q²) ≥ 0.7978 Pl / √x`. -/
theorem modulus_lower (w P Q Pl : ℝ) (hw : 0 < w) (hPl : 0 < Pl) (hP : Pl ≤ P) :
    7978 / 10000 * Pl / √w ≤ √(2 / (π * w) * (P ^ 2 + Q ^ 2)) := by
  have hsw : 0 < √w := Real.sqrt_pos.mpr hw
  have h1 : Pl ≤ √(P ^ 2 + Q ^ 2) := by
    rw [show Pl = √(Pl ^ 2) by rw [Real.sqrt_sq hPl.le]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 := sqrt_two_div_pi
  have e1 : √(2 / (π * w) * (P ^ 2 + Q ^ 2)) = √(2 / π) * √(P ^ 2 + Q ^ 2) / √w := by
    rw [← div_div, Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity)]
    ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ hsw.le
  calc 7978 / 10000 * Pl ≤ √(2 / π) * Pl := mul_le_mul_of_nonneg_right h2 hPl.le
    _ ≤ √(2 / π) * √(P ^ 2 + Q ^ 2) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)

#print axioms invsqrtpi_near
#print axioms tpi_near
#print axioms combine_sub
#print axioms combine_add
#print axioms final_step
#print axioms J0_form
#print axioms Y0_form
#print axioms J1_form
#print axioms Y1_form
#print axioms modulus_lower

end Library.Numerics.Float64.Bessel.BesselCombine
