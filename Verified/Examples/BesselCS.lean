import Verified.Examples.TrigNear
import Verified.Examples.Bessel
import LeanExe.ProofKit.F64HalfUlp
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64RoundFinish
import LeanExe.ProofKit.F64Exact

/-!
The pairs `(cc, ss)` of `Bessel.asym0` and `Bessel.asym1` for `x ≥ 2`, as distances from
`A = √2 cos θ` and `B = √2 sin θ`, where `θ = x - π/4` for `asym0`, so that `A = sin x + cos x` and
`B = sin x - cos x`, and `θ = x - 3π/4` for `asym1`, so that `A = sin x - cos x` and
`B = -sin x - cos x`.  In both cases `A² + B² = 2`, and `A B = -cos 2x` or `cos 2x` is the cosine
term that the code computes from `x + x`, which is exact below `2 ^ 1023` (`add_self_exact`).

`Trig.sin` and `Trig.cos` lie within `e = (71/50) u` of `sin x` and `cos x` (`TrigNear`), with
`u = 2 ^ -53`, so the direct sum or difference lies within `2e + u = (96/25) u`, the rounding
being at most `u` below 2 (`F64HalfUlp`).  The sign of the rounded product `s c` tells which of `A`
and `B` has magnitude near 1 or more: `(A B)` and `|A|, |B| ≤ √2` give
`A² - B² = ±4 sin x cos x`.  The code divides `A B` by that one, so the quotient lies within
`(627/100) u` of the other (`quot_near`), and the two branches give
`|cc - A| ≤ (96/25) u`, `|ss - B| ≤ (627/100) u`, `A² ≥ 1 - 2^-48`, `B² ≤ 1 + 2^-48`, or the same
with the roles exchanged.  From `2 ^ 1023` on, the code keeps both direct values.
-/

namespace Verified.Examples.BesselCS
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64HalfUlp TrigNear

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 1200

/-- `w + w` for a positive normal word below `2 ^ 1023`. -/
theorem add_self_word (w : UInt64) (hf : Finite w) (hs : Wasm.IEEE64.sign w = false)
    (he1 : 1 ≤ Wasm.IEEE64.exponent w) (he2 : Wasm.IEEE64.exponent w ≤ 2045) :
    Wasm.IEEE64.add w w = Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 1024 0) w := by
  have hfr : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hsm : Wasm.IEEE64.scaledMagnitude w =
      (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
    have hne : (Wasm.IEEE64.exponent w == 0) = false := by
      rw [beq_eq_false_iff_ne]; omega
    simp only [Wasm.IEEE64.scaledMagnitude, hne, Bool.false_eq_true, ite_false]
  have hsv : Wasm.IEEE64.scaledValue w = (Wasm.IEEE64.scaledMagnitude w : Int) := by
    simp [Wasm.IEEE64.scaledValue, hs]
  have hpos : 0 < Wasm.IEEE64.scaledMagnitude w := by rw [hsm]; positivity
  have hsum : (Wasm.IEEE64.scaledValue w + Wasm.IEEE64.scaledValue w).natAbs =
      (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ Wasm.IEEE64.exponent w := by
    rw [hsv, hsm]
    set m := (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ (Wasm.IEEE64.exponent w - 1) with hm
    have h2 : (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ Wasm.IEEE64.exponent w = 2 * m := by
      have : 2 ^ Wasm.IEEE64.exponent w = 2 * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this, hm]
      ring
    have h3 : ((m : ℤ) + (m : ℤ)) = ((2 * m : ℕ) : ℤ) := by push_cast; ring
    rw [h2, h3]
    rfl
  have hne : Wasm.IEEE64.scaledValue w + Wasm.IEEE64.scaledValue w ≠ 0 := by
    rw [hsv]; omega
  have hnn : ¬ Wasm.IEEE64.scaledValue w + Wasm.IEEE64.scaledValue w < 0 := by
    rw [hsv]; omega
  have hadd : Wasm.IEEE64.add w w = Wasm.IEEE64.roundScaledMagnitude false
      ((2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ Wasm.IEEE64.exponent w) := by
    rw [← hsum]
    simp [Wasm.IEEE64.add, not_nan_of_finite hf, not_infinite_of_finite hf, hne, hnn]
  rw [hadd, F64RoundFinish.roundScaled_mul_pow false _ _ (by omega) (by omega) (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega),
    F64PowerScale.mul_power 1024 w (by norm_num) (by norm_num) hf he1 (by omega),
    ite_eq_right (by omega), hs,
    show Wasm.IEEE64.exponent w + 1024 - 1023 = Wasm.IEEE64.exponent w + 1 by omega,
    show 2 ^ 52 + Wasm.IEEE64.fraction w - 2 ^ 52 = Wasm.IEEE64.fraction w by omega]

/-- `x + x` is exact for `2 ≤ x < 2 ^ 1023`. -/
theorem add_self_exact (x : Float) (hxf : Finite x.toBits) (hx2 : 2 ≤ value x.toBits)
    (hix : x.toBits >>> 32 &&& 0x7fffffff < 0x7fe00000) :
    Finite (x + x).toBits ∧ value (x + x).toBits = 2 * value x.toBits := by
  have hs : Wasm.IEEE64.sign x.toBits = false := F64Exact.sign_of_pos _ (by linarith)
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hhw := TrigSinCos.high_word x.toBits
  have hix' := UInt64.lt_iff_toNat_lt.mp hix
  rw [hhw] at hix'
  simp only [UInt64.reduceToNat] at hix'
  have he2 : Wasm.IEEE64.exponent x.toBits ≤ 2045 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have he1 : 1 ≤ Wasm.IEEE64.exponent x.toBits := by
    by_contra h0
    have he0 : Wasm.IEEE64.exponent x.toBits = 0 := by omega
    have hsmall : value x.toBits < 1 := by
      have h1 : x.toBits.toNat < 0x0010000000000000 := by
        simp only [Wasm.IEEE64.exponent] at he0
        omega
      have := F64PositiveOrder.value_strict (left := x.toBits)
        (right := (0x0010000000000000 : UInt64)) (by decide) h1
      have h2 : value (0x0010000000000000 : UInt64) ≤ 1 := by
        rw [← PolyBound.ratOfWord_cast]
        have : PolyBound.ratOfWord 0x0010000000000000 = 1 / 2 ^ 1022 := by decide +kernel
        rw [this]
        norm_num
      linarith
    linarith
  rw [F64Bits.toBits_add, add_self_word _ hxf hs he1 he2]
  have h := F64PowerScale.mul_power_finite 1024 x.toBits (by norm_num) (by norm_num) hxf he1
    (by omega) (by omega)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  norm_num

/-- The sign of a finite `Float` against `0.0`. -/
theorem zero_lt_iff (x : Float) (hxf : Finite x.toBits) : 0.0 < x ↔ 0 < value x.toBits := by
  have h0 : (0.0 : Float).toBits = 0 := by decide
  have hn : Wasm.IEEE64.isNaN x.toBits = false := not_nan_of_finite hxf
  rw [F64Bits.lt_iff, h0]
  unfold Wasm.IEEE64.lt
  rw [hn, TrigSmall.value_of_scaled]
  have hz : Wasm.IEEE64.isNaN (0 : UInt64) = false := by decide
  have hs : Wasm.IEEE64.scaledValue (0 : UInt64) = 0 := by decide
  simp only [hz, hs, Bool.false_or, Bool.false_eq_true, ite_false, decide_eq_true_eq]
  constructor
  · intro h
    exact div_pos (by exact_mod_cast h) (by positivity)
  · intro h
    by_contra hc
    have : (Wasm.IEEE64.scaledValue x.toBits : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hc
    have := div_nonpos_of_nonpos_of_nonneg this (show (0 : ℝ) ≤ 2 ^ 1074 by positivity)
    linarith

theorem fcongr {f : Float} {v v' e : ℝ} (h : FApprox f v e) (hv : v = v') : FApprox f v' e :=
  hv ▸ h

/-- The quotient `z / w` of the branch that divides by the larger of `A` and `B`. -/
theorem quot_near {z w : Float} {A B ea e m : ℝ} (hz : FApprox z (A * B) e)
    (hw : FApprox w A ea) (hAB : A ^ 2 + B ^ 2 = 2) (hm : m ≤ |A|) (hem : ea < m)
    (hB : (1 + e) / (m - ea) < 2 ^ 1022) :
    FApprox (z / w) B ((e + ea / m) / (m - ea) + (1 + e) / (m - ea) / 2 ^ 53 + 1 / 2 ^ 1075) := by
  have hab : |A * B| ≤ 1 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B, abs_nonneg A, abs_nonneg B]
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, abs_zero] at hm
    have : 0 ≤ ea := (abs_nonneg _).trans hw.2
    linarith
  have h := fapprox_div hz hw 1 m hab hm hem _ le_rfl hB
  simp only [one_mul] at h
  rwa [mul_div_cancel_left₀ B hA0] at h

/-- The error bound of `quot_near` in the case of the code. -/
theorem quot_bound : ((71 / 50 * 𝐮) + (96 / 25 * 𝐮) / (1 - 1 / 2 ^ 48)) /
      ((1 - 1 / 2 ^ 48) - 96 / 25 * 𝐮) + (1 + 71 / 50 * 𝐮) / ((1 - 1 / 2 ^ 48) - 96 / 25 * 𝐮) /
        2 ^ 53 + 1 / 2 ^ 1075 ≤ 627 / 100 * 𝐮 := by
  norm_num [unitRoundoff64]

/-- The rounded product `s c` and what its sign says about `sin x cos x`. -/
theorem product_near {s c : Float} {σ γ : ℝ} (hs : FApprox s σ trigErr) (hc : FApprox c γ trigErr)
    (hσ : |σ| ≤ 1) (hγ : |γ| ≤ 1) :
    Finite (s * c).toBits ∧ |value (s * c).toBits - σ * γ| ≤ 1 / 2 ^ 50 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have h := fapprox_mul hs hc 1 1 hσ hγ ((1 + trigErr) * (1 + trigErr)) le_rfl
    (by unfold trigErr; rw [hu]; norm_num)
  refine ⟨h.1, h.2.trans ?_⟩
  unfold trigErr
  rw [hu]
  norm_num

/-- The direct sum `s + c` and difference `s - c`. -/
theorem add_near {s c : Float} {σ γ : ℝ} (hs : FApprox s σ trigErr) (hc : FApprox c γ trigErr)
    (h : |σ + γ| ≤ 3 / 2) : FApprox (s + c) (σ + γ) (96 / 25 * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hh := fapprox_add_half hs hc 1022 (by norm_num) (by unfold trigErr; rw [hu]; norm_num; linarith)
  refine ⟨hh.1, hh.2.trans ?_⟩
  unfold trigErr
  rw [hu]
  norm_num

theorem sub_near {s c : Float} {σ γ : ℝ} (hs : FApprox s σ trigErr) (hc : FApprox c γ trigErr)
    (h : |σ - γ| ≤ 3 / 2) : FApprox (s - c) (σ - γ) (96 / 25 * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hh := fapprox_sub_half hs hc 1022 (by norm_num) (by unfold trigErr; rw [hu]; norm_num; linarith)
  refine ⟨hh.1, hh.2.trans ?_⟩
  unfold trigErr
  rw [hu]
  norm_num

/-- `|A| ≥ 1 - 2 ^ -48` from `A² ≥ 1 - 2 ^ -49`. -/
theorem abs_ge_of_sq {A : ℝ} (h : 1 - 1 / 2 ^ 49 ≤ A ^ 2) : 1 - 1 / 2 ^ 48 ≤ |A| := by
  by_contra hc
  replace hc := not_le.mp hc
  have h0 := abs_nonneg A
  have : A ^ 2 < (1 - 1 / 2 ^ 48) ^ 2 := by
    rw [← sq_abs]
    exact pow_lt_pow_left₀ hc h0 (by norm_num)
  nlinarith

theorem abs_le_of_sq {A : ℝ} (h : A ^ 2 ≤ 9 / 4) : |A| ≤ 3 / 2 := by
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt (A ^ 2) ≤ Real.sqrt (9 / 4) := Real.sqrt_le_sqrt h
    _ = 3 / 2 := by
      rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)

/-- The two branches of a pair, as `asym0` and `asym1` produce them. -/
def Branches (cc ss : Float) (A B : ℝ) : Prop :=
  (FApprox cc A (96 / 25 * 𝐮) ∧ FApprox ss B (627 / 100 * 𝐮) ∧
      1 - 1 / 2 ^ 48 ≤ |A| ∧ B ^ 2 ≤ 1 + 1 / 2 ^ 48) ∨
    (FApprox cc A (627 / 100 * 𝐮) ∧ FApprox ss B (96 / 25 * 𝐮) ∧
      1 - 1 / 2 ^ 48 ≤ |B| ∧ A ^ 2 ≤ 1 + 1 / 2 ^ 48)

theorem sincos_bounds (v : ℝ) : |Real.sin v| ≤ 1 ∧ |Real.cos v| ≤ 1 ∧
    Real.sin v ^ 2 + Real.cos v ^ 2 = 1 :=
  ⟨Real.abs_sin_le_one v, Real.abs_cos_le_one v, Real.sin_sq_add_cos_sq v⟩

theorem z_of_cos (x : Float) (hxf : Finite x.toBits) (hx2 : 2 ≤ value x.toBits)
    (hix : x.toBits >>> 32 &&& 0x7fffffff < 0x7fe00000) :
    FApprox (Trig.cos (x + x)) (Real.cos (value x.toBits) ^ 2 - Real.sin (value x.toBits) ^ 2)
      trigErr := by
  obtain ⟨hf, hv⟩ := add_self_exact x hxf hx2 hix
  have h := cos_near (x + x) hf
  rw [hv] at h
  refine fcongr h ?_
  rw [Real.cos_two_mul]
  linear_combination Real.sin_sq_add_cos_sq (value x.toBits)

/-- `asym0` for `2 ≤ x < 2 ^ 1023`. -/
theorem asym0_near (x : Float) (hxf : Finite x.toBits) (hx2 : 2 ≤ value x.toBits)
    (ix : UInt64) (hix : ix = x.toBits >>> 32 &&& 0x7fffffff) (hlt : ix < 0x7fe00000) :
    Branches (Bessel.asym0 Trig.invPi Trig.halfPi ix x).1 (Bessel.asym0 Trig.invPi Trig.halfPi ix x).2
      (Real.sin (value x.toBits) + Real.cos (value x.toBits))
      (Real.sin (value x.toBits) - Real.cos (value x.toBits)) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  set v := value x.toBits
  obtain ⟨hσ, hγ, h1⟩ := sincos_bounds v
  have hs : FApprox (Trig.sinWith Trig.invPi Trig.halfPi x) (Real.sin v) trigErr := sin_near x hxf
  have hc : FApprox (Trig.cosWith Trig.invPi Trig.halfPi x) (Real.cos v) trigErr := cos_near x hxf
  have hz0 := z_of_cos x hxf hx2 (hix ▸ hlt)
  have hz : FApprox (-Trig.cosWith Trig.invPi Trig.halfPi (x + x))
      ((Real.sin v + Real.cos v) * (Real.sin v - Real.cos v)) trigErr := by
    refine fcongr (fapprox_neg hz0) ?_
    ring
  have hAB : (Real.sin v + Real.cos v) ^ 2 + (Real.sin v - Real.cos v) ^ 2 = 2 := by
    nlinarith
  have hcc := add_near hs hc (abs_le_of_sq (by nlinarith [sq_nonneg (Real.sin v - Real.cos v)]))
  have hss := sub_near hs hc (abs_le_of_sq (by nlinarith [sq_nonneg (Real.sin v + Real.cos v)]))
  obtain ⟨hpf, hp⟩ := product_near hs hc hσ hγ
  unfold Bessel.asym0
  dsimp only
  rw [ite_eq_left hlt]
  by_cases hneg : Trig.sinWith Trig.invPi Trig.halfPi x * Trig.cosWith Trig.invPi Trig.halfPi x < 0.0
  · rw [ite_eq_left hneg]
    have hv := (TrigSinCos.lt_zero_iff _ hpf).mp hneg
    have hB2 : 1 - 1 / 2 ^ 49 ≤ (Real.sin v - Real.cos v) ^ 2 := by
      have := (abs_le.mp hp).1
      nlinarith
    have hm := abs_ge_of_sq hB2
    have hq := quot_near (A := Real.sin v - Real.cos v) (B := Real.sin v + Real.cos v) (m := 1 - 1 / 2 ^ 48)
      (fcongr hz (by ring)) hss (by linarith) hm (by rw [hu]; norm_num)
      (by unfold trigErr; rw [hu]; norm_num)
    right
    refine ⟨hq.mono (by unfold trigErr at *; exact quot_bound), hss, hm, ?_⟩
    have := (abs_le.mp hp).1
    nlinarith
  · rw [ite_eq_right hneg]
    have hv : 0 ≤ value (Trig.sinWith Trig.invPi Trig.halfPi x *
        Trig.cosWith Trig.invPi Trig.halfPi x).toBits :=
      not_lt.mp fun h => hneg ((TrigSinCos.lt_zero_iff _ hpf).mpr h)
    have hA2 : 1 - 1 / 2 ^ 49 ≤ (Real.sin v + Real.cos v) ^ 2 := by
      have := (abs_le.mp hp).2
      nlinarith
    have hm := abs_ge_of_sq hA2
    have hq := quot_near (A := Real.sin v + Real.cos v) (B := Real.sin v - Real.cos v) (m := 1 - 1 / 2 ^ 48)
      hz hcc hAB hm (by rw [hu]; norm_num) (by unfold trigErr; rw [hu]; norm_num)
    left
    refine ⟨hcc, hq.mono (by unfold trigErr at *; exact quot_bound), hm, ?_⟩
    have := (abs_le.mp hp).2
    nlinarith

/-- `asym1` for `2 ≤ x < 2 ^ 1023`. -/
theorem asym1_near (x : Float) (hxf : Finite x.toBits) (hx2 : 2 ≤ value x.toBits)
    (ix : UInt64) (hix : ix = x.toBits >>> 32 &&& 0x7fffffff) (hlt : ix < 0x7fe00000) :
    Branches (Bessel.asym1 Trig.invPi Trig.halfPi ix x).1 (Bessel.asym1 Trig.invPi Trig.halfPi ix x).2
      (Real.sin (value x.toBits) - Real.cos (value x.toBits))
      (-Real.sin (value x.toBits) - Real.cos (value x.toBits)) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  set v := value x.toBits
  obtain ⟨hσ, hγ, h1⟩ := sincos_bounds v
  have hs : FApprox (Trig.sinWith Trig.invPi Trig.halfPi x) (Real.sin v) trigErr := sin_near x hxf
  have hc : FApprox (Trig.cosWith Trig.invPi Trig.halfPi x) (Real.cos v) trigErr := cos_near x hxf
  have hz0 := z_of_cos x hxf hx2 (hix ▸ hlt)
  have hz : FApprox (Trig.cosWith Trig.invPi Trig.halfPi (x + x))
      ((Real.sin v - Real.cos v) * (-Real.sin v - Real.cos v)) trigErr := by
    refine fcongr hz0 ?_
    ring
  have hAB : (Real.sin v - Real.cos v) ^ 2 + (-Real.sin v - Real.cos v) ^ 2 = 2 := by
    nlinarith
  have hcc := sub_near hs hc (abs_le_of_sq (by nlinarith [sq_nonneg (Real.sin v + Real.cos v)]))
  have hss : FApprox (-Trig.sinWith Trig.invPi Trig.halfPi x - Trig.cosWith Trig.invPi Trig.halfPi x)
      (-Real.sin v - Real.cos v) (96 / 25 * 𝐮) := by
    have hn := fapprox_neg hs
    have hh := fapprox_sub_half hn hc 1022 (by norm_num) (by
      have : |-Real.sin v - Real.cos v| ≤ 3 / 2 :=
        abs_le_of_sq (by nlinarith [sq_nonneg (Real.sin v - Real.cos v)])
      unfold trigErr; rw [hu]; norm_num; linarith)
    refine ⟨hh.1, hh.2.trans ?_⟩
    unfold trigErr
    rw [hu]
    norm_num
  obtain ⟨hpf, hp⟩ := product_near hs hc hσ hγ
  unfold Bessel.asym1
  dsimp only
  rw [ite_eq_left hlt]
  by_cases hpos : Trig.sinWith Trig.invPi Trig.halfPi x * Trig.cosWith Trig.invPi Trig.halfPi x > 0.0
  · rw [ite_eq_left hpos]
    have hv := (zero_lt_iff _ hpf).mp hpos
    have hB2 : 1 - 1 / 2 ^ 49 ≤ (-Real.sin v - Real.cos v) ^ 2 := by
      have := (abs_le.mp hp).2
      nlinarith
    have hm := abs_ge_of_sq hB2
    have hq := quot_near (A := -Real.sin v - Real.cos v) (B := Real.sin v - Real.cos v)
      (m := 1 - 1 / 2 ^ 48) (fcongr hz (by ring)) hss (by linarith) hm
      (by rw [hu]; norm_num) (by unfold trigErr; rw [hu]; norm_num)
    right
    refine ⟨hq.mono (by unfold trigErr at *; exact quot_bound), hss, hm, ?_⟩
    have := (abs_le.mp hp).2
    nlinarith
  · rw [ite_eq_right hpos]
    have hv : value (Trig.sinWith Trig.invPi Trig.halfPi x *
        Trig.cosWith Trig.invPi Trig.halfPi x).toBits ≤ 0 :=
      not_lt.mp fun h => hpos ((zero_lt_iff _ hpf).mpr h)
    have hA2 : 1 - 1 / 2 ^ 49 ≤ (Real.sin v - Real.cos v) ^ 2 := by
      have := (abs_le.mp hp).1
      nlinarith
    have hm := abs_ge_of_sq hA2
    have hq := quot_near (A := Real.sin v - Real.cos v) (B := -Real.sin v - Real.cos v)
      (m := 1 - 1 / 2 ^ 48) hz hcc hAB hm (by rw [hu]; norm_num)
      (by unfold trigErr; rw [hu]; norm_num)
    left
    refine ⟨hcc, hq.mono (by unfold trigErr at *; exact quot_bound), hm, ?_⟩
    have := (abs_le.mp hp).1
    nlinarith

/-- From `2 ^ 1023` on, both values of `asym0` are direct. -/
theorem asym0_huge (x : Float) (hxf : Finite x.toBits) (ix : UInt64) (hge : ¬ ix < 0x7fe00000) :
    FApprox (Bessel.asym0 Trig.invPi Trig.halfPi ix x).1
        (Real.sin (value x.toBits) + Real.cos (value x.toBits)) (96 / 25 * 𝐮) ∧
      FApprox (Bessel.asym0 Trig.invPi Trig.halfPi ix x).2
        (Real.sin (value x.toBits) - Real.cos (value x.toBits)) (96 / 25 * 𝐮) := by
  set v := value x.toBits
  obtain ⟨hσ, hγ, h1⟩ := sincos_bounds v
  have hs : FApprox (Trig.sinWith Trig.invPi Trig.halfPi x) (Real.sin v) trigErr := sin_near x hxf
  have hc : FApprox (Trig.cosWith Trig.invPi Trig.halfPi x) (Real.cos v) trigErr := cos_near x hxf
  unfold Bessel.asym0
  dsimp only
  rw [ite_eq_right hge]
  exact ⟨add_near hs hc (abs_le_of_sq (by nlinarith [sq_nonneg (Real.sin v - Real.cos v)])),
    sub_near hs hc (abs_le_of_sq (by nlinarith [sq_nonneg (Real.sin v + Real.cos v)]))⟩

/-- From `2 ^ 1023` on, both values of `asym1` are direct. -/
theorem asym1_huge (x : Float) (hxf : Finite x.toBits) (ix : UInt64) (hge : ¬ ix < 0x7fe00000) :
    FApprox (Bessel.asym1 Trig.invPi Trig.halfPi ix x).1
        (Real.sin (value x.toBits) - Real.cos (value x.toBits)) (96 / 25 * 𝐮) ∧
      FApprox (Bessel.asym1 Trig.invPi Trig.halfPi ix x).2
        (-Real.sin (value x.toBits) - Real.cos (value x.toBits)) (96 / 25 * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  set v := value x.toBits
  obtain ⟨hσ, hγ, h1⟩ := sincos_bounds v
  have hs : FApprox (Trig.sinWith Trig.invPi Trig.halfPi x) (Real.sin v) trigErr := sin_near x hxf
  have hc : FApprox (Trig.cosWith Trig.invPi Trig.halfPi x) (Real.cos v) trigErr := cos_near x hxf
  unfold Bessel.asym1
  dsimp only
  rw [ite_eq_right hge]
  refine ⟨sub_near hs hc (abs_le_of_sq (by nlinarith [sq_nonneg (Real.sin v + Real.cos v)])), ?_⟩
  have hn := fapprox_neg hs
  have hh := fapprox_sub_half hn hc 1022 (by norm_num) (by
    have : |-Real.sin v - Real.cos v| ≤ 3 / 2 :=
      abs_le_of_sq (by nlinarith [sq_nonneg (Real.sin v - Real.cos v)])
    unfold trigErr; rw [hu]; norm_num; linarith)
  refine ⟨hh.1, hh.2.trans ?_⟩
  unfold trigErr
  rw [hu]
  norm_num

#print axioms add_self_word
#print axioms add_self_exact
#print axioms zero_lt_iff
#print axioms quot_near
#print axioms product_near
#print axioms asym0_near
#print axioms asym1_near
#print axioms asym0_huge
#print axioms asym1_huge

end Verified.Examples.BesselCS
