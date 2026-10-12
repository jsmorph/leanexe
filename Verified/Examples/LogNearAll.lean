import Verified.Examples.LogNearMain
import Verified.Examples.LogTheorem
import LeanExe.ProofKit.F64Approx

/-!
The error of `Log.log` as a distance for every finite argument with positive value: the result
lies within `(6/5) u |log x| + 2 ^ -59` of `log x`, with `u = 2 ^ -53` (`log_near`).  On the main
path `LogNearMain` gives `u |log x| + 2 ^ -59`.  On the path near 1 the result before its final
rounding is within `(1/15 + 1/13) u ρ + (15/16) 2 ^ -62 ρ` of `log x` for `ρ = |x - 1|`, and
`|log x| ≥ (15/16) ρ`, so the error is below `1.16 u |log x|`; `near1_near` follows
`LogTheorem.near1_within` up to its conversion to steps.  `log 1` is exactly `+0`.
-/

namespace Verified.Examples.LogNearAll
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx LogTheorem

set_option exponentiation.threshold 4096

local notation "𝐮" => unitRoundoff64

/-- The bound on the error of `Log.log` at a result near `y`. -/
noncomputable def logErr (y : ℝ) : ℝ := 6 / 5 * 𝐮 * |y| + 1 / 2 ^ 59

theorem main_le (y : ℝ) : 𝐮 * |y| + 1 / 2 ^ 59 ≤ logErr y := by
  unfold logErr
  have : 0 ≤ 𝐮 * |y| := mul_nonneg (by norm_num [unitRoundoff64]) (abs_nonneg _)
  linarith

theorem near1_near (x : Float) (hlo : 4606619468846596096 ≤ x.toBits.toNat)
    (hhi : x.toBits.toNat < 4607473789381378048) (hne : x.toBits.toNat ≠ 4607182418800017408) :
    FApprox (Log.log x) (Real.log (value x.toBits)) (logErr (Real.log (value x.toBits))) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  unfold FApprox Approx
  rw [Log.log, LogBranches.near_selected _ _ x hlo hhi hne, LogNear1.near1_bits,
    LogNear1.near1Word_eq]
  have hlt : x.toBits.toNat < 2 ^ 63 := by simp only [Nat.reducePow]; omega
  have hs : Wasm.IEEE64.sign x.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    exact hlt
  have he : Wasm.IEEE64.exponent x.toBits = 1022 ∨ Wasm.IEEE64.exponent x.toBits = 1023 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have hxf : Finite x.toBits := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
    omega
  obtain ⟨hb1, hb2⟩ := LogMain.bound_values
  have hv1 : 15 / 16 ≤ value x.toBits := by
    rw [← hb1]
    exact (F64PositiveOrder.value_le_iff (by decide) hlt).mpr hlo
  have hv2 : value x.toBits < 1 + 265 / 4096 := by
    rw [← hb2]
    exact F64PositiveOrder.value_strict (by decide) hhi
  have hone : value (0x3FF0000000000000 : UInt64) = 1 := by
    rw [← PolyBound.ratOfWord_cast, (LogNear1.near1_bounds).2.2.2.2.2.2.2.2.2.2.2.2]
    norm_num
  have hvne : value x.toBits ≠ 1 := by
    intro h
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · have := F64PositiveOrder.value_strict (left := x.toBits)
        (right := (0x3FF0000000000000 : UInt64)) (by decide) h1
      rw [hone] at this
      linarith
    · have := F64PositiveOrder.value_strict (left := (0x3FF0000000000000 : UInt64))
        (right := x.toBits) hlt h1
      rw [hone] at this
      linarith
  have hcf : Finite (0x3FF0000000000000 : UInt64) := (LogNear1.near1_constants).2.2.2.2.2.2.2.2.2.2.2.2
  -- `r = x - 1` exactly
  have hgx : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue x.toBits := by
    have hne0 : (Wasm.IEEE64.exponent x.toBits == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Wasm.IEEE64.scaledMagnitude, hne0, ite_false]
    rcases he with h | h <;> rw [h]
    · exact ⟨(2 ^ 52 + Wasm.IEEE64.fraction x.toBits : Nat), by push_cast; ring⟩
    · exact ⟨(2 * (2 ^ 52 + Wasm.IEEE64.fraction x.toBits) : Nat), by push_cast; ring⟩
  have hg1 : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) :=
    ⟨2 ^ 53, by decide +kernel⟩
  have hdiff : value x.toBits - value (0x3FF0000000000000 : UInt64) =
      ((Wasm.IEEE64.scaledValue x.toBits - Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) :
        Int) : ℝ) / 2 ^ 1074 := by
    simp only [value]
    push_cast
    ring
  have hbound : |Wasm.IEEE64.scaledValue x.toBits -
      Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64)| ≤ 2 ^ 53 * 2 ^ 1021 := by
    have h : |((Wasm.IEEE64.scaledValue x.toBits -
        Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) : Int) : ℝ)| ≤
        ((2 ^ 53 * 2 ^ 1021 : Int) : ℝ) := by
      have heq : ((Wasm.IEEE64.scaledValue x.toBits -
          Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) : Int) : ℝ) =
          (value x.toBits - value (0x3FF0000000000000 : UInt64)) * 2 ^ 1074 := by
        rw [hdiff]
        field_simp
      rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), hone]
      have h1 : |value x.toBits - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have h2 : |value x.toBits - 1| * (2 : ℝ) ^ 1074 ≤ 1 * 2 ^ 1074 := by gcongr
      push_cast
      have h3 : (1 : ℝ) * 2 ^ 1074 ≤ 2 ^ 53 * 2 ^ 1021 := by norm_num
      linarith
    exact_mod_cast h
  obtain ⟨hrf, hrv⟩ := F64ErrorTrack.sub_exact_grid _ _ hxf hcf 1021 (by norm_num) hgx hg1 hbound
  rw [hone] at hrv
  -- `2 ^ -53 ≤ |x - 1| ≤ 1/15`
  have hρ0 : 1 / 2 ^ 53 ≤ |value x.toBits - 1| := by
    obtain ⟨m, hm⟩ := dvd_sub hgx hg1
    rw [hm, hone, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hdiff
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, mul_zero, zero_div] at hdiff
      exact hvne (by linarith)
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
    rw [hdiff, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1021)]
    rw [le_div_iff₀ (by positivity)]
    have : (1 : ℝ) / 2 ^ 53 * 2 ^ 1074 = 2 ^ 1021 * 1 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left hm1 (by positivity)
  have hρ1 : |value x.toBits - 1| ≤ 1 / 15 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hresf, hres⟩ := LogNear1.near1_error _ hrf _ (by rw [hrv]) hρ0 hρ1
    (Real.log (value x.toBits))
  have hker := LogKernelPoly.near1_kernel_error (value x.toBits - 1) (by linarith) (by linarith)
  rw [show 1 + (value x.toBits - 1) = value x.toBits by ring] at hker
  rw [hrv] at hres
  have hlow := log_near_lower (value x.toBits - 1) (by linarith) (by linarith)
  rw [show 1 + (value x.toBits - 1) = value x.toBits by ring] at hlow
  refine ⟨hresf, ?_⟩
  unfold logErr
  set ρ := |value x.toBits - 1|
  have hP : |(value x.toBits - 1) * PolyBound.eval LogKernelPoly.near1Kernel
      (value x.toBits - 1) - Real.log (value x.toBits)| ≤ ρ * ((15 / 16) / 2 ^ 62) := by
    rw [abs_sub_comm]
    exact hker
  have hρpos : 0 ≤ ρ := abs_nonneg _
  have hu0 : (0 : ℝ) ≤ 1 + unitRoundoff64 := by rw [hu]; norm_num
  have h1 := mul_le_mul_of_nonneg_left (add_le_add_left hP (unitRoundoff64 * ρ *
    (1 / 15 + 1 / 13))) hu0
  rw [hu] at h1 hres ⊢
  nlinarith [hlow, hρpos]

/-- `Log.log` on every finite argument with positive value. -/
theorem log_near (x : Float) (hf : Finite x.toBits) (hpos : 0 < value x.toBits) :
    FApprox (Log.log x) (Real.log (value x.toBits)) (logErr (Real.log (value x.toBits))) := by
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x.toBits) with h | h
    · exfalso
      have : value x.toBits = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h]
        split <;> simp
      linarith
    · exact h
  have hs : Wasm.IEEE64.sign x.toBits = false := by
    cases h : Wasm.IEEE64.sign x.toBits
    · rfl
    · exact absurd ((F64Magnitude.sign_value _ hmag).mp h) (not_lt.mpr hpos.le)
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hfin : Wasm.IEEE64.exponent x.toBits ≠ 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
    exact hf
  have hnz : 0 < x.toBits.toNat := by
    rcases Nat.eq_zero_or_pos x.toBits.toNat with h | h
    · exfalso
      have h0 : Wasm.IEEE64.scaledMagnitude x.toBits = 0 := by
        simp [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, h]
      omega
    · exact h
  by_cases hsub : x.toBits.toNat < 4503599627370496
  · obtain ⟨h1, h2⟩ := LogNearMain.subnormal_near x hnz hsub
    exact ⟨h1, h2.trans (main_le _)⟩
  · have he : 1 ≤ Wasm.IEEE64.exponent x.toBits := by
      simp only [Wasm.IEEE64.exponent]
      simp only [Nat.reducePow] at hlt
      omega
    by_cases hnear : 4606619468846596096 ≤ x.toBits.toNat ∧ x.toBits.toNat < 4607473789381378048
    · by_cases hone : x.toBits.toNat = 4607182418800017408
      · have hx1 : x.toBits = 0x3FF0000000000000 := UInt64.toNat_inj.mp (by rw [hone]; rfl)
        have hv1 : value x.toBits = 1 := by
          rw [hx1, ← PolyBound.ratOfWord_cast, (LogNear1.near1_bounds).2.2.2.2.2.2.2.2.2.2.2.2]
          norm_num
        rw [hv1, Real.log_one, Log.log, LogBranches.one_selected _ _ x hone]
        have h0 : (0.0 : Float).toBits = 0 := rfl
        have hz : PolyBound.ratOfWord 0 = 0 := by decide +kernel
        refine ⟨by rw [h0]; unfold CodeLib.IEEE64.Finite; decide, ?_⟩
        rw [h0, ← PolyBound.ratOfWord_cast, hz]
        unfold logErr
        norm_num
      · exact near1_near x hnear.1 hnear.2 hone
    · obtain ⟨h1, h2⟩ := LogNearMain.normal_near x hf hs he (by omega)
      exact ⟨h1, h2.trans (main_le _)⟩

#print axioms main_le
#print axioms near1_near
#print axioms log_near

end Verified.Examples.LogNearAll
