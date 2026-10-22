import Library.Numerics.Float64.Sinpi.SinpiProduct
import Library.Numerics.Float64.Trig.TrigQuadrant
import Library.Numerics.Float64.Tan.TanWith

/-!
The kernels of `Sinpi`: for `x` from `2 ^ -54` to `1/4`, `kernelSinpi x` and `kernelCospi x` lie
within one step of `sin (π x)` and `cos (π x)`, and for `x` from `2 ^ -54` below `1/2`,
`kernelTanpi x` lies within one step of `tan (π x)`.  The product `π x = w + t` meets the
hypotheses of fdlibm's kernels: `t` within `|w| / 2 ^ 52` and `w + t` within a relative `2 ^ -59`
of `π x`.  Above `1/4`, `kernelTanpi` takes `-(-1/tan (π (1/2 - x)))`, which is `tan (π x)`.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiKernels

open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Trig.TrigKernelWords Library.Numerics.Float64.Trig.TrigKernelSpec Library.Numerics.Float64.Trig.TrigCosKernel Library.Numerics.Float64.Trig.TrigStep
  SinpiProduct SinpiSingle Library.Numerics.Float64.Tan.TanWith Library.Numerics.Float64.Tan.TanBigWords Library.Numerics.Float64.Tan.TanStep

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 1200

theorem sub_abs_le (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have := abs_add_le a (-b)
  rwa [abs_neg, ← sub_eq_add_neg] at this

theorem flt_iff (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a < b ↔ value a.toBits < value b.toBits := by
  rw [F64Bits.lt_iff]
  unfold Wasm.IEEE64.lt
  rw [not_nan_of_finite ha, not_nan_of_finite hb, Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled,
    Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled, div_lt_div_iff_of_pos_right (by positivity)]
  simp only [Bool.false_or, Bool.false_eq_true, ite_false, decide_eq_true_eq]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem feq_iff (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    (a == b) = true ↔ value a.toBits = value b.toBits := by
  rw [F64Bits.beq_eq]
  unfold Wasm.IEEE64.eq
  rw [not_nan_of_finite ha, not_nan_of_finite hb, Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled,
    Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled]
  simp only [Bool.false_or, Bool.false_eq_true, ite_false, beq_iff_eq]
  constructor
  · intro h; rw [h]
  · intro h
    have := (div_left_inj' (show (2 : ℝ) ^ 1074 ≠ 0 by positivity)).mp h
    exact_mod_cast this

/-- A finite word equal to its target is within one step of it. -/
theorem exact_within (c : UInt64) (y : ℝ) (hcf : Finite c) (hc : value c = y)
    (hy0 : 1 / 2 ^ 1000 ≤ |y|) (hy1 : |y| ≤ 2 ^ 1000) :
    F64SignedRounding.WithinSteps 1 y c := by
  refine near_rel c y y hcf (fun v _ => by rw [hc, sub_self, abs_zero]; exact abs_nonneg _)
    hy0 hy1 ?_
  rw [sub_self, abs_zero]
  have : (0 : ℝ) ≤ 𝐮 := by rw [show 𝐮 = 1 / 2 ^ 53 from rfl]; positivity
  positivity

/-- fdlibm's sine and cosine kernels on `y0 + y1` near `r`. -/
theorem trig_pair (y0 y1 : Float) (r : ℝ) (f0 : Finite y0.toBits) (f1 : Finite y1.toBits)
    (hlo : 1 / 2 ^ 70 ≤ |value y0.toBits|) (hX1 : |value y0.toBits| ≤ 78541 / 100000)
    (hy : |value y1.toBits| ≤ |value y0.toBits| / 2 ^ 52)
    (har : |value y0.toBits + value y1.toBits - r| ≤ |r| / 2 ^ 59)
    (hup : |value y0.toBits| ≤ |r| * (1 + 1 / 2 ^ 50)) (hr0 : 1 / 2 ^ 69 ≤ |r|)
    (hr1 : |r| ≤ 78541 / 100000) :
    F64SignedRounding.WithinSteps 1 (Real.sin r) (Trig.kernelSin y0 y1 true).toBits ∧
      F64SignedRounding.WithinSteps 1 (Real.cos r) (Trig.kernelCos y0 y1).toBits := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hcf, t, hct, hts⟩ := sinTail_spec y0.toBits y1.toBits _ f0 f1 rfl hlo hX1 hy
    rw [kernelSin_tail_bits]
    exact sin_final _ t _ r _ hcf hct hts har (abs_nonneg _) hup hr0 hr1
  · obtain ⟨hcf, hc⟩ := cos_spec y0.toBits y1.toBits _ f0 f1 rfl hlo hX1 hy
    rw [kernelCos_bits]
    exact cos_final _ _ r hcf hc har hr1

/-- `Sinpi.piProduct` on a float from `2 ^ -54` to `1/2`, with the hypotheses of the kernels. -/
theorem product_float (x : Float) (V : ℝ) (hs : x.toBits.toNat < 2 ^ 63) (hf : Finite x.toBits)
    (hV : value x.toBits = V) (hV0 : 1 / 2 ^ 54 ≤ V) (hV1 : V ≤ 1 / 2) :
    Finite (Sinpi.piProduct x).1.toBits ∧ Finite (Sinpi.piProduct x).2.toBits ∧
      1 / 2 ^ 70 ≤ |value (Sinpi.piProduct x).1.toBits| ∧
      |value (Sinpi.piProduct x).1.toBits| ≤ |Real.pi * V| * (1 + 1 / 2 ^ 50) ∧
      |value (Sinpi.piProduct x).2.toBits| ≤ |value (Sinpi.piProduct x).1.toBits| / 2 ^ 52 ∧
      |value (Sinpi.piProduct x).1.toBits + value (Sinpi.piProduct x).2.toBits - Real.pi * V| ≤
        |Real.pi * V| / 2 ^ 59 ∧ 1 / 2 ^ 69 ≤ |Real.pi * V| ∧ |Real.pi * V| ≤ Real.pi * V := by
  obtain ⟨b1, b2⟩ := product_bits x
  rw [b1, b2]
  obtain ⟨f1, f2, herr, ht⟩ := product_spec x.toBits V hs hf hV hV0 hV1
  have hpi := Real.pi_gt_three
  have hV0' : 0 < V := lt_of_lt_of_le (by positivity) hV0
  have hPV : |Real.pi * V| = Real.pi * V := abs_of_pos (by positivity)
  have h3 : 3 * V ≤ Real.pi * V := mul_le_mul_of_nonneg_right hpi.le hV0'.le
  rw [hPV]
  have ha := abs_sub_abs_le_abs_sub (value (productW x.toBits).1 + value (productW x.toBits).2)
    (Real.pi * V)
  have hb := abs_sub_abs_le_abs_sub (Real.pi * V)
    (value (productW x.toBits).1 + value (productW x.toBits).2)
  rw [abs_sub_comm (Real.pi * V), abs_of_pos (by positivity : 0 < Real.pi * V)] at hb
  rw [abs_of_pos (by positivity : 0 < Real.pi * V)] at ha
  have hs1 := abs_add_le (value (productW x.toBits).1) (value (productW x.toBits).2)
  have hs2 := abs_sub_abs_le_abs_sub (value (productW x.toBits).1 + value (productW x.toBits).2)
    (value (productW x.toBits).2)
  rw [add_sub_cancel_right] at hs2
  have hs3 := sub_abs_le (value (productW x.toBits).1 + value (productW x.toBits).2)
    (value (productW x.toBits).2)
  rw [add_sub_cancel_right] at hs3
  refine ⟨f1, f2, ?_, ?_, ht, ?_, ?_, le_refl _⟩
  · have : (1 : ℝ) / 2 ^ 70 * (1 + 1 / 2 ^ 52) ≤ 3 * (1 / 2 ^ 54) - 1 / 2 ^ 54 / 2 ^ 62 := by
      norm_num
    linarith
  · have : V / 2 ^ 62 ≤ Real.pi * V / 2 ^ 62 := by linarith
    linarith
  · linarith
  · linarith

theorem kernelSinpi_eq (x : Float) :
    Sinpi.kernelSinpi x = Trig.kernelSin (Sinpi.piProduct x).1 (Sinpi.piProduct x).2 true := by
  unfold Sinpi.kernelSinpi
  split
  next hi lo heq => rw [heq]

theorem kernelCospi_eq (x : Float) :
    Sinpi.kernelCospi x = Trig.kernelCos (Sinpi.piProduct x).1 (Sinpi.piProduct x).2 := by
  unfold Sinpi.kernelCospi
  split
  next hi lo heq => rw [heq]

/-- `kernelSinpi` and `kernelCospi` from `2 ^ -54` to `1/4`. -/
theorem kernel_pair (x : Float) (V : ℝ) (hs : x.toBits.toNat < 2 ^ 63) (hf : Finite x.toBits)
    (hV : value x.toBits = V) (hV0 : 1 / 2 ^ 54 ≤ V) (hV1 : V ≤ 1 / 4) :
    F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * V)) (Sinpi.kernelSinpi x).toBits ∧
      F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * V)) (Sinpi.kernelCospi x).toBits := by
  obtain ⟨f1, f2, hlo, hup, ht, har, hr0, hr⟩ := product_float x V hs hf hV hV0 (by linarith)
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hV0' : 0 < V := lt_of_lt_of_le (by positivity) hV0
  have hr1 : |Real.pi * V| ≤ 78541 / 100000 := by
    rw [abs_of_pos (by positivity : 0 < Real.pi * V)]
    have : Real.pi * V ≤ 3.1416 * (1 / 4) :=
      mul_le_mul hpi.le hV1 hV0'.le (by norm_num)
    linarith
  have hX1 : |value (Sinpi.piProduct x).1.toBits| ≤ 78541 / 100000 := by
    have : |Real.pi * V| * (1 + 1 / 2 ^ 50) ≤ 0.7854 * (1 + 1 / 2 ^ 50) := by
      rw [abs_of_pos (by positivity : 0 < Real.pi * V)]
      have : Real.pi * V ≤ 3.1416 * (1 / 4) :=
        mul_le_mul hpi.le hV1 hV0'.le (by norm_num)
      exact mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have : (0.7854 : ℝ) * (1 + 1 / 2 ^ 50) ≤ 78541 / 100000 := by norm_num
    linarith
  obtain ⟨hs1, hc1⟩ := trig_pair _ _ (Real.pi * V) f1 f2 hlo hX1 ht har hup hr0 hr1
  rw [kernelSinpi_eq, kernelCospi_eq]
  exact ⟨hs1, hc1⟩

#print axioms kernel_pair

end Library.Numerics.Float64.Sinpi.SinpiKernels
