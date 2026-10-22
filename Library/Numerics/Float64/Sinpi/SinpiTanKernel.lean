import Library.Numerics.Float64.Sinpi.SinpiKernels

/-!
`Sinpi.kernelTanpi` for `x` from `2 ^ -54` below `1/2`: within one step of `tan (π x)`.  Below
`1/4` it is `Tan.kernelTan` on the product `π x`.  Above, `1/2 - x` is exact and at least
`2 ^ -54`, and the result `-(-1/tan (π (1/2 - x)))` is `tan (π x)`.  At `1/4` the result is 1.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiTanKernel

open CodeLib.IEEE64 LeanExe.ProofKit SinpiProduct SinpiKernels Library.Numerics.Float64.Tan.TanWith Library.Numerics.Float64.Tan.TanBigWords Library.Numerics.Float64.Tan.TanTrunc
  Library.Numerics.Float64.Trig.TrigSinCos

set_option exponentiation.threshold 1200

theorem quarter_facts : (0.25 : Float).toBits = 0x3FD0000000000000 ∧
    (0.5 : Float).toBits = 0x3FE0000000000000 ∧ (1.0 : Float).toBits = 0x3FF0000000000000 ∧
    value (0x3FD0000000000000 : UInt64) = 1 / 4 ∧ value (0x3FE0000000000000 : UInt64) = 1 / 2 ∧
    value (0x3FF0000000000000 : UInt64) = 1 ∧ Finite (0x3FD0000000000000 : UInt64) ∧
    Finite (0x3FE0000000000000 : UInt64) ∧ Finite (0x3FF0000000000000 : UInt64) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Library.Numerics.Float64.Trig.TrigReduce.value_word _ 1 2 (by norm_num) (by decide +kernel)]; norm_num
  · rw [Library.Numerics.Float64.Trig.TrigReduce.value_word _ 1 1 (by norm_num) (by decide +kernel)]; norm_num
  · rw [Library.Numerics.Float64.Trig.TrigReduce.value_word _ 1 0 (by norm_num) (by decide +kernel)]; norm_num
  all_goals unfold CodeLib.IEEE64.Finite; decide

/-- A positive word from `1/4` below `1/2` lies at most `1/2 - 2 ^ -54`. -/
theorem below_half (v : UInt64) (h0 : 1 / 4 ≤ |value v|) (h1 : |value v| < 1 / 2) :
    |value v| ≤ 1 / 2 - 1 / 2 ^ 54 := by
  have hl := F64SignedNearestSum.grid_lower v
  have hb := F64SignedNearestSum.grid_bound v
  have he1 : 1073 ≤ 53 + (Wasm.IEEE64.exponent v - 1) := by
    by_contra hc
    have : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent v - 1)) / 2 ^ 1074 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity), show (1 : ℝ) / 4 * 2 ^ 1074 = 2 ^ 1072 by norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have he0 : 1 ≤ Wasm.IEEE64.exponent v := by omega
  have he2 : 52 + (Wasm.IEEE64.exponent v - 1) ≤ 1072 := by
    by_contra hc
    have : (1 : ℝ) / 2 ≤ 2 ^ (52 + (Wasm.IEEE64.exponent v - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), show (1 : ℝ) / 2 * 2 ^ 1074 = 2 ^ 1073 by norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [hl he0]
  obtain ⟨m, hm, -⟩ := mag_split v
  have he : Wasm.IEEE64.exponent v - 1 = 1020 := by omega
  rw [he] at hm
  rw [F64RoundNearest.abs_value, hm] at h1 ⊢
  push_cast at h1 ⊢
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [div_le_iff₀ (by positivity)]
  have hm1 : (m : ℝ) < 2 ^ 53 := by linarith
  have hm2 : (m : ℝ) + 1 ≤ 2 ^ 53 := by
    have : m < 2 ^ 53 := by exact_mod_cast hm1
    have : m + 1 ≤ 2 ^ 53 := this
    exact_mod_cast this
  linarith

theorem kernelTanpi_cases (x : Float) :
    (x < 0.25 → Sinpi.kernelTanpi x =
      Tan.kernelTan (Sinpi.piProduct x).1 (Sinpi.piProduct x).2 false) ∧
    (¬ x < 0.25 → x > 0.25 → Sinpi.kernelTanpi x =
      -Tan.kernelTan (Sinpi.piProduct (0.5 - x)).1 (Sinpi.piProduct (0.5 - x)).2 true) ∧
    (¬ x < 0.25 → ¬ x > 0.25 → Sinpi.kernelTanpi x = 1.0) := by
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · unfold Sinpi.kernelTanpi
    rw [if_pos h]
  · unfold Sinpi.kernelTanpi
    rw [if_neg h1, if_pos h2]
  · unfold Sinpi.kernelTanpi
    rw [if_neg h1, if_neg h2]

/-- `kernelTanpi` from `2 ^ -54` below `1/2`. -/
theorem kernel_tanpi (x : Float) (V : ℝ) (hs : x.toBits.toNat < 2 ^ 63) (hf : Finite x.toBits)
    (hV : value x.toBits = V) (hV0 : 1 / 2 ^ 54 ≤ V) (hV1 : V < 1 / 2) :
    F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * V)) (Sinpi.kernelTanpi x).toBits := by
  obtain ⟨q25, q5, q1, v25, v5, v1, f25, f5, f1⟩ := quarter_facts
  obtain ⟨c1, c2, c3⟩ := kernelTanpi_cases x
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi3 := Real.pi_gt_three
  have hV0' : 0 < V := lt_of_lt_of_le (by positivity) hV0
  have hlt : x < 0.25 ↔ V < 1 / 4 := by
    rw [flt_iff x 0.25 hf (by rw [q25]; exact f25), q25, v25, hV]
  have hgt : x > 0.25 ↔ 1 / 4 < V := by
    show (0.25 : Float) < x ↔ _
    rw [flt_iff 0.25 x (by rw [q25]; exact f25) hf, q25, v25, hV]
  by_cases h1 : V < 1 / 4
  · rw [c1 (hlt.mpr h1)]
    obtain ⟨g1, g2, hlo, hup, ht, har, -, -⟩ := product_float x V hs hf hV hV0 (by linarith)
    have hX1 : |value (Sinpi.piProduct x).1.toBits| ≤ 78541 / 100000 := by
      have : |Real.pi * V| ≤ 0.7854 := by
        rw [abs_of_pos (by positivity : 0 < Real.pi * V)]
        have : Real.pi * V ≤ 3.1416 * (1 / 4) := mul_le_mul hpi.le h1.le hV0'.le (by norm_num)
        linarith
      have : |Real.pi * V| * (1 + 1 / 2 ^ 50) ≤ 0.7854 * (1 + 1 / 2 ^ 50) :=
        mul_le_mul_of_nonneg_right this (by norm_num)
      have : (0.7854 : ℝ) * (1 + 1 / 2 ^ 50) ≤ 78541 / 100000 := by norm_num
      linarith
    have hk := kernel_within _ _ false (Real.pi * V) _ g1 g2 rfl hlo hX1 ht har
    simpa using hk
  · by_cases h2 : 1 / 4 < V
    · rw [c2 (fun h => h1 (hlt.mp h)) (hgt.mpr h2)]
      -- `1/2 - x` is exact.
      have hb : (0.5 - x).toBits = Wasm.IEEE64.sub 0x3FE0000000000000 x.toBits := by
        rw [F64Bits.toBits_sub, q5]
      obtain ⟨hdf, hdv⟩ := sterbenz 0x3FE0000000000000 x.toBits f5 hf
        (by rw [v5, hV]; exact mul_nonneg (by norm_num) hV0'.le)
        (by rw [v5, hV, abs_of_pos hV0']; norm_num; linarith)
        (by rw [v5, hV, abs_of_pos hV0']; norm_num; linarith) (by decide)
      rw [v5, hV] at hdv
      have hgap := below_half x.toBits (by rw [hV, abs_of_pos hV0']; linarith)
        (by rw [hV, abs_of_pos hV0']; exact hV1)
      rw [hV, abs_of_pos hV0'] at hgap
      have hs' : (0.5 - x).toBits.toNat < 2 ^ 63 := by
        rw [hb]
        have h0 : 0 < value (Wasm.IEEE64.sub 0x3FE0000000000000 x.toBits) := by
          rw [hdv]; linarith
        by_contra hc
        push Not at hc
        have hsg : Wasm.IEEE64.sign (Wasm.IEEE64.sub 0x3FE0000000000000 x.toBits) = true := by
          unfold Wasm.IEEE64.sign; simp only [decide_eq_true_eq]; exact hc
        have := sign_true _ hsg
        have := abs_nonneg (value (Wasm.IEEE64.sub 0x3FE0000000000000 x.toBits))
        linarith
      obtain ⟨g1, g2, hlo, hup, ht, har, -, -⟩ := product_float (0.5 - x) (1 / 2 - V) hs'
        (by rw [hb]; exact hdf) (by rw [hb, hdv]) (by linarith) (by linarith)
      have hW0 : 0 < 1 / 2 - V := by linarith
      have hX1 : |value (Sinpi.piProduct (0.5 - x)).1.toBits| ≤ 78541 / 100000 := by
        have : |Real.pi * (1 / 2 - V)| ≤ 0.7854 := by
          rw [abs_of_pos (mul_pos Real.pi_pos hW0)]
          have : Real.pi * (1 / 2 - V) ≤ 3.1416 * (1 / 4) :=
            mul_le_mul hpi.le (by linarith) hW0.le (by norm_num)
          linarith
        have : |Real.pi * (1 / 2 - V)| * (1 + 1 / 2 ^ 50) ≤ 0.7854 * (1 + 1 / 2 ^ 50) :=
          mul_le_mul_of_nonneg_right this (by norm_num)
        have : (0.7854 : ℝ) * (1 + 1 / 2 ^ 50) ≤ 78541 / 100000 := by norm_num
        linarith
      have hk := kernel_within _ _ true (Real.pi * (1 / 2 - V)) _ g1 g2 rfl hlo hX1 ht har
      simp only [↓reduceIte] at hk
      have hn := neg_within _ _ hk
      have hid : -(-1 / Real.tan (Real.pi * (1 / 2 - V))) = Real.tan (Real.pi * V) := by
        rw [show Real.pi * (1 / 2 - V) = Real.pi / 2 - Real.pi * V by ring,
          Real.tan_pi_div_two_sub, neg_div, neg_neg, one_div, inv_inv]
      rwa [hid] at hn
    · have hq : V = 1 / 4 := by linarith
      rw [c3 (fun h => h1 (hlt.mp h)) (fun h => h2 (hgt.mp h)), q1]
      refine exact_within _ _ (by exact f1) (by rw [v1, hq, show Real.pi * (1 / 4) = Real.pi / 4 by
        ring, Real.tan_pi_div_four]) ?_ ?_
      · rw [hq, show Real.pi * (1 / 4) = Real.pi / 4 by ring, Real.tan_pi_div_four]; norm_num
      · rw [hq, show Real.pi * (1 / 4) = Real.pi / 4 by ring, Real.tan_pi_div_four]; norm_num

#print axioms kernel_tanpi

end Library.Numerics.Float64.Sinpi.SinpiTanKernel
