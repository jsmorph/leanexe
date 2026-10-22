import Library.Numerics.Float64.Sinpi.SinpiReflect

/-!
The reflected kernels of `Sinpi` on `[0, 1)`, each against `sin`, `cos`, or `tan` of `π a`: the
four branches of the sine chain, the four pieces of the cosine, and the two of the tangent.  At
`a = 1/2` the sine chain evaluates `kernelCospi 0`, which is exactly 1.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiPieces

open CodeLib.IEEE64 LeanExe.ProofKit SinpiProduct SinpiKernels SinpiTanKernel SinpiReflect
  TanWith TanBigWords TanTrunc TrigSinCos TrigKernelWords

set_option exponentiation.threshold 1200

theorem lt_word (a w : UInt64) (ha : a.toNat < 2 ^ 63) (hw : w.toNat < 2 ^ 63) :
    value a < value w ↔ a.toNat < w.toNat := by
  rw [← not_le, F64PositiveOrder.value_le_iff hw ha, not_le]

/-- The thresholds of the high word of a positive `a`. -/
theorem thresholds (a : Float) (ix : UInt64) (A : ℝ) (hix : ix.toNat = a.toBits.toNat / 2 ^ 32)
    (hs : a.toBits.toNat < 2 ^ 63) (hA : value a.toBits = A) :
    (ix < 0x3fd00000 ↔ A < 1 / 4) ∧ (ix < 0x3fe00000 ↔ A < 1 / 2) ∧
      (ix < 0x3fe80000 ↔ A < 3 / 4) := by
  obtain ⟨-, -, -, v25, v5, -, -, -, -⟩ := quarter_facts
  obtain ⟨v75, -⟩ := three_quarter
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt64.lt_iff_toNat_lt, hix, ← hA, ← v25, lt_word _ _ hs (by decide)]
    show a.toBits.toNat / 2 ^ 32 < 1070596096 ↔ a.toBits.toNat < 4598175219545276416
    omega
  · rw [UInt64.lt_iff_toNat_lt, hix, ← hA, ← v5, lt_word _ _ hs (by decide)]
    show a.toBits.toNat / 2 ^ 32 < 1071644672 ↔ a.toBits.toNat < 4602678819172646912
    omega
  · rw [UInt64.lt_iff_toNat_lt, hix, ← hA, ← v75, lt_word _ _ hs (by decide)]
    show a.toBits.toNat / 2 ^ 32 < 1072168960 ↔ a.toBits.toNat < 4604930618986332160
    omega

/-- `1.0 - a` for `a` from `1/2` below 1. -/
theorem one_sub_half (a : Float) (A : ℝ) (hf : Finite a.toBits) (hA : value a.toBits = A)
    (h0 : 1 / 2 ≤ A) (h1 : A < 1) :
    Finite (1.0 - a).toBits ∧ value (1.0 - a).toBits = 1 - A ∧
      (1.0 - a).toBits.toNat < 2 ^ 63 ∧ 1 / 2 ^ 54 ≤ 1 - A := by
  obtain ⟨-, -, q1, -, -, v1, -, -, f1⟩ := quarter_facts
  have hA0 : 0 < A := by linarith
  have hb : (1.0 - a).toBits = Wasm.IEEE64.sub 0x3FF0000000000000 a.toBits := by
    rw [F64Bits.toBits_sub, q1]
  obtain ⟨hdf, hdv⟩ := sterbenz 0x3FF0000000000000 a.toBits f1 hf
    (by rw [v1, hA]; exact mul_nonneg (by norm_num) hA0.le)
    (by rw [v1, hA, abs_of_pos hA0]; norm_num; linarith)
    (by rw [v1, hA, abs_of_pos hA0]; norm_num; linarith) (by decide)
  rw [v1, hA] at hdv
  have hgap := below_one a.toBits (by rw [hA, abs_of_pos hA0]; exact h0)
    (by rw [hA, abs_of_pos hA0]; exact h1)
  rw [hA, abs_of_pos hA0] at hgap
  rw [hb]
  exact ⟨hdf, hdv, pos_toNat _ (by rw [hdv]; linarith), by
    have : (1 : ℝ) / 2 ^ 54 ≤ 1 / 2 ^ 53 := by norm_num
    linarith⟩

/-- `kernelCospi` of a float with the bits of `+0` is 1. -/
theorem cospi_zero (f : Float) (hf : f.toBits = 0) :
    (Sinpi.kernelCospi f).toBits = 0x3FF0000000000000 := by
  obtain ⟨b1, b2⟩ := product_bits f
  have hp : productW 0 = (0, 0) := by decide +kernel
  have hc : cosW 0 0 = 0x3FF0000000000000 := by decide +kernel
  rw [kernelCospi_eq, kernelCos_bits, b1, b2, hf, hp]
  exact hc

/-- The sine chain on `[2 ^ -54, 1)`. -/
theorem sin_chain (a : Float) (ix : UInt64) (A : ℝ) (hix : ix.toNat = a.toBits.toNat / 2 ^ 32)
    (hs : a.toBits.toNat < 2 ^ 63) (hf : Finite a.toBits) (hA : value a.toBits = A)
    (hA0 : 1 / 2 ^ 54 ≤ A) (hA1 : A < 1) :
    F64SignedRounding.WithinSteps 1 (Real.sin (Real.pi * A))
      (if ix < 0x3fd00000 then Sinpi.kernelSinpi a
        else if ix < 0x3fe00000 then Sinpi.kernelCospi (0.5 - a)
        else if ix < 0x3fe80000 then Sinpi.kernelCospi (a - 0.5)
        else Sinpi.kernelSinpi (1.0 - a)).toBits := by
  obtain ⟨c1, c2, c3⟩ := thresholds a ix A hix hs hA
  by_cases h1 : A < 1 / 4
  · rw [if_pos (c1.mpr h1)]
    exact (kernel_pair a A hs hf hA hA0 h1.le).1
  rw [if_neg (fun h => h1 (c1.mp h))]
  by_cases h2 : A < 1 / 2
  · rw [if_pos (c2.mpr h2)]
    obtain ⟨df, dv, ds, d0⟩ := half_sub a A hf hA (by linarith) h2
    have := (kernel_pair (0.5 - a) (1 / 2 - A) ds df dv d0 (by linarith)).2
    rwa [show Real.pi * (1 / 2 - A) = Real.pi / 2 - Real.pi * A by ring,
      Real.cos_pi_div_two_sub] at this
  rw [if_neg (fun h => h2 (c2.mp h))]
  by_cases h3 : A < 3 / 4
  · rw [if_pos (c3.mpr h3)]
    obtain ⟨df, dv, dcase⟩ := sub_half a A hf hA (by linarith) h3
    rcases dcase with hq | ⟨ds, d0⟩
    · -- `a = 1/2`: `a - 0.5` is `+0`, and the kernel gives exactly 1.
      obtain ⟨-, -, -, -, v5, -, -, -, -⟩ := quarter_facts
      have ha : a.toBits = 0x3FE0000000000000 := by
        apply UInt64.toNat_inj.mp
        have e1 := (F64PositiveOrder.value_le_iff (left := a.toBits)
          (right := 0x3FE0000000000000) hs (by decide)).mp (le_of_eq (by rw [hA, v5, hq]))
        have e2 := (F64PositiveOrder.value_le_iff (left := 0x3FE0000000000000)
          (right := a.toBits) (by decide) hs).mp (le_of_eq (by rw [hA, v5, hq]))
        omega
      have hz : (a - 0.5).toBits = 0 := by
        rw [F64Bits.toBits_sub, ha, (quarter_facts).2.1]
        decide +kernel
      rw [cospi_zero _ hz]
      refine exact_within _ _ (by unfold CodeLib.IEEE64.Finite; decide) ?_ ?_ ?_
      · rw [hq, show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
        exact (quarter_facts).2.2.2.2.2.1
      · rw [hq, show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]; norm_num
      · rw [hq, show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]; norm_num
    · have := (kernel_pair (a - 0.5) (A - 1 / 2) ds df dv d0 (by linarith)).2
      rwa [show Real.pi * (A - 1 / 2) = Real.pi * A - Real.pi / 2 by ring,
        Real.cos_sub_pi_div_two] at this
  rw [if_neg (fun h => h3 (c3.mp h))]
  obtain ⟨df, dv, ds, d0⟩ := one_sub a A hf hA (by linarith) hA1
  have := (kernel_pair (1.0 - a) (1 - A) ds df dv d0 (by linarith)).1
  rwa [show Real.pi * (1 - A) = Real.pi - Real.pi * A by ring, Real.sin_pi_sub] at this

/-- The pieces of the cosine. -/
theorem cos_pieces (a : Float) (A : ℝ) (hs : a.toBits.toNat < 2 ^ 63) (hf : Finite a.toBits)
    (hA : value a.toBits = A) (hA0 : 1 / 2 ^ 54 ≤ A) (hA1 : A < 1) :
    (A < 1 / 4 → F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * A))
      (Sinpi.kernelCospi a).toBits) ∧
    (1 / 4 ≤ A → A < 1 / 2 → F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * A))
      (Sinpi.kernelSinpi (0.5 - a)).toBits) ∧
    (1 / 2 < A → A < 3 / 4 → F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * A))
      (-Sinpi.kernelSinpi (a - 0.5)).toBits) ∧
    (3 / 4 ≤ A → F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * A))
      (-Sinpi.kernelCospi (1.0 - a)).toBits) := by
  refine ⟨fun h1 => (kernel_pair a A hs hf hA hA0 h1.le).2, fun h1 h2 => ?_,
    fun h1 h2 => ?_, fun h1 => ?_⟩
  · obtain ⟨df, dv, ds, d0⟩ := half_sub a A hf hA h1 h2
    have := (kernel_pair (0.5 - a) (1 / 2 - A) ds df dv d0 (by linarith)).1
    rwa [show Real.pi * (1 / 2 - A) = Real.pi / 2 - Real.pi * A by ring,
      Real.sin_pi_div_two_sub] at this
  · obtain ⟨df, dv, dcase⟩ := sub_half a A hf hA h1.le h2
    rcases dcase with hq | ⟨ds, d0⟩
    · exact absurd hq (ne_of_gt h1)
    · have := neg_within _ _ (kernel_pair (a - 0.5) (A - 1 / 2) ds df dv d0 (by linarith)).1
      rwa [show Real.pi * (A - 1 / 2) = Real.pi * A - Real.pi / 2 by ring,
        Real.sin_sub_pi_div_two, neg_neg] at this
  · obtain ⟨df, dv, ds, d0⟩ := one_sub a A hf hA h1 hA1
    have := neg_within _ _ (kernel_pair (1.0 - a) (1 - A) ds df dv d0 (by linarith)).2
    rwa [show Real.pi * (1 - A) = Real.pi - Real.pi * A by ring, Real.cos_pi_sub,
      neg_neg] at this

/-- The pieces of the tangent. -/
theorem tan_pieces (a : Float) (A : ℝ) (hs : a.toBits.toNat < 2 ^ 63) (hf : Finite a.toBits)
    (hA : value a.toBits = A) (hA0 : 1 / 2 ^ 54 ≤ A) (hA1 : A < 1) :
    (A < 1 / 2 → F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * A))
      (Sinpi.kernelTanpi a).toBits) ∧
    (1 / 2 < A → F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * A))
      (-Sinpi.kernelTanpi (1.0 - a)).toBits) := by
  refine ⟨fun h1 => kernel_tanpi a A hs hf hA hA0 h1, fun h1 => ?_⟩
  obtain ⟨df, dv, ds, d0⟩ := one_sub_half a A hf hA h1.le hA1
  have := neg_within _ _ (kernel_tanpi (1.0 - a) (1 - A) ds df dv d0 (by linarith))
  rwa [show Real.pi * (1 - A) = Real.pi - Real.pi * A by ring, Real.tan_pi_sub,
    neg_neg] at this

#print axioms sin_chain
#print axioms cos_pieces
#print axioms tan_pieces

end Library.Numerics.Float64.Sinpi.SinpiPieces
