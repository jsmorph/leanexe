import Verified.Examples.SinpiCos

/-!
`Sinpi.cospi` from 1 on: within one step of `cos (π x)` for every finite `x` with `|x| ≥ 1`.
-/

namespace Verified.Examples.SinpiCosFloor

open CodeLib.IEEE64 LeanExe.ProofKit TrigSinCos TanBigWords TanTrunc TanWith SinpiBits
  SinpiFloor SinpiPieces SinpiCommon SinpiReflect SinpiSin SinpiKernels SinpiTanKernel SinpiCos

set_option exponentiation.threshold 1200

/-- The fraction step shared by `cospi` and `tanpi`: the floor of `|x|` and the exact fraction. -/
theorem floor_frac (x : Float) (hxf : Finite x.toBits) (h1 : 1 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 2 ^ 52) :
    ∃ N : Nat, 1 ≤ N ∧ N < 2 ^ 52 ∧
      value (Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff)
        (x.toBits &&& 0xFFFFFFFF)).1.toBits = N ∧
      Finite (Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff)
        (x.toBits &&& 0xFFFFFFFF)).1.toBits ∧
      (30 < (Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff) (x.toBits &&& 0xFFFFFFFF)).2.toNat →
        2 ^ 31 ≤ N) ∧
      Finite (x.abs - (Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff)
        (x.toBits &&& 0xFFFFFFFF)).1).toBits ∧
      value (x.abs - (Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff)
        (x.toBits &&& 0xFFFFFFFF)).1).toBits = |value x.toBits| - N ∧
      ((|value x.toBits| = N ∧ (x.abs - (Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff)
        (x.toBits &&& 0xFFFFFFFF)).1).toBits = 0) ∨
       (N + 1 / 2 ^ 52 ≤ |value x.toBits| ∧ |value x.toBits| < N + 1 ∧
        (x.abs - (Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff)
          (x.toBits &&& 0xFFFFFFFF)).1).toBits.toNat < 2 ^ 63)) := by
  obtain ⟨hs, hf, hv, hn, hix, hlx⟩ := abs_facts x hxf
  have hpos : 0 < value x.abs.toBits := by rw [hv]; linarith
  have he1 : 1023 ≤ Wasm.IEEE64.exponent x.abs.toBits := by
    have := TrigNearest.grid_bound x.abs.toBits
    rw [abs_of_pos hpos, hv] at this
    by_contra hc
    have : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent x.abs.toBits - 1)) / 2 ^ 1074 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have he2 : Wasm.IEEE64.exponent x.abs.toBits ≤ 1074 := by
    have := TrigNearest.grid_lower x.abs.toBits (by omega)
    rw [abs_of_pos hpos, hv] at this
    by_contra hc
    have : (2 : ℝ) ^ 52 ≤ 2 ^ (52 + (Wasm.IEEE64.exponent x.abs.toBits - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨hj0, hflb⟩ := ffloor_bits x.abs.toBits _ _ hs hix hlx he1 he2
  generalize Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff) (x.toBits &&& 0xFFFFFFFF) = P
    at hj0 hflb ⊢
  obtain ⟨fl, j0⟩ := P
  dsimp only at hj0 hflb ⊢
  obtain ⟨hflf, -, N, hNv, hN1, hN52, hNl, hNu, hNcase⟩ :=
    floor_spec x.abs.toBits fl.toBits hs he1 he2 hflb
  rw [hv] at hNl hNu hNcase
  have hfl0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hdf, hdv⟩ := sterbenz x.abs.toBits fl.toBits hf hflf
    (by rw [hNv, hv]; exact mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    (by rw [hNv, hv, abs_of_pos hfl0, abs_abs]; linarith)
    (by rw [hNv, hv, abs_of_pos hfl0, abs_abs]
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        linarith)
    (by omega)
  rw [hNv, hv] at hdv
  have hab : (x.abs - fl).toBits = Wasm.IEEE64.sub x.abs.toBits fl.toBits :=
    F64Bits.toBits_sub _ _
  refine ⟨N, hN1, hN52, hNv, hflf, ?_, by rw [hab]; exact hdf, by rw [hab, hdv], ?_⟩
  · intro hj
    rw [hj0] at hj
    have := TrigNearest.grid_lower x.abs.toBits (by omega)
    rw [abs_of_pos hpos, hv] at this
    have h31 : (2 : ℝ) ^ 31 ≤
        2 ^ (52 + (Wasm.IEEE64.exponent x.abs.toBits - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have : (2 : ℝ) ^ 31 < N + 1 := by linarith
    have : 2 ^ 31 < N + 1 := by exact_mod_cast this
    omega
  rcases hNcase with heq | hgt
  · left
    refine ⟨heq, ?_⟩
    rw [hab]
    refine sub_self_zero _ _ hf hflf (by
      unfold Wasm.IEEE64.sign
      simp only [decide_eq_false_iff_not, not_le]
      exact hs) ?_
    have h1' : (Wasm.IEEE64.scaledValue x.abs.toBits : ℝ) =
        Wasm.IEEE64.scaledValue fl.toBits := by
      have e1 := TrigSmall.value_of_scaled x.abs.toBits
      have e2 := TrigSmall.value_of_scaled fl.toBits
      rw [hv, heq] at e1
      rw [hNv] at e2
      have : (Wasm.IEEE64.scaledValue x.abs.toBits : ℝ) / 2 ^ 1074 =
          (Wasm.IEEE64.scaledValue fl.toBits : ℝ) / 2 ^ 1074 := by rw [← e1, ← e2]
      exact (div_left_inj' (by positivity)).mp this
    exact_mod_cast h1'
  · right
    have h52 : (0 : ℝ) < 1 / 2 ^ 52 := by positivity
    exact ⟨hgt, hNu, pos_toNat _ (by rw [hab, hdv]; linarith)⟩

theorem ge_of_not_lt (a b : UInt64) (h : ¬ a < b) : b ≤ a := by
  rw [UInt64.lt_iff_toNat_lt] at h
  rw [UInt64.le_iff_toNat_le]
  omega

/-- `Float` equality with `0.5` on a finite word. -/
theorem beq_half (a : Float) (hf : Finite a.toBits) :
    (a == 0.5) = decide (value a.toBits = 1 / 2) := by
  obtain ⟨-, q5, -, -, v5, -, -, f5, -⟩ := quarter_facts
  have h := feq_iff a 0.5 hf (by rw [q5]; exact f5)
  rw [q5, v5] at h
  rw [Bool.eq_iff_iff, h, decide_eq_true_iff]

/-- The high word of a positive fraction word against 0 and the quarter thresholds. -/
theorem frac_high (a : Float) (F : ℝ) (hs : a.toBits.toNat < 2 ^ 63) (hA : value a.toBits = F)
    (hF : 1 / 2 ^ 52 ≤ F) : (a.toBits >>> 32 == 0) = false := by
  have hix : (a.toBits >>> 32).toNat = a.toBits.toNat / 2 ^ 32 := by
    rw [TrigWords.shr_toNat]; rfl
  rcases Bool.eq_false_or_eq_true (a.toBits >>> 32 == 0) with h | h
  · exfalso
    have h' : a.toBits >>> 32 = 0 := by simpa using h
    have := congrArg UInt64.toNat h'
    rw [hix, UInt64.toNat_zero] at this
    have hlt : a.toBits.toNat < (0x3CB0000000000000 : UInt64).toNat := by
      show _ < 4372995238176751616
      omega
    have hval := F64PositiveOrder.value_strict (by decide) hlt
    have : value (0x3CB0000000000000 : UInt64) = 1 / 2 ^ 52 := by
      rw [TrigReduce.value_word _ 1 52 (by norm_num) (by decide +kernel)]; norm_num
    rw [this, hA] at hval
    linarith
  · exact h

/-- `cospi` from 1 below `2 ^ 52`. -/
theorem cospi_floor (x : Float) (hxf : Finite x.toBits) (h1 : 1 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 2 ^ 52) :
    F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * value x.toBits))
      (Sinpi.cospi x).toBits := by
  obtain ⟨-, -, -, -, hix, -⟩ := abs_facts x hxf
  obtain ⟨c1, -, c52, -⟩ := abs_thresholds x hxf
  obtain ⟨o1, on1, vn1, fn1⟩ := one_negOne
  obtain ⟨-, -, -, -, -, v1, -, -, f1⟩ := quarter_facts
  obtain ⟨N, hN1, hN52, hNv, hflf, hj, hdf, hdv, hcase⟩ := floor_frac x hxf h1 h2
  rw [cos_abs_pi]
  unfold Sinpi.cospi
  dsimp only
  rw [ax_abs, if_neg (fun h' => by linarith [c1.mp h']), if_pos (c52.mpr h2)]
  generalize Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff) (x.toBits &&& 0xFFFFFFFF) = P at *
  obtain ⟨fl, j0⟩ := P
  dsimp only at *
  have hodd := oddPart_spec fl j0 N hflf hNv hN1 (by omega) hj
  have hshift := cos_shift (|value x.toBits| - N) N
  rw [show (N : ℝ) + (|value x.toBits| - N) = |value x.toBits| by ring] at hshift
  have hff : ¬((false : Bool) = true) := by decide
  rcases hcase with ⟨heq, hz⟩ | ⟨hgt, hlt, ha63⟩
  · -- An integer: the result is `±1`.
    have hb : (x.abs - fl == 0.5) = false := by
      rw [beq_half _ hdf, hdv, heq, sub_self]; simp
    rw [hb, Bool.and_false, if_neg hff, hz, show (0 : UInt64) >>> 32 = 0 by decide,
      if_pos (show (0 : UInt64) < 0x3fd00000 by decide),
      if_pos (show ((0 : UInt64) == 0) = true by decide), hodd, hshift, heq, sub_self, mul_zero,
      Real.cos_zero]
    by_cases hp : N % 2 = 1
    · rw [if_pos hp, decide_eq_true hp, if_pos rfl, on1]
      exact pm_one _ _ fn1 vn1 (by norm_num)
    · rw [if_neg hp, decide_eq_false hp, if_neg hff, o1]
      exact pm_one _ _ f1 v1 (by norm_num)
  · set F := |value x.toBits| - N with hFdef
    have hF0 : 1 / 2 ^ 52 ≤ F := by rw [hFdef]; linarith
    have hF1 : F < 1 := by rw [hFdef]; linarith
    have hpcs := cos_pieces (x.abs - fl) F ha63 hdf hdv (le_trans (by norm_num) hF0) hF1
    obtain ⟨t1, t2, t3⟩ := thresholds (x.abs - fl) ((x.abs - fl).toBits >>> 32) F
      (by rw [TrigWords.shr_toNat]; rfl) ha63 hdv
    by_cases hh : F = 1 / 2
    · -- An integer plus `1/2`: the result is `+0`.
      have hb : (x.abs - fl == 0.5) = true := by rw [beq_half _ hdf, hdv, hh]; simp
      rw [hb, Bool.and_true, decide_eq_true (ge_of_not_lt _ _ (fun h' => by linarith [t2.mp h'])),
        decide_eq_true (t3.mpr (by linarith)), if_pos (show (true && true) = true from rfl),
        hshift, hh,
        show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.cos_pi_div_two, neg_zero, ite_self,
        (zero_bits').1]
      exact TrigTiny.zero_step _ (by decide)
    · have hb : (x.abs - fl == 0.5) = false := by rw [beq_half _ hdf, hdv]; simpa using hh
      rw [hb, Bool.and_false, if_neg hff, frac_high _ F ha63 hdv hF0, hodd]
      have hc : F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * F))
          (if (x.abs - fl).toBits >>> 32 < 0x3fd00000 then
            (if false = true then (1.0 : Float) else Sinpi.kernelCospi (x.abs - fl))
          else if (x.abs - fl).toBits >>> 32 < 0x3fe00000 then
            Sinpi.kernelSinpi (0.5 - (x.abs - fl))
          else if (x.abs - fl).toBits >>> 32 < 0x3fe80000 then
            -Sinpi.kernelSinpi ((x.abs - fl) - 0.5)
          else -Sinpi.kernelCospi (1.0 - (x.abs - fl))).toBits := by
        by_cases hq : F < 1 / 4
        · rw [if_pos (t1.mpr hq), if_neg hff]
          exact hpcs.1 hq
        rw [if_neg (fun h' => hq (t1.mp h'))]
        by_cases hq2 : F < 1 / 2
        · rw [if_pos (t2.mpr hq2)]
          exact hpcs.2.1 (not_lt.mp hq) hq2
        rw [if_neg (fun h' => hq2 (t2.mp h'))]
        by_cases hq3 : F < 3 / 4
        · rw [if_pos (t3.mpr hq3)]
          exact hpcs.2.2.1 (lt_of_le_of_ne (not_lt.mp hq2) (Ne.symm hh)) hq3
        rw [if_neg (fun h' => hq3 (t3.mp h'))]
        exact hpcs.2.2.2 (not_lt.mp hq3)
      by_cases hp : N % 2 = 1
      · rw [hshift, if_pos hp, decide_eq_true hp, if_pos rfl]
        exact neg_within _ _ hc
      · rw [hshift, if_neg hp, decide_eq_false hp, if_neg hff]
        exact hc

#print axioms cospi_floor

end Verified.Examples.SinpiCosFloor
