import Library.Numerics.Float64.Sinpi.SinpiTanKernel

/-!
The reflections of `Sinpi` on `[0, 1)`: for a positive `a` from `1/4` below `1/2`, `0.5 - a` is
exact and lies from `2 ^ -54` to `1/4`; from `1/2` below `3/4`, `a - 0.5` is exact; and from
`3/4` below 1, `1.0 - a` is exact and lies from `2 ^ -53` to `1/4`.  With the identities
`cos (π/2 - θ) = sin θ` and their relatives, each reflected kernel gives `sin`, `cos`, or `tan` of
`π a`.
-/

namespace Library.Numerics.Float64.Sinpi.SinpiReflect

open CodeLib.IEEE64 LeanExe.ProofKit SinpiProduct SinpiKernels SinpiTanKernel Library.Numerics.Float64.Tan.TanWith
  Library.Numerics.Float64.Tan.TanBigWords Library.Numerics.Float64.Tan.TanTrunc Library.Numerics.Float64.Trig.TrigSinCos

set_option exponentiation.threshold 1200

theorem three_quarter : value (0x3FE8000000000000 : UInt64) = 3 / 4 ∧
    Finite (0x3FE8000000000000 : UInt64) := by
  refine ⟨?_, by unfold CodeLib.IEEE64.Finite; decide⟩
  rw [Library.Numerics.Float64.Trig.TrigReduce.value_word _ 3 2 (by norm_num) (by decide +kernel)]
  norm_num

/-- A positive word has `toNat` below `2 ^ 63`. -/
theorem pos_toNat (w : UInt64) (h : 0 < value w) : w.toNat < 2 ^ 63 := by
  by_contra hc
  push Not at hc
  have hsg : Wasm.IEEE64.sign w = true := by
    unfold Wasm.IEEE64.sign
    simp only [decide_eq_true_eq]
    exact hc
  have := sign_true w hsg
  have := abs_nonneg (value w)
  linarith

/-- A positive word from `1/2` below 1 lies at least `2 ^ -53` below 1 and is a multiple of
`2 ^ -53` away from `1/2`. -/
theorem below_one (v : UInt64) (h0 : 1 / 2 ≤ |value v|) (h1 : |value v| < 1) :
    |value v| ≤ 1 - 1 / 2 ^ 53 ∧ (|value v| = 1 / 2 ∨ 1 / 2 + 1 / 2 ^ 53 ≤ |value v|) := by
  have hl := F64SignedNearestSum.grid_lower v
  have hb := F64SignedNearestSum.grid_bound v
  have he1 : 1074 ≤ 53 + (Wasm.IEEE64.exponent v - 1) := by
    by_contra hc
    have : (2 : ℝ) ^ (53 + (Wasm.IEEE64.exponent v - 1)) / 2 ^ 1074 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity), show (1 : ℝ) / 2 * 2 ^ 1074 = 2 ^ 1073 by norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have he0 : 1 ≤ Wasm.IEEE64.exponent v := by omega
  have he2 : 52 + (Wasm.IEEE64.exponent v - 1) ≤ 1073 := by
    by_contra hc
    have : (1 : ℝ) ≤ 2 ^ (52 + (Wasm.IEEE64.exponent v - 1)) / 2 ^ 1074 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [hl he0]
  obtain ⟨m, hm, -⟩ := mag_split v
  have he : Wasm.IEEE64.exponent v - 1 = 1021 := by omega
  rw [he] at hm
  rw [F64RoundNearest.abs_value, hm] at h0 h1 ⊢
  push_cast at h0 h1 ⊢
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at h0
  have hm1 : (m : ℝ) < 2 ^ 53 := by linarith
  have hm0 : (2 : ℝ) ^ 52 ≤ m := by linarith
  have hmn : m < 2 ^ 53 := by exact_mod_cast hm1
  have hmn0 : 2 ^ 52 ≤ m := by exact_mod_cast hm0
  constructor
  · have : m + 1 ≤ 2 ^ 53 := hmn
    have : (m : ℝ) + 1 ≤ 2 ^ 53 := by exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    linarith
  · rcases Nat.eq_or_lt_of_le hmn0 with h | h
    · left
      rw [← h]
      norm_num
    · right
      have : 2 ^ 52 + 1 ≤ m := h
      have : (2 : ℝ) ^ 52 + 1 ≤ m := by exact_mod_cast this
      rw [le_div_iff₀ (by positivity)]
      linarith

/-- `0.5 - a` for `a` from `1/4` below `1/2`. -/
theorem half_sub (a : Float) (A : ℝ) (hf : Finite a.toBits) (hA : value a.toBits = A)
    (h0 : 1 / 4 ≤ A) (h1 : A < 1 / 2) :
    Finite (0.5 - a).toBits ∧ value (0.5 - a).toBits = 1 / 2 - A ∧
      (0.5 - a).toBits.toNat < 2 ^ 63 ∧ 1 / 2 ^ 54 ≤ 1 / 2 - A := by
  obtain ⟨-, q5, -, -, v5, -, -, f5, -⟩ := quarter_facts
  have hA0 : 0 < A := by linarith
  have hb : (0.5 - a).toBits = Wasm.IEEE64.sub 0x3FE0000000000000 a.toBits := by
    rw [F64Bits.toBits_sub, q5]
  obtain ⟨hdf, hdv⟩ := sterbenz 0x3FE0000000000000 a.toBits f5 hf
    (by rw [v5, hA]; exact mul_nonneg (by norm_num) hA0.le)
    (by rw [v5, hA, abs_of_pos hA0]; norm_num; linarith)
    (by rw [v5, hA, abs_of_pos hA0]; norm_num; linarith) (by decide)
  rw [v5, hA] at hdv
  have hgap := below_half a.toBits (by rw [hA, abs_of_pos hA0]; linarith)
    (by rw [hA, abs_of_pos hA0]; exact h1)
  rw [hA, abs_of_pos hA0] at hgap
  rw [hb]
  exact ⟨hdf, hdv, pos_toNat _ (by rw [hdv]; linarith), by linarith⟩

/-- `a - 0.5` for `a` from `1/2` below `3/4`. -/
theorem sub_half (a : Float) (A : ℝ) (hf : Finite a.toBits) (hA : value a.toBits = A)
    (h0 : 1 / 2 ≤ A) (h1 : A < 3 / 4) :
    Finite (a - 0.5).toBits ∧ value (a - 0.5).toBits = A - 1 / 2 ∧
      (A = 1 / 2 ∨ ((a - 0.5).toBits.toNat < 2 ^ 63 ∧ 1 / 2 ^ 54 ≤ A - 1 / 2)) := by
  obtain ⟨-, q5, -, -, v5, -, -, f5, -⟩ := quarter_facts
  have hA0 : 0 < A := by linarith
  have hb : (a - 0.5).toBits = Wasm.IEEE64.sub a.toBits 0x3FE0000000000000 := by
    rw [F64Bits.toBits_sub, q5]
  have hex : Wasm.IEEE64.exponent a.toBits ≤ 0 + 1023 :=
    Library.Numerics.Float64.Tan.TanOdd.exp_upper a.toBits 0 (by rw [hA, abs_of_pos hA0, pow_zero]; linarith)
  obtain ⟨hdf, hdv⟩ := sterbenz a.toBits 0x3FE0000000000000 hf f5
    (by rw [v5, hA]; exact mul_nonneg hA0.le (by norm_num))
    (by rw [v5, hA, abs_of_pos hA0]; norm_num; linarith)
    (by rw [v5, hA, abs_of_pos hA0]; norm_num; linarith) (by omega)
  rw [v5, hA] at hdv
  have hgap := below_one a.toBits (by rw [hA, abs_of_pos hA0]; exact h0)
    (by rw [hA, abs_of_pos hA0]; linarith)
  rw [hA, abs_of_pos hA0] at hgap
  rw [hb]
  refine ⟨hdf, hdv, ?_⟩
  rcases hgap.2 with h | h
  · exact Or.inl h
  · right
    exact ⟨pos_toNat _ (by rw [hdv]; linarith), by
      have : (1 : ℝ) / 2 ^ 54 ≤ 1 / 2 ^ 53 := by norm_num
      linarith⟩

/-- `1.0 - a` for `a` from `3/4` below 1. -/
theorem one_sub (a : Float) (A : ℝ) (hf : Finite a.toBits) (hA : value a.toBits = A)
    (h0 : 3 / 4 ≤ A) (h1 : A < 1) :
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
  have hgap := below_one a.toBits (by rw [hA, abs_of_pos hA0]; linarith)
    (by rw [hA, abs_of_pos hA0]; exact h1)
  rw [hA, abs_of_pos hA0] at hgap
  rw [hb]
  exact ⟨hdf, hdv, pos_toNat _ (by rw [hdv]; linarith), by
    have : (1 : ℝ) / 2 ^ 54 ≤ 1 / 2 ^ 53 := by norm_num
    linarith⟩

#print axioms below_one
#print axioms half_sub
#print axioms sub_half
#print axioms one_sub

end Library.Numerics.Float64.Sinpi.SinpiReflect
