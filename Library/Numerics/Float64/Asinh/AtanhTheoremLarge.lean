import Library.Numerics.Float64.Asinh.AtanhTheoremSmallCases

/-!
`Asinh.atanh` from `1/2` to 1: the code returns `0.5 log1p ((a + a)/(1 - a))` for `a = |x|`.
`a + a` and `1 - a` are exact (Sterbenz), so the quotient has relative error `2 ^ -53`, and its
term in the bound stays below `1.0002 · 2 ^ -53`.  `2 artanh a ≥ log 3`, so the halved bound lies
below two spacings of `[1/2, 1)`; from a quotient of `2 ^ 53` on, `artanh a ≥ 18` and the binade
`[16, 32)` takes the larger bound of `log1p`.
-/

namespace Library.Numerics.Float64.Asinh.AtanhTheoremLarge
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RelError F64Near Library.Numerics.Float64.Log1p.Log1pTheoremNear
  Log1pTheoremConst AsinhTheoremCompose AsinhTheoremMid AtanhTheoremSmall

set_option exponentiation.threshold 4096

theorem one_value : value (1.0 : Float).toBits = 1 := by
  have h := one_rapprox.2.2
  rw [zero_mul, abs_nonpos_iff, sub_eq_zero] at h
  exact h

/-- **`atanh` from `1/2` to 1**, at `a = |x|`. -/
theorem atanh_large (a : Float) (ha : Finite a.toBits) (h5 : 1 / 2 ≤ value a.toBits)
    (h1 : value a.toBits < 1) :
    F64SignedRounding.WithinSteps 2 (Real.artanh (value a.toBits))
      (0.5 * Log1p.log1p ((a + a) / (1.0 - a))).toBits := by
  set va := value a.toBits with hva
  have hv0 : 0 < va := by linarith
  have hden : 0 < 1 - va := by linarith
  have hne : 1 - va ≠ 0 := hden.ne'
  have hpos : a.toBits.toNat < 2 ^ 63 := by
    have := F64Exact.sign_of_pos a.toBits hv0
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using this
  have hlt : a.toBits.toNat ≤ 0x3FEFFFFFFFFFFFFF := by
    by_contra h
    have h2 := (F64PositiveOrder.value_le_iff (by decide : (0x3FF0000000000000 : UInt64).toNat < 2 ^ 63)
      hpos).mpr (by change 0x3FF0000000000000 ≤ a.toBits.toNat; omega)
    rw [Library.Numerics.Float64.Log1p.Log1pTheorem.word_value (0x3FF0000000000000 : UInt64) 1 (by decide +kernel)] at h2
    push_cast at h2
    linarith
  have hle : va ≤ 1 - 1 / 2 ^ 53 := by
    have h2 := (F64PositiveOrder.value_le_iff hpos
      (by decide : (0x3FEFFFFFFFFFFFFF : UInt64).toNat < 2 ^ 63)).mpr (by
        change a.toBits.toNat ≤ 0x3FEFFFFFFFFFFFFF
        exact hlt)
    rw [Library.Numerics.Float64.Log1p.Log1pTheorem.word_value (0x3FEFFFFFFFFFFFFF : UInt64) (1 - 1 / 2 ^ 53)
      (by decide +kernel)] at h2
    push_cast at h2
    exact h2
  obtain ⟨htf, htv⟩ := add_self_exact a ha
    (by rw [abs_of_pos hv0]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2)])
    (by rw [abs_of_pos hv0]; linarith [(by norm_num : (1 : ℝ) < 2 ^ 900)])
  have hT : RApprox (a + a).toBits (2 * va) 0 := by
    have h := rapprox_self _ htf (by rw [htv]; linarith)
    rwa [htv] at h
  obtain ⟨hdf, hdv⟩ := F64Exact.sub_exact (1.0 : Float).toBits a.toBits one_rapprox.2.1 ha
    (by rw [one_value]; norm_num) hv0 (by rw [one_value]; linarith) (by rw [one_value]; linarith)
    (by rw [one_value]; norm_num) (by linarith [(by norm_num : (1 : ℝ) < 2 ^ 900)])
  rw [← F64Bits.toBits_sub, one_value] at hdv
  rw [← F64Bits.toBits_sub] at hdf
  have hD : RApprox (1.0 - a).toBits (1 - va) 0 := by
    have h := rapprox_self _ hdf (by rw [hdv]; linarith)
    rwa [hdv] at h
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = 2 * va / (1 - va) := ⟨_, rfl⟩
  have hW2 : 2 ≤ W := by
    rw [hW, le_div_iff₀ hden]
    linarith
  have hW54 : W ≤ 2 ^ 54 := by
    rw [hW, div_le_iff₀ hden]
    have : (1 : ℝ) / 2 ^ 53 ≤ 1 - va := by linarith
    have h3 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 ^ 54)
    linarith [(by norm_num : (2 : ℝ) ^ 54 * (1 / 2 ^ 53) = 2)]
  have hq0 := rapprox_div hT hD (by norm_num) (1 / 2 ^ 1000)
    (by
      rw [← hW]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 * 2)])
    (by
      rw [← hW]
      have : (1 + 0) / (1 - 0) * W ≤ 2 ^ 54 := by
        rw [add_zero, sub_zero, div_one, one_mul]
        exact hW54
      linarith [(by norm_num : (2 : ℝ) ^ 54 < 2 ^ 1022)])
  rw [← F64Bits.toBits_div, ← hW] at hq0
  have hq := hq0.mono (ρ' := 10001 / 10000 / 2 ^ 53) (by norm_num)
  obtain ⟨q, hqdef⟩ : ∃ q : Float, q = (a + a) / (1.0 - a) := ⟨_, rfl⟩
  rw [← hqdef] at hq
  rw [← hqdef]
  have hd : |value q.toBits - W| ≤ 10001 / 10000 / 2 ^ 53 * W := hq.2.2
  have hda := abs_le.mp hd
  have hρW : 10001 / 10000 / 2 ^ 53 * W ≤ W / 2 := by linarith
  have hq2 : 1 / 2 ^ 29 ≤ value q.toBits := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 29 ≤ 1)]
  have hρ : (0 : ℝ) ≤ 1 - 10001 / 10000 / 2 ^ 53 := by norm_num
  have hm : 0 < 1 + W * (1 - 10001 / 10000 / 2 ^ 53) := by linarith
  have hLW : Real.log (1 + W) = 2 * Real.artanh va := by
    rw [two_artanh va hv0.le h1, hW, log_W va hv0.le h1]
  -- the argument term
  have hK : 10001 / 10000 / 2 ^ 53 * W / (1 + W * (1 - 10001 / 10000 / 2 ^ 53)) ≤
      10003 / 10000 / 2 ^ 53 := by
    rw [div_le_iff₀ hm]
    linarith
  -- `2 artanh a ≥ log 3`
  have hY3 : 10986 / 10000 ≤ 2 * Real.artanh va := by
    rw [two_artanh va hv0.le h1]
    have l1 : (405465 / 1000000 : ℝ) ≤ Real.log (3 / 2) := by
      have := log_ge (1 / 2) (405465 / 1000000) 8 (by norm_num) (by norm_num) (by decide +kernel)
      push_cast at this
      norm_num at this ⊢
      linarith
    have l2 : Real.log (1 / 2) ≤ -693147 / 1000000 := by
      have := log_le (-1 / 2) (-693147 / 1000000) 8 (by norm_num) (by norm_num) (by decide +kernel)
      push_cast at this
      norm_num at this ⊢
      linarith
    have h3 : Real.log (3 / 2) ≤ Real.log (1 + va) := Real.log_le_log (by norm_num) (by linarith)
    have h4 : Real.log (1 - va) ≤ Real.log (1 / 2) := Real.log_le_log hden (by linarith)
    linarith
  have hYu : 2 * Real.artanh va ≤ 2 ^ 54 := by
    rw [← hLW]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + W)
    linarith
  have hN0 := log1p_near q hq.2.1 hq2
  rcases lt_or_ge (value q.toBits) (2 ^ 53) with c | c
  · rw [errBound_mid _ (by linarith) c] at hN0
    have hN2 := near_compose hN0 hd hm (by linarith) (by linarith)
    rw [hLW] at hN2
    have hN3 := hN2.mono (E' := 133 / 100 / 2 ^ 54 + 10003 / 10000 / 2 ^ 53) (by linarith)
    have hY0 : 0 ≤ 2 * Real.artanh va := by linarith
    have hN4 := hN3.half (by
        rw [abs_of_nonneg hY0]
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 998 + (133 / 100 / 2 ^ 54 + 10003 / 10000 / 2 ^ 53) ≤ 1)])
      (by rw [abs_of_nonneg hY0]; linarith [(by norm_num : (2 : ℝ) ^ 54 + 1 < 2 ^ 1000)])
    rw [show 2 * Real.artanh va / 2 = Real.artanh va by ring] at hN4
    rw [F64Bits.toBits_mul, show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]
    refine hN4.within_two 1022 (by norm_num) (by norm_num) ?_ (by norm_num) ?_
    · rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num),
        abs_of_nonneg (by linarith)]
      linarith [(by norm_num : (2 : ℝ) ^ (1022 + 51) / 2 ^ 1074 +
        (133 / 100 / 2 ^ 54 + 10003 / 10000 / 2 ^ 53) / 2 ≤ 54 / 100)]
    · rw [abs_of_nonneg (by linarith)]
      linarith [(by norm_num : (2 : ℝ) ^ 54 < 2 ^ 1023)]
  · rw [errBound_big _ c] at hN0
    have hN2 := near_compose hN0 hd hm (by linarith) (by linarith)
    rw [hLW] at hN2
    have hN3 := hN2.mono (E' := 6 / 2 ^ 54 + 10003 / 10000 / 2 ^ 53) (by linarith)
    -- `W ≥ 2 ^ 52`, so `2 artanh a ≥ 52 log 2`
    have hW52 : 2 ^ 52 ≤ W := by linarith [hda.2]
    have hY36 : 36 ≤ 2 * Real.artanh va := by
      rw [← hLW]
      have h2 : Real.log ((2 : ℝ) ^ (52 : ℕ)) = (52 : ℕ) * Real.log 2 := Real.log_pow 2 52
      have h3 : Real.log ((2 : ℝ) ^ (52 : ℕ)) ≤ Real.log (1 + W) :=
        Real.log_le_log (by positivity) (by linarith)
      have h4 := Library.Numerics.Float64.Log1p.Log1pTheoremTail.ln2_bounds
      rw [h2] at h3
      push_cast at h3
      linarith [h4.1]
    have hN4 := hN3.half (by
        rw [abs_of_nonneg (by linarith)]
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 998 + (6 / 2 ^ 54 + 10003 / 10000 / 2 ^ 53) ≤ 1)])
      (by rw [abs_of_nonneg (by linarith)]; linarith [(by norm_num : (2 : ℝ) ^ 54 + 1 < 2 ^ 1000)])
    rw [show 2 * Real.artanh va / 2 = Real.artanh va by ring] at hN4
    rw [F64Bits.toBits_mul, show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]
    refine hN4.within_two 1027 (by norm_num) (by norm_num) ?_ (by norm_num) ?_
    · rw [F64PositiveSpacing.boundary_value 1027 (by norm_num) (by norm_num),
        abs_of_nonneg (by linarith)]
      linarith [(by norm_num : (2 : ℝ) ^ (1027 + 51) / 2 ^ 1074 +
        (6 / 2 ^ 54 + 10003 / 10000 / 2 ^ 53) / 2 ≤ 17)]
    · rw [abs_of_nonneg (by linarith)]
      linarith [(by norm_num : (2 : ℝ) ^ 54 < 2 ^ 1023)]

#print axioms atanh_large

end Library.Numerics.Float64.Asinh.AtanhTheoremLarge
