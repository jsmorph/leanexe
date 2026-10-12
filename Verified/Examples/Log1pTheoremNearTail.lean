import Verified.Examples.Log1pTheoremTail

/-!
Error bounds of `Log1p.log1pTail` for `x ≥ 0`, in the form `F64Near.Near`: the exact value of the
last operation lies within `E` of `log (1 + x)`, and the result is its nearest word.  For `K = 0`
the bound is `1.74 · 2 ^ -53 x² + 2 ^ -59 x` up to `x = 0.285` and `0.65 · 2 ^ -54` above.  For
`K ≥ 1` the bound comes from `finish_s_near`, `finish_q_near`, and `finish_z_near`; the case
`K = 1`, `f < -0.175` splits at `f = -0.2501` and `f = -0.2199`, where `|G|` falls below `1/4`, so
that the bound drops from `0.85 · 2 ^ -54` to `0.76` and `0.43 · 2 ^ -54`.  `K ≥ 2` and `f ≥ -0.175`
give `1.33 · 2 ^ -54`.
-/

namespace Verified.Examples.Log1pTheoremNearTail
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64Near PolyBound Log1pTheoremBranches
  Log1pTheoremCore Log1pTheoremConst Log1pTheoremK0 Log1pTheoremTail

set_option exponentiation.threshold 4096

/-- `K = 0`, `2 ^ -30 ≤ x ≤ 0.285`. -/
theorem k0_near_low (f : Float) (hf : Finite f.toBits) (hv1 : 1 / 2 ^ 30 ≤ value f.toBits)
    (hv2 : value f.toBits ≤ 285 / 1000) :
    Near (f - (hfsqOf f - POf f)).toBits (Real.log (1 + value f.toBits))
      (174 / 100 / 2 ^ 53 * value f.toBits ^ 2 + value f.toBits / 2 ^ 59) := by
  set v := value f.toBits with hvdef
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv1
  have hσ : |v| = v := abs_of_pos hv0
  have hc := core_P2 f hf (by rw [hσ]; linarith) (by rw [hσ]; linarith) (by linarith)
  have hX := x_approx f (285 / 1000) _ _ _ _ (by rw [hσ]; linarith) hc.1 hc.2 (by norm_num)
  have hs := sstar_abs v 2 (by norm_num) (by linarith)
  have hs1 : |sStar v| ≤ 1716 / 10000 := by
    refine hs.trans ?_
    rw [div_le_iff₀ (by norm_num), hσ]
    linarith
  have hcl := k0_close f hX (by linarith) hs1
  have hlog : v / (1 + v) ≤ Real.log (1 + v) := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + v)
    rw [show v / (1 + v) = 1 - (1 + v)⁻¹ by field_simp; ring]
    exact this
  have hlogu : Real.log (1 + v) ≤ v := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + v)
    linarith
  have hy : v / (1285 / 1000) ≤ Real.log (1 + v) := by
    have h1 : v / (1285 / 1000) ≤ v / (1 + v) :=
      div_le_div_of_nonneg_left hv0.le (by linarith) (by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
  have hE : 174 / 100 / 2 ^ 53 * v ^ 2 + v / 2 ^ 59 ≤ v / 2 ^ 50 := by
    have : v ^ 2 ≤ v := by nlinarith
    have h1 : 174 / 100 / 2 ^ 53 * v ^ 2 ≤ 174 / 100 / 2 ^ 53 * v :=
      mul_le_mul_of_nonneg_left this (by norm_num)
    have h2 : 174 / 100 / 2 ^ 53 * v + v / 2 ^ 59 ≤ v / 2 ^ 50 := by
      have : (174 / 100 / 2 ^ 53 + 1 / 2 ^ 59 : ℝ) ≤ 1 / 2 ^ 50 := by norm_num
      nlinarith
    linarith
  refine near_sub (approx_self f.toBits hf) hX _ _ (hcl.trans ?_) ?_ ?_
  · have hk : (5001 / 10000 / 2 ^ 53 + 11289 / 5000 / 2 ^ 53 * (285 / 1000) +
        (1 / 2 + 209 / 625 * (285 / 1000) + (5001 / 10000 / 2 ^ 53 + 11289 / 5000 / 2 ^ 53 *
          (285 / 1000))) / 2 ^ 53 : ℝ) ≤ 174 / 100 / 2 ^ 53 := by norm_num
    have hvv : |v| * |v| = v ^ 2 := by rw [hσ]; ring
    have h1 := mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ |v| * |v|)
    have h2 : |sStar v| * ((93 / 128) / 2 ^ 58) ≤ v / 2 * ((93 / 128) / 2 ^ 58) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [hσ] at hs
      exact hs
    have h3 : v / 2 * ((93 / 128) / 2 ^ 58) ≤ v / 2 ^ 59 := by
      have : (0 : ℝ) ≤ v * (1 / 2 ^ 59 - 93 / 128 / 2 ^ 59) := by
        apply mul_nonneg hv0.le
        norm_num
      linarith
    rw [hvv] at h1 ⊢
    linarith
  · rw [abs_of_nonneg hlog0]
    have : v / 2 ^ 50 < v / (1285 / 1000) :=
      div_lt_div_of_pos_left hv0 (by norm_num) (by norm_num)
    linarith
  · rw [abs_of_nonneg hlog0]
    have : v / 2 ^ 50 ≤ v := div_le_self hv0.le (by norm_num)
    have h2 : (1 : ℝ) < 2 ^ 1023 := one_lt_pow₀ (by norm_num) (by norm_num)
    linarith

/-- `K = 0`, `0.285 ≤ x ≤ 0.41422`. -/
theorem k0_near_high (f : Float) (hf : Finite f.toBits) (hv1 : 285 / 1000 ≤ value f.toBits)
    (hv2 : value f.toBits ≤ 41422 / 100000) :
    Near (f - (hfsqOf f - POf f)).toBits (Real.log (1 + value f.toBits)) ((13 / 20) / 2 ^ 54) := by
  set v := value f.toBits with hvdef
  have hσ : |v| = v := abs_of_pos (by linarith)
  have hc := core_P3 f hf (by rw [hσ]; linarith) (by rw [hσ]; linarith) (by linarith)
  have hX := x_approx f (41422 / 100000) _ _ _ _ (by rw [hσ]; linarith) hc.1 hc.2 (by norm_num)
  have hs := sstar_abs v (2285 / 1000) (by norm_num) (by linarith)
  have hs1 : |sStar v| ≤ 1716 / 10000 := sstar_le v (by linarith) hv2
  have hcl := k0_close f hX (by linarith) hs1
  have hl0 := log_ge (285 / 1000) (2507 / 10000) 6 (by norm_num) (by norm_num) (by decide +kernel)
  have hl : (2507 / 10000 : ℝ) ≤ Real.log (1 + v) := by
    push_cast at hl0
    exact hl0.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlu := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + v)
  refine near_sub (approx_self f.toBits hf) hX _ ((13 / 20) / 2 ^ 54) (hcl.trans ?_) ?_ ?_
  · exact abs_err _ |v| _ _ (41422 / 100000) (2285 / 1000) _ (by positivity) (abs_nonneg v)
      (by rw [hσ]; exact hv2) (by norm_num) (by positivity) hs (by norm_num)
  · rw [abs_of_pos (by linarith)]
    have : (13 / 20 : ℝ) / 2 ^ 54 ≤ 7 / 10000 := by norm_num
    linarith
  · rw [abs_of_pos (by linarith)]
    have h2 : (2 : ℝ) ≤ 2 ^ 1023 := by norm_num
    have : (13 / 20 : ℝ) / 2 ^ 54 ≤ 1 := by norm_num
    linarith

set_option maxHeartbeats 2000000 in
/-- `log1pTail` for `K ≥ 1`, with the bound refined for `K = 1`, `f < -0.175`. -/
theorem tail_near (f c : Float) (k hu : UInt64) (K t et E : ℝ) (hf : Finite f.toBits)
    (hv1 : -2929 / 10000 ≤ value f.toBits) (hv2 : value f.toBits ≤ 41422 / 100000)
    (hhu1 : (hu == 0) = false → 1 / 2 ^ 30 ≤ |value f.toBits|)
    (hhu2 : (hu == 0) = true → |value f.toBits| ≤ 1 / 2 ^ 19)
    (hvz : value f.toBits ≠ 0 → 1 / 2 ^ 1000 ≤ |value f.toBits|)
    (hk : (k == 0) = false) (hkd : FApprox (LogCoreBits.kdOf k) K 0)
    (hA : FApprox (LogCoreBits.kdOf k * ln2HiF) (K * value 0x3FE62E42FEE00000) 0)
    (hK : K = 1 ∨ (2 ≤ K ∧ K ≤ 1100))
    (hc : FApprox c t et) (ht : |t| ≤ 1 / 2 ^ 52) (het : et ≤ 1 / 2 ^ 60)
    (hE1 : K = 1 → value f.toBits < -2501 / 10000 → 85 / 100 / 2 ^ 54 ≤ E)
    (hE2 : K = 1 → value f.toBits < -2199 / 10000 → 76 / 100 / 2 ^ 54 ≤ E)
    (hE3 : K = 1 → value f.toBits < -175 / 1000 → 43 / 100 / 2 ^ 54 ≤ E)
    (hE4 : 133 / 100 / 2 ^ 54 ≤ E ∨ (K = 1 ∧ value f.toBits < -175 / 1000)) :
    Near (Log1p.log1pTail f c k hu).toBits
      (K * Real.log 2 + Real.log (1 + value f.toBits) + Real.log (1 + t)) E := by
  set v := value f.toBits with hvdef
  have hKM : |K| ≤ 1100 := by
    rcases hK with h | h
    · rw [h]; norm_num
    · rw [abs_of_pos (by linarith [h.1])]; exact h.2
  have hK1 : 1 ≤ |K| := by
    rcases hK with h | h
    · rw [h]; norm_num
    · rw [abs_of_pos (by linarith [h.1])]; linarith [h.1]
  have hl2b := ln2_bounds
  have hlog := log_range v hv1 hv2
  have htl := abs_log_t t (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 1 / 4)])
  have htl' := abs_le.mp htl
  have hlv := abs_le.mp hlog
  have hlv_l := hlv.1
  have hlv_r := hlv.2
  have hta := abs_le.mp ht
  have hta_l := hta.1
  have hta_r := hta.2
  by_cases hneg : K = 1 ∧ v < -175 / 1000
  · -- `K = 1`, `f < -0.175`: the general path
    obtain ⟨hK1', hv3⟩ := hneg
    have hhu : (hu == 0) = false := by
      cases h : (hu == 0)
      · rfl
      · have := abs_le.mp (hhu2 h)
        linarith [this.1, (by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 175 / 1000)]
    rw [Log1pTheoremBranches.tail_s_eq f c k hu hk hhu]
    have hσ0 := hhu1 hhu
    have hs := sstar_le v (by linarith) hv2
    have hc1 := core_P1 f hf (abs_le.mpr ⟨by linarith, by linarith⟩) hσ0 (by linarith)
    have hY : (3465 / 10000 : ℝ) ≤ |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
      rw [hK1', one_mul, abs_of_pos (by linarith)]
      linarith
    by_cases ha : v < -2501 / 10000
    · refine (finish_s_near f c k K t et 1 (1 / 2 ^ 52) (2929 / 10000) _ _ _ _ (34659 / 100000)
        ((85 / 100) / 2 ^ 54) (3465 / 10000) 1015 1017 1020 hf (by linarith)
        (abs_le.mpr ⟨by linarith, by linarith⟩) hc1.1 hc1.2 hkd hA (by rw [hK1']; norm_num) hc
        ht (by norm_num) (by norm_num) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)])
        hlog (by norm_num) hs (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ hY
        (by norm_num)).mono (hE1 hK1' ha)
      all_goals first
        | (norm_num; done)
        | (norm_num at het ⊢; linarith)
    by_cases hb : v < -2199 / 10000
    · refine (finish_s_near f c k K t et 1 (1 / 2 ^ 52) (2501 / 10000) _ _ _ _ (34659 / 100000)
        ((76 / 100) / 2 ^ 54) (3465 / 10000) 1014 1017 1020 hf (by linarith)
        (abs_le.mpr ⟨by linarith, by linarith⟩) hc1.1 hc1.2 hkd hA (by rw [hK1']; norm_num) hc
        ht (by norm_num) (by norm_num) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)])
        hlog (by norm_num) hs (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ hY
        (by norm_num)).mono (hE2 hK1' hb)
      all_goals first
        | (norm_num; done)
        | (norm_num at het ⊢; linarith)
    · have hl0 := log_ge (-2199 / 10000) (-24834 / 100000) 8 (by norm_num) (by norm_num)
        (by decide +kernel)
      push_cast at hl0
      have hl1 : Real.log (1 + -2199 / 10000) ≤ Real.log (1 + v) :=
        Real.log_le_log (by norm_num) (by linarith)
      have hl2 : Real.log (1 + v) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
      have hlog' : |Real.log (1 + v)| ≤ 24834 / 100000 := by
        rw [abs_le]
        constructor <;> linarith
      refine (finish_s_near f c k K t et 1 (1 / 2 ^ 52) (2199 / 10000) _ _ _ _ (24834 / 100000)
        ((43 / 100) / 2 ^ 54) (3465 / 10000) 1014 1016 1019 hf (by linarith)
        (abs_le.mpr ⟨by linarith, by linarith⟩) hc1.1 hc1.2 hkd hA (by rw [hK1']; norm_num) hc
        ht (by norm_num) (by norm_num) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)])
        hlog' (by norm_num) hs (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ hY
        (by norm_num)).mono (hE3 hK1' hv3)
      all_goals first
        | (norm_num; done)
        | (norm_num at het ⊢; linarith)
  · -- `K ≥ 2` or `f ≥ -0.175`
    have hE' : 133 / 100 / 2 ^ 54 ≤ E := hE4.resolve_right hneg
    have hY : (5004 / 10000 : ℝ) ≤ |K * Real.log 2 + Real.log (1 + v) + Real.log (1 + t)| := by
      rcases hK with h | h
      · have h2 : -175 / 1000 ≤ v := by
          by_contra hcon
          exact hneg ⟨h, by linarith⟩
        have hl := log_ge (-175 / 1000) (-19238 / 100000) 8 (by norm_num) (by norm_num)
          (by decide +kernel)
        push_cast at hl
        have h3 : Real.log (1 + -175 / 1000) ≤ Real.log (1 + v) :=
          Real.log_le_log (by norm_num) (by linarith)
        rw [h, one_mul, abs_of_pos (by linarith)]
        linarith
      · have h3 : 2 * (6931471803 / 10 ^ 10) ≤ K * Real.log 2 :=
          mul_le_mul h.1 hl2b.1.le (by norm_num) (by linarith)
        rw [abs_of_pos (by linarith)]
        linarith
    cases hhu : (hu == 0)
    · rw [Log1pTheoremBranches.tail_s_eq f c k hu hk hhu]
      have hσ0 := hhu1 hhu
      have hs := sstar_le v (by linarith) hv2
      have hc4 := core_P4 f hf (abs_le.mpr ⟨by linarith, by linarith⟩) hσ0 (by linarith)
      refine (finish_s_near f c k K t et 1100 (1 / 2 ^ 52) (41422 / 100000) _ _ _ _
        (34659 / 100000) ((133 / 100) / 2 ^ 54) (5004 / 10000) 1016 1018 1020 hf (by linarith)
        (abs_le.mpr ⟨by linarith, by linarith⟩) hc4.1 hc4.2 hkd hA hKM hc ht (by norm_num)
        (by norm_num) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)]) hlog (by norm_num) hs
        (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ hY (by norm_num)).mono hE'
      all_goals first
        | (norm_num; done)
        | (norm_num at het ⊢; linarith)
    · have hσ := hhu2 hhu
      cases hz : (f == 0.0)
      · rw [Log1pTheoremBranches.tail_q_eq f c k hu hk hhu hz]
        have hv0 : v ≠ 0 := by
          intro h
          have := (beq_zero_iff f hf).mpr h
          rw [hz] at this
          exact Bool.false_ne_true this
        refine (finish_q_near f c k K t et 1100 1 (1 / 2 ^ 52) ((133 / 100) / 2 ^ 54) hf hσ
          (hvz hv0) hkd hA hKM (by norm_num) hK1 hc ht (by norm_num) (by norm_num)
          (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)]) ?_ (by norm_num)).mono hE'
        norm_num at het ⊢
        linarith
      · have hv0 : v = 0 := (beq_zero_iff f hf).mp hz
        rw [Log1pTheoremBranches.tail_z_eq f c k hu hk hhu hz]
        refine (finish_z_near c k v K t et 1100 1 (1 / 2 ^ 52) ((133 / 100) / 2 ^ 54) hv0 hkd hA
          hKM (by norm_num) hK1 hc ht (by norm_num) (by norm_num)
          (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)]) ?_ (by norm_num)).mono hE'
        norm_num at het ⊢
        linarith

#print axioms k0_near_low
#print axioms k0_near_high
#print axioms tail_near

end Verified.Examples.Log1pTheoremNearTail
