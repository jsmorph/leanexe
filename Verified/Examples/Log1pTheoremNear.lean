import Verified.Examples.Log1pTheorem
import Verified.Examples.Log1pTheoremNearTail

/-!
`Log1p.log1p x` for `x ≥ 2 ^ -29` as the nearest word of a value within `errBound x` of
`log (1 + x)` (`log1p_near`).  The bound follows the code's branches on `x`: the case `K = 0` below
`0.41421`, the main path with `K ≥ 1` up to `2 ^ 53`, where the refined cases of
`Log1pTheoremNearTail.tail_near` apply for `x < 0.6501`, and `K ≥ 53` above.  The boundaries in
`x` lie at least `10 ^ -4` inside the boundaries of the cases in `f`, which absorbs the rounding of
`u = 1 + x`.
-/

namespace Verified.Examples.Log1pTheoremNear
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64Near Log1pTheoremBranches Log1pTheoremTail
  Log1pTheoremReduce Log1pTheoremCorr Log1pTheorem Log1pTheoremNearTail

set_option exponentiation.threshold 4096

/-- The bound of `log1p_near`. -/
noncomputable def errBound (v : ℝ) : ℝ :=
  if v ≤ 285 / 1000 then 174 / 100 / 2 ^ 53 * v ^ 2 + v / 2 ^ 59
  else if v < 868669 / 2097152 then 65 / 100 / 2 ^ 54
  else if v < 4999 / 10000 then 85 / 100 / 2 ^ 54
  else if v < 5603 / 10000 then 76 / 100 / 2 ^ 54
  else if v < 6499 / 10000 then 43 / 100 / 2 ^ 54
  else if v < 2 ^ 53 then 133 / 100 / 2 ^ 54
  else 6 / 2 ^ 54

/-- The main path for `u ≥ 1.4142`, where `K ≥ 1`. -/
theorem main_near (x u c : Float) (hdom : -1 < value x.toBits) (hu : Finite u.toBits)
    (hfar : 14142132 / 10 ^ 7 ≤ value u.toBits) (et : ℝ)
    (hc : FApprox c ((1 + value x.toBits - value u.toBits) / value u.toBits) et)
    (ht : |(1 + value x.toBits - value u.toBits) / value u.toBits| ≤ 1 / 2 ^ 52)
    (het : et ≤ 1 / 2 ^ 60) (E : ℝ)
    (hE1 : value x.toBits < 4999 / 10000 → 85 / 100 / 2 ^ 54 ≤ E)
    (hE2 : value x.toBits < 5603 / 10000 → 76 / 100 / 2 ^ 54 ≤ E)
    (hE3 : value x.toBits < 6501 / 10000 → 43 / 100 / 2 ^ 54 ≤ E)
    (hE4 : 133 / 100 / 2 ^ 54 ≤ E ∨ value x.toBits < 6499 / 10000) :
    Near (mainTail u c (kOf u)).toBits (Real.log (1 + value x.toBits)) E := by
  have hpos : (1 : ℝ) / 2 ^ 60 ≤ value u.toBits := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 14142132 / 10 ^ 7)]
  obtain ⟨f, k, hu', K, heq, hff, hf1, hf2, hvu, hhu1, hhu2, hvz, hk0, hkK, hK1, hK2, hK0⟩ :=
    main_reduce u c hu hpos (Or.inr hfar)
  obtain ⟨hkd, hA⟩ := kd_exact k K (by omega) (by omega) hkK
  have hu0 : 0 < value u.toBits := lt_of_lt_of_le (by positivity) hpos
  have hd : |1 + value x.toBits - value u.toBits| ≤ value u.toBits / 2 ^ 52 := by
    have h := ht
    rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0] at h
    linarith
  have hda := abs_le.mp hd
  have hKp : 1 ≤ K := by
    by_contra hcon
    have h1 : (2 : ℝ) ^ K ≤ 2 ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [show (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 by norm_num] at h1
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 1 + value f.toBits)]
  have hK1u : K = 1 → value u.toBits = 2 * (1 + value f.toBits) := by
    intro h
    rw [hvu, h]
    norm_num
  have hK2u : 2 ≤ K → 4 * (1 + value f.toBits) ≤ value u.toBits := by
    intro h
    have h1 : (2 : ℝ) ^ (2 : ℤ) ≤ 2 ^ K := zpow_le_zpow_right₀ (by norm_num) h
    rw [show (2 : ℝ) ^ (2 : ℤ) = 4 by norm_num] at h1
    rw [hvu]
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  rw [heq, log_split (value x.toBits) (value u.toBits) (value f.toBits)
    ((1 + value x.toBits - value u.toBits) / value u.toBits) K hvu (by linarith) hu0 rfl hdom]
  have hK' : (K : ℝ) = 1 ∨ (2 ≤ (K : ℝ) ∧ (K : ℝ) ≤ 1100) := by
    rcases (by omega : K = 1 ∨ (2 ≤ K ∧ K ≤ 1100)) with h | h
    · left
      exact_mod_cast h
    · right
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hKeq : (K : ℝ) = 1 → K = 1 := fun h => by exact_mod_cast h
  refine tail_near f c k hu' K _ et E hff hf1 hf2 hhu1 hhu2 hvz hk0 hkd hA hK' hc ht het ?_ ?_ ?_ ?_
  · intro h hv
    have := hK1u (hKeq h)
    exact hE1 (by linarith)
  · intro h hv
    have := hK1u (hKeq h)
    exact hE2 (by linarith)
  · intro h hv
    have := hK1u (hKeq h)
    exact hE3 (by linarith)
  · rcases hE4 with h | h
    · exact Or.inl h
    · right
      rcases (by omega : K = 1 ∨ 2 ≤ K) with hk | hk
      · have := hK1u hk
        exact ⟨by exact_mod_cast hk, by linarith⟩
      · have := hK2u hk
        exfalso
        linarith

/-- The cases of `errBound` on the main path. -/
theorem errBound_main (v : ℝ) (h : 868669 / 2097152 ≤ v) (h53 : v < 2 ^ 53) :
    (v < 4999 / 10000 → 85 / 100 / 2 ^ 54 ≤ errBound v) ∧
    (v < 5603 / 10000 → 76 / 100 / 2 ^ 54 ≤ errBound v) ∧
    (v < 6501 / 10000 → 43 / 100 / 2 ^ 54 ≤ errBound v) ∧
    (133 / 100 / 2 ^ 54 ≤ errBound v ∨ v < 6499 / 10000) := by
  have h1 : ¬ v ≤ 285 / 1000 := by
    intro h'
    linarith [(by norm_num : (285 : ℝ) / 1000 < 868669 / 2097152)]
  have h2 : ¬ v < 868669 / 2097152 := not_lt.mpr h
  unfold errBound
  rw [if_neg h1, if_neg h2]
  split_ifs <;> refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, ?_⟩
  all_goals first
    | (norm_num; done)
    | (exfalso; linarith)
    | (left; norm_num; done)
    | (right; linarith)

/-- **`log1p` error bound.**  For finite `x ≥ 2 ^ -29`, `Log1p.log1p x` is the nearest word of a
value within `errBound x` of `log (1 + x)`. -/
theorem log1p_near (x : Float) (hx : Finite x.toBits) (h29 : 1 / 2 ^ 29 ≤ value x.toBits) :
    Near (Log1p.log1p x).toBits (Real.log (1 + value x.toBits)) (errBound (value x.toBits)) := by
  have hN := x.toBits.toNat_lt
  have hfin : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x7ff00000 := by
    rw [← ax_toNat]
    exact F64UpperWord.finite_high x.toBits hx
  obtain ⟨hsn, hsp⟩ := sign_value x hx
  have T29 := ax_lt x 0x3e200000 (by norm_num) (1 / 2 ^ 29) (by decide +kernel)
  have TP := ax_lt x 0x3FDA827A (by norm_num) (868669 / 2097152) (by decide +kernel)
  have T53 := ax_lt x 0x43400000 (by norm_num) (2 ^ 53) (by decide +kernel)
  rw [ax_toNat] at T29 TP T53
  push_cast at T29 TP T53
  have hpos : x.toBits.toNat < 2 ^ 63 := by
    by_contra h
    have := hsn (not_lt.mp h)
    linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 29)]
  have hv0 := hsp hpos
  rw [abs_of_nonneg hv0] at T29 TP T53
  have c1 : ¬ x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x3e200000 :=
    fun h => absurd (T29.mp h) (not_lt.mpr h29)
  by_cases c2 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x3FDA827A
  · have hP := TP.mp c2
    rw [log1p_k0_eq x (by bits_omega) (by rw [UInt64.lt_iff_toNat_lt, ax_toNat]; simpa using c1)
      (by simp only [ge_iff_le, not_le, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ax_toNat,
            UInt64.reduceToNat, Nat.reducePow] at *
          omega) (by bits_omega),
      tail_k0_eq x 0.0 1 (by decide)]
    by_cases c3 : value x.toBits ≤ 285 / 1000
    · rw [errBound, if_pos c3]
      exact k0_near_low x hx (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 30 ≤ 1 / 2 ^ 29)]) c3
    · rw [errBound, if_neg c3, if_pos hP]
      exact (k0_near_high x hx (by linarith) (by norm_num at hP ⊢; linarith)).mono (by norm_num)
  have hP : 868669 / 2097152 ≤ value x.toBits := not_lt.mp (fun h => c2 (TP.mpr h))
  by_cases c3 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x43400000
  · have h53 := T53.mp c3
    obtain ⟨hE1, hE2, hE3, hE4⟩ := errBound_main (value x.toBits) hP h53
    rw [log1p_main_eq x (by bits_omega) (by bits_omega) (by bits_omega) (by bits_omega)
      (by bits_omega)]
    rcases lt_trichotomy x.toBits.toNat 0x3FEFFFFFFFFFFFFF with c4 | c4 | c4
    · have hw : value x.toBits ≤ value (0x3FEFFFFFFFFFFFFE : UInt64) :=
        (F64PositiveOrder.value_le_iff hpos (by decide)).mpr (by
          change x.toBits.toNat ≤ 0x3FEFFFFFFFFFFFFE
          omega)
      rw [word_value (0x3FEFFFFFFFFFFFFE : UInt64) (1 - 1 / 2 ^ 52) (by decide +kernel)] at hw
      push_cast at hw
      obtain ⟨huf, hlo, hlt, hc, ht⟩ := corr_hi x hx (by norm_num at hP ⊢; linarith) hw
      exact main_near x (1.0 + x) _ (by linarith) huf hlo _ hc ht le_rfl _ hE1 hE2 hE3 hE4
    · have hxb : x.toBits = 0x3FEFFFFFFFFFFFFF := UInt64.toNat_inj.mp c4
      have hvx : value x.toBits = 1 - 1 / 2 ^ 53 := by
        rw [hxb, word_value _ (1 - 1 / 2 ^ 53) (by decide +kernel)]
        norm_num
      have hE : 133 / 100 / 2 ^ 54 ≤ errBound (value x.toBits) :=
        hE4.resolve_right (by rw [hvx]; norm_num)
      exact (special_two_near x hxb).mono (le_trans (by norm_num) hE)
    · have hw : value (0x3FF0000000000000 : UInt64) ≤ value x.toBits :=
        (F64PositiveOrder.value_le_iff (by decide) hpos).mpr (by
          change 0x3FF0000000000000 ≤ x.toBits.toNat
          omega)
      rw [word_value (0x3FF0000000000000 : UInt64) 1 (by decide +kernel)] at hw
      push_cast at hw
      obtain ⟨huf, hlo, hhi, hc, ht⟩ := corr_big x hx hw h53
      exact main_near x (1.0 + x) _ (by linarith) huf (by linarith) _ hc ht le_rfl _ hE1 hE2 hE3
        hE4
  · have h53 : 2 ^ 53 ≤ value x.toBits := not_lt.mp (fun h => c3 (T53.mpr h))
    rw [log1p_big_eq x (by bits_omega) (by bits_omega) (by bits_omega) (by bits_omega)
      (by bits_omega)]
    have hE : errBound (value x.toBits) = 6 / 2 ^ 54 := by
      have h0 : (6499 : ℝ) / 10000 < 2 ^ 53 := by norm_num
      have e1 : ¬ value x.toBits ≤ 285 / 1000 := by intro h; linarith
      have e2 : ¬ value x.toBits < 868669 / 2097152 := by intro h; linarith
      have e3 : ¬ value x.toBits < 4999 / 10000 := by intro h; linarith
      have e4 : ¬ value x.toBits < 5603 / 10000 := by intro h; linarith
      have e5 : ¬ value x.toBits < 6499 / 10000 := by intro h; linarith
      have e6 : ¬ value x.toBits < 2 ^ 53 := not_lt.mpr h53
      rw [errBound, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6]
    rw [hE]
    exact big_near x hx h53

#print axioms main_near
#print axioms log1p_near

end Verified.Examples.Log1pTheoremNear
