import Verified.Examples.ArmReconstruction
import Verified.Examples.ExpNegativeFinal

/-!
The special paths of `Exp2.exp2SpecialCase`, shared by Arm's `exp2` and `exp10`, for any
polynomial word `w` that approximates `T + ρ - 1`.  For a positive exponent the scale is lowered
by one binade, `s = 2 ^ (q - 1) H j`, and the rounded sum `s + s · w` is doubled exactly.  For a
negative exponent the scale is raised by 1022 binades, and the result is `2 ^ -1022` times
either the sum or, below 1, the compensated sum of `ExpSpecialNegative`.  Either way the result
lies within one step of the reference of `E = 2 ^ q exp (j log 2 / 128) ρ`.
-/

namespace Verified.Examples.ArmSpecial
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative F64Magnitude ExpSpecialNegative

set_option exponentiation.threshold 4096

theorem two_word : (0x4000000000000000 : UInt64) = Wasm.IEEE64.encodeFinite false 1024 0 := by
  decide +kernel

theorem head_zero : value (ExpTableBounds.headBits 0) = 1 := by
  have h : Wasm.IEEE64.scaledValue (ExpTableBounds.headBits 0) = (2 : Int) ^ 1074 := by
    decide +kernel
  rw [value, h]
  norm_num

/-- The doubled sum for a positive exponent, below the overflow threshold. -/
theorem positive_within (s w : UInt64) (q : Int) (j : Fin 128) (ρ : ℝ)
    (hsf : Finite s) (hwf : Finite w)
    (hs : value s = (2 : ℝ) ^ (q - 1) * value (ExpTableBounds.headBits j.val))
    (hqlo : 0 ≤ q) (hqhi : q ≤ 1024)
    (hW : |value w| ≤ 1 / 64)
    (hWe : |value w - (value (ExpTableBounds.tailBits j.val) + ρ - 1)| ≤ 1 / 2 ^ 56)
    (hρl : 319 / 320 ≤ ρ) (hρu : ρ ≤ 257 / 256)
    (hEmax : (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ ≤
      2 ^ 1024 - 2 ^ 980) :
    F64SignedRounding.WithinSteps 1
      ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ)
      (Wasm.IEEE64.mul 0x4000000000000000 (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w))) := by
  obtain ⟨hEn, hEz⟩ := ArmReconstruction.target_range q j ρ hρl hρu
  set E := (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ with hEdef
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hb := ExpTableBounds.entry_bounds j
  have hH1 : 1 ≤ value (ExpTableBounds.headBits j.val) := hb.2.2.1
  have hH2 : value (ExpTableBounds.headBits j.val) ≤ 2 := hb.2.2.2.1
  have hTb : |value (ExpTableBounds.tailBits j.val)| ≤ 1 / 2 ^ 53 := hb.2.2.2.2
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  have hQ1 : (2 : ℝ) ^ (q - 1) = (2 : ℝ) ^ q / 2 := by
    rw [zpow_sub₀ (by norm_num), zpow_one]
  have hρ : |ρ - 1| ≤ 1 / 128 := by
    rw [abs_le]
    constructor <;> linarith
  -- the scale is at most `2 ^ 1023`
  have hSmax : value s ≤ (2 : ℝ) ^ 1023 := by
    rw [hs, hQ1]
    rcases lt_or_eq_of_le hqhi with hq | hq
    · have hq' : q ≤ 1023 := by omega
      have h : (2 : ℝ) ^ q ≤ (2 : ℝ) ^ ((1023 : Nat) : Int) :=
        zpow_le_zpow_right₀ (by norm_num) hq'
      rw [zpow_natCast] at h
      calc
        _ ≤ (2 : ℝ) ^ 1023 / 2 * 2 :=
          mul_le_mul (div_le_div_of_nonneg_right h (by norm_num)) hH2 (by linarith) (by positivity)
        _ = _ := by ring
    · have hj0 : j.val = 0 := by
        by_contra hj
        have h1 := (hEn hj).1
        rw [hq] at h1
        have : (2 : ℝ) ^ (1024 : Int) = 2 ^ 1024 := zpow_natCast 2 1024
        rw [this] at h1
        linarith
      rw [hj0, head_zero, hq, show (2 : ℝ) ^ (1024 : Int) = 2 ^ 1024 from zpow_natCast 2 1024]
      norm_num
  have hS0 : 0 < value s := by
    rw [hs]
    exact mul_pos (zpow_pos (by norm_num) _) (by linarith)
  have hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s := by
    rw [hs, hQ1]
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_zpow₀ (by norm_num) hqlo
    have : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 := by norm_num
    nlinarith
  have htab := ArmReconstruction.table_general s q (-1) j ρ (by rw [← sub_eq_add_neg]; exact hs)
    (by linarith) hρu
  have hm1 : (2 : ℝ) ^ (-1 : Int) = 1 / 2 := by norm_num
  rw [hm1, ← hEdef] at htab
  have hfit : value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ + value s / 2 ^ 50 <
      (2 : ℝ) ^ 1023 := by
    have h1 := (abs_le.mp htab).2
    have h2 : value s / 2 ^ 98 + value s / 2 ^ 50 ≤ (2 : ℝ) ^ 1023 / 2 ^ 49 := by
      have : value s / 2 ^ 98 + value s / 2 ^ 50 ≤ value s / 2 ^ 49 := by
        linarith [hS0.le]
      exact this.trans (div_le_div_of_nonneg_right hSmax (by norm_num))
    have h3 : (1 : ℝ) / 2 * E ≤ (2 ^ 1024 - 2 ^ 980) / 2 := by linarith
    have h4 : (2 ^ 1024 - 2 ^ 980 : ℝ) / 2 + 2 ^ 1023 / 2 ^ 49 < 2 ^ 1023 := by norm_num
    linarith
  obtain ⟨hyf, hye⟩ := ArmReconstruction.reconstruction_general s w _ ρ hsf hwf hslo hSmax hW
    hWe hρ hTb hfit
  set y := Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)
  have hyE : |value y - E / 2| ≤ (5 / 4) * unitRoundoff64 * value s := by
    calc
      _ ≤ |value y - value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ| +
          |value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ - 1 / 2 * E| := by
        rw [show E / 2 = 1 / 2 * E by ring]
        exact abs_sub_le _ _ _
      _ ≤ (6 / 5) * unitRoundoff64 * value s + value s / 2 ^ 98 := add_le_add hye htab
      _ ≤ _ := by rw [hu]; nlinarith only [hS0]
  have hEpos : 0 < E := mul_pos (mul_pos hQ (Real.exp_pos _)) (by linarith)
  have hElo : (2 : ℝ) ^ q * (319 / 320) ≤ E := by
    by_cases hj0 : j.val = 0
    · exact (hEz hj0).1
    · have := (hEn hj0).1
      nlinarith
  have hSq : value s ≤ (2 : ℝ) ^ q := by
    rw [hs, hQ1]
    nlinarith
  -- the sum is a positive normal number below `2 ^ 1023`
  have hypos : 1 / (2 : ℝ) ^ 1022 < value y := by
    have h1 := (abs_le.mp hyE).1
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_zpow₀ (by norm_num) hqlo
    rw [hu] at h1
    have : (1 : ℝ) / 2 ^ 1022 < 1 / 4 := by norm_num
    nlinarith
  obtain ⟨hye1, hys⟩ := normal_of_value y hypos
  have hyhi : value y < (2 : ℝ) ^ 1023 := by
    have h1 := (abs_le.mp hyE).2
    rw [hu] at h1
    have : (5 / 4) * (1 / 2 ^ 53) * value s ≤ (5 / 4) * (1 / 2 ^ 53) * (2 : ℝ) ^ 1023 :=
      mul_le_mul_of_nonneg_left hSmax (by norm_num)
    have : (2 ^ 1024 - 2 ^ 980 : ℝ) / 2 + 5 / 4 * (1 / 2 ^ 53) * 2 ^ 1023 < 2 ^ 1023 := by
      norm_num
    linarith
  have hyexp : Wasm.IEEE64.exponent y ≤ 2045 := by
    by_contra hn
    have h := magnitude_ge y 2046 1023 (by norm_num) (by norm_num) (by norm_num) (by omega)
    rw [abs_of_pos (lt_trans (by positivity) hypos)] at h
    have : (2 : ℝ) ^ (1023 : Int) = 2 ^ 1023 := zpow_natCast 2 1023
    linarith
  obtain ⟨hcf, hcv⟩ := F64PowerScale.mul_power_finite 1024 y (by norm_num) (by norm_num) hyf
    hye1 (by omega) (by omega)
  rw [← two_word] at hcf hcv
  set c := Wasm.IEEE64.mul 0x4000000000000000 y
  have hcv' : value c = 2 * value y := by
    rw [hcv]
    norm_num
  have herr : |value c - E| ≤
      (7 / 5) * unitRoundoff64 * ((2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) := by
    rw [hcv', show 2 * value y - E = 2 * (value y - E / 2) by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hs2 : (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val) = 2 * value s := by
      rw [hs, hQ1]
      ring
    rw [hs2, hu]
    rw [hu] at hyE
    nlinarith only [hyE, hS0]
  have hcpos : 0 < value c := by
    rw [hcv']
    linarith
  have hclim := F64PositiveOrder.positive_finite_encoding _ hcf hcpos
  have hq : -1022 ≤ q := by omega
  have hstep := ExpOneStep.one_step_of_error E _ c q j hq hEn hEz herr (Or.inl ⟨hclim, rfl⟩)
  exact F64SignedRounding.within_of_nonneg 1 E hEpos.le c hclim.le hstep.1 hstep.2

/-- The scaled-down result for a negative exponent. -/
theorem negative_within (s w : UInt64) (q : Int) (j : Fin 128) (ρ : ℝ)
    (hsf : Finite s) (hwf : Finite w)
    (hs : value s = (2 : ℝ) ^ (q + 1022) * value (ExpTableBounds.headBits j.val))
    (hqlo : -2022 ≤ q) (hqhi : q ≤ -23)
    (hW : |value w| ≤ 1 / 64)
    (hWe : |value w - (value (ExpTableBounds.tailBits j.val) + ρ - 1)| ≤ 1 / 2 ^ 56)
    (hρl : 319 / 320 ≤ ρ) (hρu : ρ ≤ 257 / 256) :
    F64SignedRounding.WithinSteps 1
      ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ)
      (Wasm.IEEE64.mul 0x0010000000000000
        (if Wasm.IEEE64.lt (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) one then
          compRounded (compSum s (Wasm.IEEE64.mul s w))
        else Wasm.IEEE64.add s (Wasm.IEEE64.mul s w))) := by
  obtain ⟨hEn, hEz⟩ := ArmReconstruction.target_range q j ρ hρl hρu
  set E := (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * ρ with hEdef
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hu0 : 0 < unitRoundoff64 := by rw [hu]; positivity
  have hb := ExpTableBounds.entry_bounds j
  have hH1 : 1 ≤ value (ExpTableBounds.headBits j.val) := hb.2.2.1
  have hH : value (ExpTableBounds.headBits j.val) ≤ 255 / 128 := (ExpCoreRange.head_bounds j).1
  have hTb : |value (ExpTableBounds.tailBits j.val)| ≤ 1 / 2 ^ 53 := hb.2.2.2.2
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  have hρ : |ρ - 1| ≤ 1 / 128 := by
    rw [abs_le]
    constructor <;> linarith
  have hR : (0 : ℝ) < (2 : ℝ) ^ (q + 1022) := zpow_pos (by norm_num) _
  have hS : 0 < value s := by rw [hs]; exact mul_pos hR (by linarith)
  have hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s := by
    rw [hs]
    have h : (2 : ℝ) ^ (-((1000 : Nat) : Int)) ≤ (2 : ℝ) ^ (q + 1022) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    simp only [zpow_neg, zpow_natCast, inv_eq_one_div] at h
    nlinarith
  have hshi : value s ≤ (2 : ℝ) ^ 1000 := by
    rw [hs]
    have h : (2 : ℝ) ^ (q + 1022) ≤ (2 : ℝ) ^ ((999 : Nat) : Int) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_natCast] at h
    calc
      _ ≤ (2 : ℝ) ^ 999 * 2 := mul_le_mul h (by linarith) (by linarith) (by positivity)
      _ = _ := by norm_num
  obtain ⟨hpf, hPm, hpre0⟩ := ArmReconstruction.presum_general s w _ ρ hsf hwf hslo
    (hshi.trans (by norm_num)) hW hWe hρ hTb
  have htab := ArmReconstruction.table_general s q 1022 j ρ hs (by linarith) hρu
  rw [← hEdef] at htab
  have hpre : |value s + value (Wasm.IEEE64.mul s w) - (2 : ℝ) ^ (1022 : Int) * E| ≤
      (11 / 64) * unitRoundoff64 * value s := by
    calc
      _ ≤ |value s + value (Wasm.IEEE64.mul s w) -
            value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ| +
          |value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ - (2 : ℝ) ^ (1022 : Int) * E| :=
        abs_sub_le _ _ _
      _ ≤ (21 / 128) * unitRoundoff64 * value s + value s / 2 ^ 98 := add_le_add hpre0 htab
      _ ≤ _ := by rw [hu]; nlinarith only [hS]
  have hfit : value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ + value s / 2 ^ 50 <
      (2 : ℝ) ^ 1023 := by
    have h1 : 1 + value (ExpTableBounds.tailBits j.val) ≤ 2 := by
      have := (abs_le.mp hTb).2
      linarith [show (1 : ℝ) / 2 ^ 53 ≤ 1 by norm_num]
    have hm : value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ ≤
        value s * 2 * (257 / 256) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hS.le) hρu (by linarith)
        (mul_nonneg hS.le (by norm_num))
    have hd : value s / 2 ^ 50 ≤ value s := div_le_self hS.le (by norm_num)
    calc
      _ ≤ value s * 2 * (257 / 256) + value s := add_le_add hm hd
      _ ≤ (2 : ℝ) ^ 1000 * 2 * (257 / 256) + 2 ^ 1000 := by gcongr
      _ < (2 : ℝ) ^ 1023 := by norm_num
  obtain ⟨hyf, hye0⟩ := ArmReconstruction.reconstruction_general s w _ ρ hsf hwf hslo
    (hshi.trans (by norm_num)) hW hWe hρ hTb hfit
  have hye : |value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) - (2 : ℝ) ^ (1022 : Int) * E| ≤
      (7 / 5) * unitRoundoff64 * value s := by
    calc
      _ ≤ |value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) -
            value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ| +
          |value s * (1 + value (ExpTableBounds.tailBits j.val)) * ρ - (2 : ℝ) ^ (1022 : Int) * E| :=
        abs_sub_le _ _ _
      _ ≤ (6 / 5) * unitRoundoff64 * value s + value s / 2 ^ 98 := add_le_add hye0 htab
      _ ≤ _ := by rw [hu]; nlinarith only [hS]
  generalize hp : Wasm.IEEE64.mul s w = p at *
  have hE : 0 < E := mul_pos (mul_pos hQ (Real.exp_pos _)) (by linarith)
  have hlt := lt_one_iff _ hyf
  by_cases hy1 : value (Wasm.IEEE64.add s p) < 1
  · rw [hlt, decide_eq_true hy1, ite_eq_left rfl]
    have hS2 := (comp_sum_bounds s p hsf hpf hS hshi hPm hy1).2.2.2
    have hpre' : |value s + value p - (2 : ℝ) ^ (1022 : Int) * E| ≤ 11 / 16 * unitRoundoff64 := by
      have : (11 / 64) * unitRoundoff64 * value s ≤ (11 / 64) * unitRoundoff64 * 2 :=
        mul_le_mul_of_nonneg_left hS2.le (mul_nonneg (by norm_num) hu0.le)
      linarith
    obtain ⟨hclim, hc1, hc2⟩ := compensated_one_step s p _ hsf hpf hS hshi hPm hy1 hE hpre'
    exact F64SignedRounding.within_of_nonneg 1 E hE.le _ hclim.le hc1 hc2
  · rw [hlt, decide_eq_false hy1]
    simp only [Bool.false_eq_true, ite_false]
    have hy1' : 1 ≤ value (Wasm.IEEE64.add s p) := le_of_not_gt hy1
    have hey := exponent_ge_of_one_le _ hy1'
    have hefin : Wasm.IEEE64.exponent (Wasm.IEEE64.add s p) ≤ 2046 := by
      have h := hyf
      simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
      have : Wasm.IEEE64.exponent (Wasm.IEEE64.add s p) < 2048 := Nat.mod_lt _ (by norm_num)
      omega
    obtain ⟨hcf, hcv⟩ := F64PowerScale.mul_power_finite 1 (Wasm.IEEE64.add s p) (by norm_num)
      (by norm_num) hyf (by omega) (by omega) (by omega)
    rw [← scale_down_word] at hcf hcv
    set c := Wasm.IEEE64.mul 0x0010000000000000 (Wasm.IEEE64.add s p)
    have hcv' : value c = (2 : ℝ) ^ (-1022 : Int) * value (Wasm.IEEE64.add s p) := by
      rw [hcv, show ((1 : Nat) : Int) - 1023 = -1022 by norm_num]
    have hEu : E ≤ (2 : ℝ) ^ q * (2 - 1 / 65536) := by
      by_cases hj0 : j.val = 0
      · have := (hEz hj0).2
        nlinarith
      · exact (hEn hj0).2
    have hzq : (2 : ℝ) ^ (1022 : Int) * (2 : ℝ) ^ q = (2 : ℝ) ^ (q + 1022) := by
      rw [← zpow_add₀ (by norm_num), add_comm]
    have hm1022 : (2 : ℝ) ^ (-1022 : Int) * (2 : ℝ) ^ (q + 1022) = (2 : ℝ) ^ q := by
      rw [← zpow_add₀ (by norm_num), show (-1022 : Int) + (q + 1022) = q by ring]
    have hinv : (2 : ℝ) ^ (-1022 : Int) * (2 : ℝ) ^ (1022 : Int) = 1 := by
      rw [← zpow_add₀ (by norm_num), show (-1022 : Int) + 1022 = 0 by norm_num, zpow_zero]
    have hq : -1022 ≤ q := by
      by_contra hn
      push Not at hn
      have hR' : (2 : ℝ) ^ (q + 1022) ≤ (2 : ℝ) ^ (-1 : Int) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hhalf : (2 : ℝ) ^ (-1 : Int) = 1 / 2 := by norm_num
      have h1 : (2 : ℝ) ^ (1022 : Int) * E ≤ (2 : ℝ) ^ (q + 1022) * (2 - 1 / 65536) := by
        rw [← hzq, mul_assoc]
        exact mul_le_mul_of_nonneg_left hEu (by positivity)
      have h2 : value s ≤ (2 : ℝ) ^ (q + 1022) * (255 / 128) := by
        rw [hs]
        exact mul_le_mul_of_nonneg_left hH hR.le
      have h3 := abs_le.mp hye
      rw [hu] at h3
      rw [hhalf] at hR'
      linarith
    have herr : |value c - E| ≤
        (7 / 5) * unitRoundoff64 * ((2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) := by
      have hid : value c - E = (2 : ℝ) ^ (-1022 : Int) *
          (value (Wasm.IEEE64.add s p) - (2 : ℝ) ^ (1022 : Int) * E) := by
        rw [hcv', mul_sub, ← mul_assoc, hinv, one_mul]
      rw [hid, abs_mul, abs_of_pos (zpow_pos (by norm_num) _)]
      calc
        _ ≤ (2 : ℝ) ^ (-1022 : Int) * ((7 / 5) * unitRoundoff64 * value s) :=
          mul_le_mul_of_nonneg_left hye (by positivity)
        _ = _ := by
          rw [hs, ← hm1022]
          ring
    have hcpos : 0 < value c := by
      rw [hcv']
      exact mul_pos (zpow_pos (by norm_num) _) (by linarith)
    have hclim := F64PositiveOrder.positive_finite_encoding _ hcf hcpos
    have hstep := ExpOneStep.one_step_of_error E _ c q j hq hEn hEz herr (Or.inl ⟨hclim, rfl⟩)
    exact F64SignedRounding.within_of_nonneg 1 E hE.le c hclim.le hstep.1 hstep.2

#print axioms two_word
#print axioms head_zero
#print axioms positive_within
#print axioms negative_within

end Verified.Examples.ArmSpecial
