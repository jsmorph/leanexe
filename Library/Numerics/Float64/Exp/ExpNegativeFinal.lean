import Library.Numerics.Float64.Exp.ExpSpecialNegative
import LeanExe.ProofKit.F64Magnitude

/-!
The final multiplication of the negative special path of `Exp.exp`: the exact product of
`2 ^ -1022` and the compensated value, and the product of `2 ^ -1022` and a reconstruction of at
least 1.
-/

namespace Library.Numerics.Float64.Exp.ExpSpecialNegative
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative F64Magnitude

set_option exponentiation.threshold 4096

theorem scale_down_word : (0x0010000000000000 : UInt64) = Wasm.IEEE64.encodeFinite false 1 0 := by
  decide +kernel
#print axioms scale_down_word

/-- The compensated result: `2 ^ -1022 (z - 1)`, exact, for `z` on the grid of `2 ^ -52` in
`[1, 2]`. -/
theorem comp_final (z : UInt64) (hzf : Finite z) (R : Nat)
    (hR : Wasm.IEEE64.scaledValue z = (R : Int) * 2 ^ 1022) (hRl : 2 ^ 52 ≤ R) (hRu : R ≤ 2 ^ 53) :
    Finite (Wasm.IEEE64.mul 0x0010000000000000 (compRounded z)) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.mul 0x0010000000000000 (compRounded z)) = false ∧
      value (Wasm.IEEE64.mul 0x0010000000000000 (compRounded z)) =
        (value z - 1) / (2 : ℝ) ^ 1022 := by
  obtain ⟨hyf, hys⟩ := F64GridExact.sub_grid_exact z one hzf one_finite ((R : Int) - 2 ^ 52) 1022
    (by rw [hR, one_scaled]; ring) (by omega) (by norm_num)
  have hm53 : R - 2 ^ 52 < 2 ^ 53 := by omega
  have hys' : Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub z one) =
      ((R - 2 ^ 52 : Nat) : Int) * 2 ^ 1022 := by
    rw [hys, hR, one_scaled, Nat.cast_sub hRl, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hzv : (value z - 1) / (2 : ℝ) ^ 1022 = ((R - 2 ^ 52 : Nat) : ℝ) / (2 : ℝ) ^ 1074 := by
    rw [grid_value z R 1022 hR, Nat.cast_sub hRl, Nat.cast_pow, Nat.cast_ofNat,
      show (2 : ℝ) ^ 1074 = 2 ^ 1022 * 2 ^ 52 by rw [← pow_add]]
    field_simp
  have hsv0 : Wasm.IEEE64.scaledValue (0 : UInt64) = 0 := by decide +kernel
  have heq : Wasm.IEEE64.eq (Wasm.IEEE64.sub z one) 0 = decide (R - 2 ^ 52 = 0) := by
    unfold Wasm.IEEE64.eq
    rw [not_nan_of_finite hyf, show Wasm.IEEE64.isNaN 0 = false by decide +kernel, hys', hsv0]
    simp only [Bool.or_false, Bool.false_eq_true, ite_false]
    by_cases h0 : R - 2 ^ 52 = 0
    · rw [h0, Nat.cast_zero, zero_mul]
      rfl
    · have hne : (((R - 2 ^ 52 : Nat) : Int) * 2 ^ 1022 == 0) = false := by
        rw [beq_eq_false_iff_ne]
        exact mul_ne_zero (by exact_mod_cast h0) (pow_ne_zero _ (by norm_num))
      rw [hne]
      exact (decide_eq_false h0).symm
  have hbits : compRounded z = if R - 2 ^ 52 = 0 then 0 else Wasm.IEEE64.sub z one := by
    unfold compRounded
    simp only [heq, decide_eq_true_eq]
  have hpf : Finite (0x0010000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  have hps : Wasm.IEEE64.sign (0x0010000000000000 : UInt64) = false := by decide +kernel
  have hpm : Wasm.IEEE64.scaledMagnitude (0x0010000000000000 : UInt64) = 2 ^ 52 := by
    decide +kernel
  rw [hbits, hzv]
  by_cases h0 : R - 2 ^ 52 = 0
  · rw [ite_eq_left h0, h0]
    have hmul : Wasm.IEEE64.mul 0x0010000000000000 0 = 0 := by decide +kernel
    rw [hmul]
    refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, by decide +kernel, ?_⟩
    rw [value, hsv0, Int.cast_zero, Nat.cast_zero]
  · have hsign : Wasm.IEEE64.sign (Wasm.IEEE64.sub z one) = false := by
      by_contra hs
      have hs' : Wasm.IEEE64.sign (Wasm.IEEE64.sub z one) = true := by simpa using hs
      have h := hys'
      simp only [Wasm.IEEE64.scaledValue, hs', ite_true] at h
      have hpos : (0 : Int) < ((R - 2 ^ 52 : Nat) : Int) * 2 ^ 1022 :=
        mul_pos (by exact_mod_cast Nat.pos_of_ne_zero h0) (pow_pos (by norm_num) _)
      have hnn : (0 : Int) ≤ (Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.sub z one) : Int) :=
        Int.natCast_nonneg _
      linarith
    have hmag : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.sub z one) = (R - 2 ^ 52) * 2 ^ 1022 := by
      have h := hys'
      simp only [Wasm.IEEE64.scaledValue, hsign, Bool.false_eq_true, ite_false] at h
      exact_mod_cast h
    rw [ite_eq_right h0, mul_finite_rounder _ _ hpf hyf, hps, hsign, hpm, hmag]
    have hp : 2 ^ 52 * ((R - 2 ^ 52) * 2 ^ 1022) = (R - 2 ^ 52) * 2 ^ (1074 + 0) := by ring
    rw [hp, F64PowerScale.dyadic_shifted_exact _ _ 0 hm53, pow_zero, Nat.mul_one]
    have hff : (false != false) = false := rfl
    rw [hff]
    have hx := roundScaledMagnitude_exact false (R - 2 ^ 52) hm53.le
    refine ⟨hx.1, hx.2.2, ?_⟩
    simp only [value, Wasm.IEEE64.scaledValue, hx.2.1, hx.2.2, Bool.false_eq_true, ite_false,
      Int.cast_natCast]

#print axioms comp_final

theorem two_zpow_1022 : (2 : ℝ) ^ (1022 : Int) = (2 : ℝ) ^ 1022 := zpow_natCast 2 1022

/-- The compensated branch: for `y = s ⊕ p < 1` with `s + p` within `(21/64) u s` of
`2 ^ 1022 E`, the compensated result lies within one step of the reference of `E`. -/
theorem compensated_one_step (s p : UInt64) (E : ℝ) (hsf : Finite s) (hpf : Finite p)
    (hS : 0 < value s) (hS2 : value s ≤ (2 : ℝ) ^ 1000) (hP : |value p| ≤ value s / 32)
    (hy1 : value (Wasm.IEEE64.add s p) < 1) (hE : 0 < E)
    (hpre : |value s + value p - (2 : ℝ) ^ (1022 : Int) * E| ≤ 11 / 16 * unitRoundoff64) :
    let c := Wasm.IEEE64.mul 0x0010000000000000 (compRounded (compSum s p))
    c.toNat < limit ∧
      c.toNat ≤ (F64PositiveRounding.roundNearestEven E).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven E).toNat ≤ c.toNat + 1 := by
  intro c
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hu0 : 0 < unitRoundoff64 := by rw [hu]; positivity
  have hu1 : unitRoundoff64 ≤ 1 / 1024 := by rw [hu]; norm_num
  obtain ⟨hzf, ⟨R, hR, hRl, hRu⟩, hze, hSlt⟩ := comp_sum_bounds s p hsf hpf hS hS2 hP hy1
  obtain ⟨hcf, hcs, hcv⟩ := comp_final (compSum s p) hzf R hR hRl hRu
  have hclim : c.toNat < limit := lt_limit_of_finite c hcf hcs
  rw [two_zpow_1022] at hpre
  set T := (2 : ℝ) ^ 1022 with hT_def
  have hT : 0 < T := by positivity
  have hRv : (2 : ℝ) ^ 52 ≤ (R : ℝ) ∧ (R : ℝ) ≤ (2 : ℝ) ^ 53 := by
    constructor <;> exact_mod_cast (by assumption)
  have hzv := grid_value _ R 1022 hR
  have h1074 : (2 : ℝ) ^ 1074 = 2 ^ 52 * T := by rw [hT_def, ← pow_add]
  have h1075 : (2 : ℝ) ^ 53 * T = 2 * 2 ^ 1074 := by rw [h1074]; ring
  have hz1 : 1 ≤ value (compSum s p) := by
    rw [hzv, le_div_iff₀ (by positivity), one_mul, h1074, ← hT_def]
    exact mul_le_mul_of_nonneg_right hRv.1 hT.le
  have hz2 : value (compSum s p) ≤ 2 := by
    rw [hzv, div_le_iff₀ (by positivity), ← hT_def]
    calc
      (R : ℝ) * T ≤ 2 ^ 53 * T := mul_le_mul_of_nonneg_right hRv.2 hT.le
      _ = 2 * 2 ^ 1074 := h1075
  -- the error of the compensated sum against 1 + T E
  have huS : unitRoundoff64 * value s ≤ unitRoundoff64 * 2 :=
    mul_le_mul_of_nonneg_left hSlt.le hu0.le
  have hu2 : unitRoundoff64 ^ 2 ≤ 1 / 1024 * unitRoundoff64 := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right hu1 hu0.le
  have herr : |value (compSum s p) - 1 - T * E| < 3 * unitRoundoff64 := by
    have h1 := abs_le.mp hze
    have h2 := abs_le.mp hpre
    rw [abs_lt]
    constructor <;> linarith
  have hcv' : value c = (value (compSum s p) - 1) / T := hcv
  have hdiff : value c - E = (value (compSum s p) - 1 - T * E) / T := by
    rw [hcv']
    field_simp
  have hbnd : value (UInt64.ofNat (2 * 2 ^ 52)) = 2 / T := by
    rw [F64NearestBinade.boundary_power 2 (-1021) (by norm_num) (by norm_num) (by norm_num),
      show (-1021 : Int) = 1 - 1022 by norm_num, zpow_sub₀ (by norm_num), zpow_one, two_zpow_1022]
  have hE2 : E ≤ 2 / T := by
    rw [le_div_iff₀ hT]
    have := abs_lt.mp herr
    nlinarith
  have hc0 : 0 ≤ value c := by
    rw [hcv']
    exact div_nonneg (by linarith) hT.le
  have hc2 : value c ≤ 2 / T := by
    rw [hcv']
    exact div_le_div_of_nonneg_right (by linarith) hT.le
  have he : |value c - E| < 3 * ((2 : ℝ) ^ (0 - 1) / (2 : ℝ) ^ 1074) / 2 := by
    rw [hdiff, abs_div, abs_of_pos hT, div_lt_iff₀ hT]
    have hk : 3 * ((2 : ℝ) ^ (0 - 1) / (2 : ℝ) ^ 1074) / 2 * T = 3 * unitRoundoff64 := by
      rw [hu, h1074, show 0 - 1 = 0 from rfl, pow_zero]
      field_simp
    rw [hk]
    exact herr
  refine ⟨hclim, F64FullStep.one_step_binades E c 0 2 (by norm_num) (by norm_num)
    (by rw [value_zero_boundary]; exact hE.le) (fun _ => by rw [hbnd]; exact hE2)
    (hclim.trans (by decide)) (by rw [value_zero_boundary]; exact hc0) (by rw [hbnd]; exact hc2) he⟩

#print axioms compensated_one_step

/-- The bits of `Exp.exp` on the negative special path, from the reduction's table index and the
sign guard. -/
theorem special_negative_bits (x : Float) (hxlo : 512 ≤ |value x.toBits|)
    (hxhi : |value x.toBits| < 1024) (j : Fin 128)
    (hg : ¬ ((ExpCoreBounds.floatShifted x).toBits &&& 0x80000000 == 0) = true)
    (hsf : Finite (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits)))
    (htf : Finite (ExpCoreState.tailBits x.toBits))
    (ht : ExpCoreState.tailBits x.toBits = ExpTableBounds.tailBits j.val) :
    (Exp.exp x).toBits = Wasm.IEEE64.mul 0x0010000000000000
      (if Wasm.IEEE64.lt (Wasm.IEEE64.add (ExpSpecialScale.negativeScale
          (ExpCoreState.shiftedBits x.toBits)) (Wasm.IEEE64.mul (ExpSpecialScale.negativeScale
          (ExpCoreState.shiftedBits x.toBits)) (ExpEvaluationBounds.evaluation
          (ExpResidualBounds.residual x.toBits) (ExpTableBounds.tailBits j.val)))) one then
        compRounded (compSum (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits))
          (Wasm.IEEE64.mul (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits))
            (ExpEvaluationBounds.evaluation (ExpResidualBounds.residual x.toBits)
              (ExpTableBounds.tailBits j.val))))
      else Wasm.IEEE64.add (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits))
        (Wasm.IEEE64.mul (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits))
          (ExpEvaluationBounds.evaluation (ExpResidualBounds.residual x.toBits)
            (ExpTableBounds.tailBits j.val)))) := by
  have hSb : (Float.ofBits (ExpSpecialScale.negativeScale
      (ExpCoreBounds.floatShifted x).toBits)).toBits =
      ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits) := by
    rw [ExpCoreBounds.floatShifted_bits, F64Bits.toBits_ofBits]
    simp only [not_nan_of_finite hsf, Bool.false_eq_true, ite_false]
  have hTb : (ExpEvaluationBounds.floatEvaluation (ExpResidualBounds.floatResidual x)
      (Float.ofBits Exp.expTable[(ExpScaleBits.index
        (ExpCoreBounds.floatShifted x).toBits).toNat]!)).toBits =
      ExpEvaluationBounds.evaluation (ExpResidualBounds.residual x.toBits)
        (ExpTableBounds.tailBits j.val) := by
    rw [ExpEvaluationBounds.evaluation_bits, ExpResidualBounds.residual_bits,
      ExpCoreBounds.floatShifted_bits]
    change ExpEvaluationBounds.evaluation _ (Float.ofBits (ExpCoreState.tailBits x.toBits)).toBits = _
    rw [F64Bits.toBits_ofBits]
    simp only [not_nan_of_finite htf, Bool.false_eq_true, ite_false]
    rw [ht]
  rw [Exp.exp, ExpBranches.special_selected _ x (ExpBranches.special_exponent x.toBits hxlo hxhi),
    core_negative_eq x hg, negativeResult_bits, F64Bits.toBits_add, F64Bits.toBits_mul, hSb, hTb]

/-- `Wasm.IEEE64.lt y one` for a finite word is the test `value y < 1`. -/
theorem lt_one_iff (y : UInt64) (hyf : Finite y) :
    Wasm.IEEE64.lt y one = decide (value y < 1) := by
  unfold Wasm.IEEE64.lt
  rw [not_nan_of_finite hyf, show Wasm.IEEE64.isNaN one = false by decide +kernel, one_scaled]
  simp only [Bool.or_false, Bool.false_eq_true, ite_false]
  rw [decide_eq_decide, value, div_lt_one (by positivity)]
  constructor <;> intro h <;> exact_mod_cast h

/-- The negative special path: for finite `-768 ≤ a ≤ -512`, `Exp.exp` is within one step of the
nonnegative nearest-even reference of `exp a`. -/
theorem negative_one_step (x : Float) (hxf : Finite x.toBits)
    (hx : |value x.toBits| ≤ 768) (hxneg : value x.toBits ≤ -512) :
    (Exp.exp x).toBits.toNat ≤ limit ∧
      (Exp.exp x).toBits.toNat ≤
        (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat ≤
        (Exp.exp x).toBits.toNat + 1 := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hu0 : 0 < unitRoundoff64 := by rw [hu]; positivity
  have hxlo : 512 ≤ |value x.toBits| := by rw [abs_of_neg (by linarith)]; linarith
  obtain ⟨k, q, j, hkv, hk, ht, hki, hj, hkn⟩ := ExpCoreState.prefix_state x.toBits hxf hx
  have hq23 := ExpSpecialScale.negative_quotient x.toBits k q j hxf hx hxneg hkv hk
  have hqb := ExpSpecialScale.quotient_bounds k q j hk hkn
  have hkneg : k < 0 := by have := j.isLt; omega
  have hguard := ExpSpecialScale.sign_guard (ExpCoreState.shiftedBits x.toBits) k hki
    (hkn.trans (by norm_num))
  rw [ite_eq_left hkneg] at hguard
  have hg : ¬ ((ExpCoreBounds.floatShifted x).toBits &&& 0x80000000 == 0) = true := by
    rw [ExpCoreBounds.floatShifted_bits, hguard]
    decide
  obtain ⟨hsf, hsv, hslo, hshi⟩ :=
    ExpSpecialScale.negative_scale_value _ k q j hki hk hj
      ((by norm_num : (-2022 : Int) ≤ -1153).trans hqb.1) hq23
  have htf : Finite (ExpCoreState.tailBits x.toBits) := by
    rw [ht]
    exact (ExpTableBounds.entry_bounds j).2.1
  have hexp := special_negative_bits x hxlo (hx.trans_lt (by norm_num)) j hg hsf htf ht
  obtain ⟨hpf, hPm, hpre⟩ := ExpTableReconstruction.presum_scaled_error x.toBits _ k q 1022 j
    hxf hx hkv hk hsf hsv hslo hshi
  obtain ⟨hyf, hye⟩ := ExpSpecialReconstruction.negative_error x.toBits hxf hx hxneg
  have hrec : ExpSpecialReconstruction.reconstruction ExpSpecialScale.negativeScale x.toBits =
      Wasm.IEEE64.add (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits))
        (Wasm.IEEE64.mul (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits))
          (ExpEvaluationBounds.evaluation (ExpResidualBounds.residual x.toBits)
            (ExpTableBounds.tailBits j.val))) := by
    simp only [ExpSpecialReconstruction.reconstruction, ExpReconstructionBounds.reconstruction, ht]
  rw [hrec] at hyf hye
  generalize hs : ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits) = s at *
  generalize hp : Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation
    (ExpResidualBounds.residual x.toBits) (ExpTableBounds.tailBits j.val)) = p at *
  have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
  have hE : 0 < Real.exp (value x.toBits) := Real.exp_pos _
  have hlt := lt_one_iff _ hyf
  by_cases hy1 : value (Wasm.IEEE64.add s p) < 1
  · rw [hlt, decide_eq_true hy1, ite_eq_left rfl] at hexp
    have hS2 := (comp_sum_bounds s p hsf hpf hS hshi hPm hy1).2.2.2
    have hpre' : |value s + value p - (2 : ℝ) ^ (1022 : Int) * Real.exp (value x.toBits)| ≤
        11 / 16 * unitRoundoff64 := by
      have : (21 / 64) * unitRoundoff64 * value s ≤ (21 / 64) * unitRoundoff64 * 2 :=
        mul_le_mul_of_nonneg_left hS2.le (by positivity)
      linarith
    obtain ⟨hclim, hc1, hc2⟩ := compensated_one_step s p _ hsf hpf hS hshi hPm hy1 hE hpre'
    rw [hexp]
    exact ⟨hclim.le, hc1, hc2⟩
  · rw [hlt, decide_eq_false hy1] at hexp
    simp only [Bool.false_eq_true, ite_false] at hexp
    have hy1' : 1 ≤ value (Wasm.IEEE64.add s p) := le_of_not_gt hy1
    have hey := exponent_ge_of_one_le _ hy1'
    have hys := (normal_of_value (Wasm.IEEE64.add s p) (by
      have : (1 : ℝ) / 2 ^ 1022 < 1 := by norm_num
      linarith)).2
    have hefin : Wasm.IEEE64.exponent (Wasm.IEEE64.add s p) ≤ 2046 := by
      have h := hyf
      simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
      have : Wasm.IEEE64.exponent (Wasm.IEEE64.add s p) < 2048 := Nat.mod_lt _ (by norm_num)
      omega
    obtain ⟨hcf, hcv⟩ := F64PowerScale.mul_power_finite 1 (Wasm.IEEE64.add s p) (by norm_num)
      (by norm_num) hyf (by omega) (by omega) (by omega)
    rw [← scale_down_word] at hcf hcv
    rw [← hexp] at hcf hcv
    have hcv' : value (Exp.exp x).toBits =
        (2 : ℝ) ^ (-1022 : Int) * value (Wasm.IEEE64.add s p) := by
      rw [hcv, show ((1 : Nat) : Int) - 1023 = -1022 by norm_num]
    obtain ⟨hEn, hEz⟩ := ExpOneStep.target_bounds x.toBits hxf hx k q j hkv hk
    have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
    have hH := ExpCoreRange.head_bounds j
    have hEu : Real.exp (value x.toBits) ≤ (2 : ℝ) ^ q * (2 - 1 / 65536) := by
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
      have hR : (2 : ℝ) ^ (q + 1022) ≤ (2 : ℝ) ^ (-1 : Int) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hhalf : (2 : ℝ) ^ (-1 : Int) = 1 / 2 := by norm_num
      have hRpos : (0 : ℝ) < (2 : ℝ) ^ (q + 1022) := zpow_pos (by norm_num) _
      have h1 : (2 : ℝ) ^ (1022 : Int) * Real.exp (value x.toBits) ≤
          (2 : ℝ) ^ (q + 1022) * (2 - 1 / 65536) := by
        rw [← hzq, mul_assoc]
        exact mul_le_mul_of_nonneg_left hEu (by positivity)
      have h2 : value s ≤ (2 : ℝ) ^ (q + 1022) * (255 / 128) := by
        rw [hsv]
        exact mul_le_mul_of_nonneg_left hH.1 hRpos.le
      have h3 := abs_le.mp hye
      rw [hu] at h3
      rw [hhalf] at hR
      linarith
    have herr : |(2 : ℝ) ^ (-1022 : Int) * value (Wasm.IEEE64.add s p) -
        Real.exp (value x.toBits)| ≤
        (7 / 5) * unitRoundoff64 * ((2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) := by
      have hid : (2 : ℝ) ^ (-1022 : Int) * value (Wasm.IEEE64.add s p) -
          Real.exp (value x.toBits) = (2 : ℝ) ^ (-1022 : Int) *
            (value (Wasm.IEEE64.add s p) - (2 : ℝ) ^ (1022 : Int) * Real.exp (value x.toBits)) := by
        rw [mul_sub, ← mul_assoc, hinv, one_mul]
      rw [hid, abs_mul, abs_of_pos (zpow_pos (by norm_num) _)]
      calc
        _ ≤ (2 : ℝ) ^ (-1022 : Int) * ((7 / 5) * unitRoundoff64 * value s) :=
          mul_le_mul_of_nonneg_left hye (by positivity)
        _ = _ := by
          rw [hsv, ← hm1022]
          ring
    have hcpos : 0 < value (Exp.exp x).toBits := by
      rw [hcv']
      exact mul_pos (zpow_pos (by norm_num) _) (by linarith)
    have hclim := F64PositiveOrder.positive_finite_encoding _ hcf hcpos
    exact ⟨hclim.le, ExpOneStep.one_step_of_error (Real.exp (value x.toBits))
      ((2 : ℝ) ^ (-1022 : Int) * value (Wasm.IEEE64.add s p)) (Exp.exp x).toBits q j hq hEn hEz
      herr (Or.inl ⟨hclim, hcv'⟩)⟩

#print axioms special_negative_bits
#print axioms lt_one_iff
#print axioms negative_one_step

end Library.Numerics.Float64.Exp.ExpSpecialNegative
