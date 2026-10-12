import Verified.Examples.ExpTight
import Verified.Examples.ExpSpecialPositive
import Verified.Examples.ExpNegativeFinal
import LeanExe.ProofKit.F64NearestHalf
import LeanExe.ProofKit.F64NearestScale

/-!
Tight error bounds for `Exp.exp`, which is `Exp.expWith Exp.expTable`.  For
`-512 < x ≤ 709.7827` the result is the nearest word to a real within `u/32` of `exp x`,
relative to `exp x` (`exp_near`).  For `-708 ≤ x ≤ -512` the code multiplies a word `y ≥ 1` by
`2 ^ -1022` exactly, and `y` is the nearest word to a real within `u/32` of `2 ^ 1022 exp x`
(`negative_near`).  Over `-708 ≤ x ≤ 709.7827` the result lies within `1.033 u exp x` of `exp x`
(`exp_relative`).  Below `-708.4` the result is subnormal and above `709.7827` it can overflow,
so these ranges cover every normal result.
-/

namespace Verified.Examples.ExpTightFloat
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem exp_two_pow (n : ℕ) : Real.exp (n * Real.log 2) = 2 ^ n := by
  rw [Real.exp_nat_mul, Real.exp_log two_pos]

theorem exp_le_two_pow (X : ℝ) (n : ℕ) (h : X ≤ n * (6931471805 / 10 ^ 10)) :
    Real.exp X ≤ 2 ^ n := by
  have hl := ExpTight.log_two_bounds.1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← exp_two_pow]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem exp_le_inv_two_pow (X : ℝ) (n : ℕ) (h : X ≤ -(n * (6931471806 / 10 ^ 10))) :
    Real.exp X ≤ 1 / 2 ^ n := by
  have hl := ExpTight.log_two_bounds.2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Real.exp X ≤ Real.exp (-(n * Real.log 2)) := Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.exp_neg, exp_two_pow] at h1
  rwa [one_div]

theorem inv_two_pow_le_exp (X : ℝ) (n : ℕ) (h : -(n * (6931471805 / 10 ^ 10)) ≤ X) :
    1 / 2 ^ n ≤ Real.exp X := by
  have hl := ExpTight.log_two_bounds.1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Real.exp (-(n * Real.log 2)) ≤ Real.exp X := Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.exp_neg, exp_two_pow] at h1
  rwa [one_div]

/-- Below `709.7827`, `exp x` stays a relative `10 ^ -5` below the overflow power `2 ^ 1024`. -/
theorem exp_upper (X : ℝ) (hX : X ≤ 7097827 / 10 ^ 4) :
    Real.exp X ≤ 2 ^ 1024 * (1 - 1 / 10 ^ 5) := by
  have hl := ExpTight.log_two_bounds.1
  have h2 := exp_two_pow 1024
  push_cast at h2
  have hsplit : Real.exp (1024 * Real.log 2) =
      Real.exp X * Real.exp (1024 * Real.log 2 - X) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE := Real.add_one_le_exp (1024 * Real.log 2 - X)
  have hX0 := Real.exp_pos X
  have h1 : 1 ≤ Real.exp (1024 * Real.log 2 - X) * (1 - 1 / 10 ^ 5) := by linarith
  calc Real.exp X ≤ Real.exp X * (Real.exp (1024 * Real.log 2 - X) * (1 - 1 / 10 ^ 5)) :=
        le_mul_of_one_le_right hX0.le h1
    _ = 2 ^ 1024 * (1 - 1 / 10 ^ 5) := by rw [← h2, hsplit]; ring

/-- A word nearest to `s`, scaled by `a`, lies within `1.033 u E` of `E` when `s` lies within
`u/32` of `b E` and `a b = 1`. -/
theorem combine (a c s b E : ℝ) (ha : 0 < a) (hE : 0 ≤ E) (hab : a * b = 1)
    (h1 : |c - s| ≤ u * s) (h2 : |s - b * E| ≤ u / 32 * (b * E)) :
    |a * c - E| ≤ 1033 / 1000 * u * E := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hbE : a * (b * E) = E := by rw [← mul_assoc, hab, one_mul]
  have hid : a * c - E = a * (c - s) + a * (s - b * E) := by linear_combination hbE
  have hs := (abs_le.mp h2).2
  have hs' : s ≤ b * E * (1 + 1 / 2 ^ 58) := by rw [hu] at hs; linarith
  have has : a * s ≤ E * (1 + 1 / 2 ^ 58) := by
    calc a * s ≤ a * (b * E * (1 + 1 / 2 ^ 58)) := mul_le_mul_of_nonneg_left hs' ha.le
      _ = E * (1 + 1 / 2 ^ 58) := by linear_combination (1 + 1 / 2 ^ 58) * hbE
  rw [hid]
  calc |a * (c - s) + a * (s - b * E)| ≤ |a * (c - s)| + |a * (s - b * E)| := abs_add_le _ _
    _ = a * |c - s| + a * |s - b * E| := by rw [abs_mul, abs_mul, abs_of_pos ha]
    _ ≤ a * (u * s) + a * (u / 32 * (b * E)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha.le) (mul_le_mul_of_nonneg_left h2 ha.le)
    _ = u * (a * s) + u / 32 * (a * (b * E)) := by ring
    _ ≤ 1033 / 1000 * u * E := by rw [hbE, hu]; nlinarith

/-- The ordinary and tiny paths, `abs x < 512`. -/
theorem small_near (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| < 512) :
    ∃ s : ℝ, Nearest s (Exp.exp x).toBits ∧
      |s - Real.exp (value x.toBits)| ≤ u / 32 * Real.exp (value x.toBits) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have he : Wasm.IEEE64.exponent x.toBits < 1032 :=
    F64ExponentBounds.exponent_lt_of_magnitude_lt x.toBits 1032 (by decide) (by
      rw [ExpBranches.small_boundary, abs_of_pos (by norm_num : (0 : ℝ) < 512)]
      exact hx)
  by_cases ht : Wasm.IEEE64.exponent x.toBits < 969
  · have hxt : |value x.toBits| ≤ 1 / (2 : ℝ) ^ 54 := by
      have h := F64ExponentBounds.magnitude_le_boundary x.toBits 969 (by decide) ht
      rw [ExpBranches.tiny_boundary, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ 54)] at h
      exact h
    have hxb := abs_le.mp hxt
    rw [Exp.exp, ExpBranches.tiny_selected _ x ht, ExpTinyError.float_result_bits]
    unfold ExpTinyError.result
    have hone := ExpTinyError.one_value
    have hn := F64NearestSum.add_nearest 0x3FF0000000000000 x.toBits
      ExpSpecialNegative.one_finite hxf (by rw [hone]; linarith) (by rw [hone]; linarith)
    rw [hone] at hn
    refine ⟨_, hn, ?_⟩
    have hq := Real.abs_exp_sub_one_sub_id_le (x := value x.toBits) (by linarith)
    have hsq : value x.toBits ^ 2 ≤ (1 / 2 ^ 54) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hxt 2
    have hE := Real.add_one_le_exp (value x.toBits)
    rw [show 1 + value x.toBits - Real.exp (value x.toBits) =
      -(Real.exp (value x.toBits) - 1 - value x.toBits) by ring, abs_neg, hu]
    nlinarith
  · have hlo : 969 ≤ Wasm.IEEE64.exponent x.toBits := Nat.le_of_not_gt ht
    rw [Exp.exp, ExpBranches.ordinary_selected _ x hlo he]
    obtain ⟨k, q, j, hkv, hk, ht', hsf, hs, hslo, hshi⟩ :=
      ExpCoreState.reduction_state x.toBits hxf hx.le
    have htf : Finite (ExpCoreState.tailBits x.toBits) := by
      rw [ht']
      exact (ExpTableBounds.entry_bounds j).2.1
    rw [ExpCoreBounds.core_bits x hsf htf]
    obtain ⟨-, hn, hE⟩ := ExpTight.reconstruction_near x.toBits _ k q 0 j hxf
      (hx.le.trans (by norm_num)) hkv hk hsf (by rw [add_zero]; exact hs) hslo hshi
    rw [zpow_zero, one_mul] at hE
    refine ⟨_, ?_, hE⟩
    simp only [ExpCoreBounds.core, ht']
    exact hn

/-- The positive special path, `512 ≤ x ≤ 709.7827`: the result is `2 ^ 1009 y` for a word `y`
nearest to a real within `u/32` of `2 ^ -1009 exp x`, and the result is itself nearest to
`2 ^ 1009` times that real. -/
theorem positive_near (x : Float) (hxf : Finite x.toBits) (hxpos : 512 ≤ value x.toBits)
    (hxhi : value x.toBits ≤ 7097827 / 10 ^ 4) :
    ∃ (y : UInt64) (s : ℝ), Nearest s y ∧
      |s - Real.exp (value x.toBits) / 2 ^ 1009| ≤
        u / 32 * (Real.exp (value x.toBits) / 2 ^ 1009) ∧
      Finite (Exp.exp x).toBits ∧ value (Exp.exp x).toBits = 2 ^ 1009 * value y ∧
      Nearest (2 ^ 1009 * s) (Exp.exp x).toBits := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hx : |value x.toBits| ≤ 768 := by rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨k, q, j, hkv, hk, ht, hki, hj, hkn⟩ := ExpCoreState.prefix_state x.toBits hxf hx
  have hq9 := ExpSpecialScale.positive_quotient x.toBits k q j hxf hx hxpos hkv hk
  have hqb := ExpSpecialScale.quotient_bounds k q j hk hkn
  obtain ⟨hsf, hsv, hslo, hshi⟩ :=
    ExpSpecialScale.positive_scale_value _ k q j hki hk hj hq9 (hqb.2.trans (by norm_num))
  have htf : Finite (ExpCoreState.tailBits x.toBits) := by
    rw [ht]
    exact (ExpTableBounds.entry_bounds j).2.1
  have hexp : (Exp.exp x).toBits = Wasm.IEEE64.mul 0x7F00000000000000
      (ExpSpecialReconstruction.floatReconstruction ExpSpecialScale.positiveScale x).toBits := by
    rw [ExpSpecialPositiveCore.exp_positive_eq x hxf hx hxpos, F64Bits.toBits_mul,
      F64Bits.toBits_ofBits]
    simp only [show Wasm.IEEE64.isNaN 0x7F00000000000000 = false by decide, Bool.false_eq_true,
      ite_false]
  rw [ExpSpecialReconstruction.reconstruction_bits _ x hsf htf] at hexp
  simp only [ExpSpecialReconstruction.reconstruction, ht] at hexp
  obtain ⟨hyf, hn, he⟩ := ExpTight.reconstruction_near x.toBits _ k q (-1009) j hxf hx hkv hk
    hsf (by simpa only [sub_eq_add_neg] using hsv) hslo hshi
  set y := ExpReconstructionBounds.reconstruction
    (ExpSpecialScale.positiveScale (ExpCoreState.shiftedBits x.toBits))
    (ExpResidualBounds.residual x.toBits) (ExpTableBounds.tailBits j.val) with hy
  have hz : (2 : ℝ) ^ (-1009 : Int) * Real.exp (value x.toBits) =
      Real.exp (value x.toBits) / 2 ^ 1009 := by
    rw [zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_comm]
  rw [hz] at he
  set s := value (ExpSpecialScale.positiveScale (ExpCoreState.shiftedBits x.toBits)) +
    value (Wasm.IEEE64.mul (ExpSpecialScale.positiveScale (ExpCoreState.shiftedBits x.toBits))
      (ExpEvaluationBounds.evaluation (ExpResidualBounds.residual x.toBits)
        (ExpTableBounds.tailBits j.val))) with hS
  have hE1 : 1 ≤ Real.exp (value x.toBits) := Real.one_le_exp (by linarith)
  have hEu := exp_upper _ hxhi
  obtain ⟨hsb1, hsb2⟩ := abs_le.mp he
  rw [hu] at hsb1 hsb2
  have hslo' : 1 / 2 ^ 1021 ≤ s := by
    have : 1 / 2 ^ 1009 ≤ Real.exp (value x.toBits) / 2 ^ 1009 := by gcongr
    linarith
  have hshi' : s ≤ 2 ^ 15 * (1 - 1 / 10 ^ 6) := by linarith
  have hyr := F64NearestHalf.nearest_relative s y hn (by linarith) (by linarith)
  obtain ⟨hyb1, hyb2⟩ := abs_le.mp hyr
  rw [hu] at hyb1 hyb2
  have hysign := (nearest_finite s y hn).2
  have hye : Wasm.IEEE64.exponent y + 1009 < 2047 := by
    by_contra hc
    have hv := F64Magnitude.value_ge_of_exponent y 1038 15 (by norm_num) (by norm_num)
      (by norm_num) hysign (by omega)
    norm_num at hv
    linarith
  obtain ⟨hcf, hcv, hcn⟩ := F64NearestScale.scale_nearest s y 1009 (by norm_num) (by norm_num) hn
    hslo' hye
  have hword : Wasm.IEEE64.mul 0x7F00000000000000 y =
      Wasm.IEEE64.mul y (Wasm.IEEE64.encodeFinite false (1023 + 1009) 0) := by
    rw [F64NearestScale.mul_comm_finite 0x7F00000000000000 y
      (by unfold CodeLib.IEEE64.Finite; decide +kernel) hyf,
      ExpSpecialPositive.scale_up_word]
  rw [hword] at hexp
  rw [hexp]
  exact ⟨y, s, hn, he, hcf, hcv, hcn⟩

/-- `exp_near`: for `-512 < x ≤ 709.7827`, `Exp.exp x` is the nearest word to a real within
`u/32` of `exp x`, relative to `exp x`. -/
theorem exp_near (x : Float) (hxf : Finite x.toBits) (hxlo : -512 < value x.toBits)
    (hxhi : value x.toBits ≤ 7097827 / 10 ^ 4) :
    ∃ s : ℝ, Nearest s (Exp.exp x).toBits ∧
      |s - Real.exp (value x.toBits)| ≤ u / 32 * Real.exp (value x.toBits) := by
  by_cases h512 : value x.toBits < 512
  · exact small_near x hxf (abs_lt.mpr ⟨hxlo, h512⟩)
  · obtain ⟨y, s, -, he, -, -, hcn⟩ := positive_near x hxf (le_of_not_gt h512) hxhi
    refine ⟨_, hcn, ?_⟩
    have hid : (2 : ℝ) ^ 1009 * s - Real.exp (value x.toBits) =
        2 ^ 1009 * (s - Real.exp (value x.toBits) / 2 ^ 1009) := by
      field_simp
    rw [hid, abs_mul, abs_of_pos (by positivity)]
    calc (2 : ℝ) ^ 1009 * |s - Real.exp (value x.toBits) / 2 ^ 1009| ≤
        2 ^ 1009 * (u / 32 * (Real.exp (value x.toBits) / 2 ^ 1009)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = u / 32 * Real.exp (value x.toBits) := by field_simp

/-- The negative special path, `-708 ≤ x ≤ -512`: the result is `2 ^ -1022 y` for a word `y ≥ 1`
nearest to a real within `u/32` of `2 ^ 1022 exp x`. -/
theorem negative_near (x : Float) (hxf : Finite x.toBits) (hxlo : -708 ≤ value x.toBits)
    (hxneg : value x.toBits ≤ -512) :
    ∃ (y : UInt64) (s : ℝ), Nearest s y ∧ 1 ≤ value y ∧
      |s - 2 ^ 1022 * Real.exp (value x.toBits)| ≤
        u / 32 * (2 ^ 1022 * Real.exp (value x.toBits)) ∧
      Finite (Exp.exp x).toBits ∧ value (Exp.exp x).toBits = value y / 2 ^ 1022 := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hx : |value x.toBits| ≤ 768 := by rw [abs_of_neg (by linarith)]; linarith
  have hxlo' : 512 ≤ |value x.toBits| := by rw [abs_of_neg (by linarith)]; linarith
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
  have hexp := ExpSpecialNegative.special_negative_bits x hxlo' (hx.trans_lt (by norm_num)) j hg
    hsf htf ht
  obtain ⟨hyf, hn, he⟩ := ExpTight.reconstruction_near x.toBits _ k q 1022 j hxf hx hkv hk
    hsf hsv hslo hshi
  rw [ExpSpecialNegative.two_zpow_1022] at he
  simp only [ExpReconstructionBounds.reconstruction] at hyf hn
  set sw := ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits) with hsw
  set y := Wasm.IEEE64.add sw (Wasm.IEEE64.mul sw (ExpEvaluationBounds.evaluation
    (ExpResidualBounds.residual x.toBits) (ExpTableBounds.tailBits j.val))) with hy
  set s := value sw + value (Wasm.IEEE64.mul sw (ExpEvaluationBounds.evaluation
    (ExpResidualBounds.residual x.toBits) (ExpTableBounds.tailBits j.val))) with hS
  have hE0 := Real.exp_pos (value x.toBits)
  have hElo : 139 / 100 ≤ 2 ^ 1022 * Real.exp (value x.toBits) := by
    have h2 := exp_two_pow 1022
    push_cast at h2
    rw [← h2, ← Real.exp_add]
    have := Real.add_one_le_exp (1022 * Real.log 2 + value x.toBits)
    have := ExpTight.log_two_bounds.1
    linarith
  have hEhi : Real.exp (value x.toBits) ≤ 1 / 2 ^ 1 :=
    exp_le_inv_two_pow _ 1 (by push_cast; linarith)
  obtain ⟨hsb1, hsb2⟩ := abs_le.mp he
  rw [hu] at hsb1 hsb2
  have hyr := F64NearestHalf.nearest_relative s y hn (by linarith) (by linarith)
  obtain ⟨hyb1, hyb2⟩ := abs_le.mp hyr
  rw [hu] at hyb1 hyb2
  have hy1 : 1 ≤ value y := by linarith
  have hlt := ExpSpecialNegative.lt_one_iff _ hyf
  rw [hlt, decide_eq_false (not_lt.mpr hy1)] at hexp
  simp only [Bool.false_eq_true, ite_false] at hexp
  have hey := F64Magnitude.exponent_ge_of_one_le _ hy1
  have hefin : Wasm.IEEE64.exponent y ≤ 2046 := by
    have h := hyf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent y < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  obtain ⟨hcf, hcv⟩ := F64PowerScale.mul_power_finite 1 y (by norm_num) (by norm_num) hyf
    (by omega) (by omega) (by omega)
  rw [← ExpSpecialNegative.scale_down_word, ← hexp] at hcf hcv
  refine ⟨y, s, hn, hy1, he, hcf, ?_⟩
  rw [hcv, show ((1 : Nat) : Int) - 1023 = -1022 by norm_num, zpow_neg, zpow_ofNat]
  ring

/-- `exp_relative`: for `-708 ≤ x ≤ 709.7827`, `Exp.exp x` lies within `1.033 u exp x` of
`exp x`. -/
theorem exp_relative (x : Float) (hxf : Finite x.toBits) (hxlo : -708 ≤ value x.toBits)
    (hxhi : value x.toBits ≤ 7097827 / 10 ^ 4) :
    Finite (Exp.exp x).toBits ∧
      |value (Exp.exp x).toBits - Real.exp (value x.toBits)| ≤
        1033 / 1000 * u * Real.exp (value x.toBits) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hE0 := Real.exp_pos (value x.toBits)
  by_cases hneg : value x.toBits ≤ -512
  · obtain ⟨y, s, hn, -, he, hcf, hcv⟩ := negative_near x hxf hxlo hneg
    have hEhi : Real.exp (value x.toBits) ≤ 1 / 2 ^ 1 :=
      exp_le_inv_two_pow _ 1 (by push_cast; linarith)
    have hElo : 1 / 2 ^ 1022 ≤ Real.exp (value x.toBits) :=
      inv_two_pow_le_exp _ 1022 (by push_cast; linarith)
    obtain ⟨hsb1, hsb2⟩ := abs_le.mp he
    rw [hu] at hsb1 hsb2
    have hyr := F64NearestHalf.nearest_relative s y hn (by linarith) (by linarith)
    refine ⟨hcf, ?_⟩
    rw [hcv, div_eq_inv_mul]
    exact combine _ _ s _ _ (by positivity) hE0.le (inv_mul_cancel₀ (by positivity)) hyr he
  · replace hneg : -512 < value x.toBits := lt_of_not_ge hneg
    by_cases h512 : value x.toBits < 512
    · obtain ⟨s, hn, he⟩ := small_near x hxf (abs_lt.mpr ⟨hneg, h512⟩)
      have hEhi : Real.exp (value x.toBits) ≤ 2 ^ 1021 :=
        exp_le_two_pow _ 1021 (by push_cast; linarith)
      have hElo : 1 / 2 ^ 1021 ≤ Real.exp (value x.toBits) :=
        inv_two_pow_le_exp _ 1021 (by push_cast; linarith)
      obtain ⟨hsb1, hsb2⟩ := abs_le.mp he
      rw [hu] at hsb1 hsb2
      have hyr := F64NearestHalf.nearest_relative s _ hn (by linarith) (by linarith)
      refine ⟨(nearest_finite s _ hn).1, ?_⟩
      have h := combine 1 _ s 1 _ one_pos hE0.le (by norm_num) hyr (by rw [one_mul]; exact he)
      rwa [one_mul] at h
    · obtain ⟨y, s, hn, he, hcf, hcv, -⟩ := positive_near x hxf (le_of_not_gt h512) hxhi
      have hE1 : 1 ≤ Real.exp (value x.toBits) := Real.one_le_exp (by linarith)
      have hEu := exp_upper _ hxhi
      obtain ⟨hsb1, hsb2⟩ := abs_le.mp he
      rw [hu] at hsb1 hsb2
      have hslo' : 1 / 2 ^ 1009 ≤ Real.exp (value x.toBits) / 2 ^ 1009 := by gcongr
      have hyr := F64NearestHalf.nearest_relative s y hn (by linarith) (by linarith)
      refine ⟨hcf, ?_⟩
      rw [hcv]
      have he' : |s - 1 / 2 ^ 1009 * Real.exp (value x.toBits)| ≤
          u / 32 * (1 / 2 ^ 1009 * Real.exp (value x.toBits)) := by
        rw [one_div_mul_eq_div]
        exact he
      exact combine _ _ s _ _ (by positivity) hE0.le (mul_one_div_cancel (by positivity)) hyr he'

#print axioms exp_upper
#print axioms combine
#print axioms small_near
#print axioms positive_near
#print axioms exp_near
#print axioms negative_near
#print axioms exp_relative

end Verified.Examples.ExpTightFloat
