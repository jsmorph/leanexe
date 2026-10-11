import Verified.Examples.Exp10Core

/-!
The three paths of `Exp2.exp10Core` on `Exp.expTable`, each within one step of the reference of
`10 ^ x`: the ordinary reconstruction `s · tmp + s` for `|x| < 256`, the doubled reconstruction
for `256 ≤ x ≤ 0x1.34413509f79fep8`, and the scaled-down reconstruction for `-350 ≤ x ≤ -256`.
-/

namespace Verified.Examples.Exp10Paths
open CodeLib.IEEE64
open LeanExe.ProofKit Exp10Constants Exp10Reduction Exp10Core

set_option exponentiation.threshold 4096

theorem checked_inverse : 425 ≤ PolyBound.ratOfWord invWord := by
  unfold invWord
  decide +kernel

/-- `1 / ratio`, `128 / log10 2`, lies between 425 and 426. -/
theorem inverse_bounds : 425 - 1 / 2 ^ 40 ≤ 1 / ratio ∧ 1 / ratio ≤ 426 + 1 / 2 ^ 40 := by
  have h1 := Exp2Approximation.cast_le checked_inverse
  push_cast at h1
  rw [PolyBound.ratOfWord_cast] at h1
  have h2 := coefficient_bounds.2.2.2.2.2.2.2
  have h3 := abs_le.mp inv_close
  have h4 := (abs_le.mp h2).2
  constructor <;> linarith

/-- `10 ^ x` from the reduction. -/
theorem target_eq (a : ℝ) (k q : Int) (j : Fin 128) (hk : k = 128 * q + j.val) :
    (10 : ℝ) ^ a = (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) *
      Real.exp ((a - (k : ℝ) * ratio) * Real.log 10) := by
  have h2q : (2 : ℝ) ^ q = Real.exp ((q : ℝ) * Real.log 2) := by
    rw [RealExpError.exp_int_mul, Real.exp_log (by norm_num)]
  have hL10 : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hr : ratio * Real.log 10 = Real.log 2 / 128 := by
    rw [ratio]
    field_simp
  rw [Real.rpow_def_of_pos (by norm_num), h2q, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [sub_mul, mul_assoc, hr, hk]
  push_cast
  ring

theorem rho_bounds (y : ℝ) (hy : |y| ≤ 1 / 364) :
    319 / 320 ≤ Real.exp y ∧ Real.exp y ≤ 257 / 256 := by
  have hl := Real.add_one_le_exp y
  have h1 := (abs_le.mp hy).1
  have h2 := (abs_le.mp hy).2
  constructor
  · linarith
  · rcases le_or_gt y 0 with h | h
    · have := Real.exp_le_one_iff.mpr h
      linarith
    · have hu := Real.exp_bound_div_one_sub_of_interval' h (by linarith)
      have hd : 1 / (1 - y) ≤ 257 / 256 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith

theorem rho_arg (x : Float) (k : Int) (hiq : |value x.toBits - (k : ℝ) * ratio| ≤ 1 / 850) :
    |(value x.toBits - (k : ℝ) * ratio) * Real.log 10| ≤ 1 / 364 := by
  obtain ⟨hl, hh⟩ := log_ten_enclosure
  have hb := checked_reduction
  have hl' : (23 / 10 : ℝ) ≤ Real.log 10 := le_trans (by
    have := Exp2Approximation.cast_le hb.2.2.2.2.2.1
    push_cast at this
    exact this) hl
  have hh' : Real.log 10 ≤ 233 / 100 := hh.trans (by
    have := Exp2Approximation.cast_le hb.2.2.2.2.2.2.1
    push_cast at this
    exact this)
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 10)]
  calc
    _ ≤ 1 / 850 * (233 / 100) := mul_le_mul hiq hh' (by linarith) (by norm_num)
    _ ≤ 1 / 364 := by norm_num

/-- Bounds on `k` from bounds on `x / ratio`. -/
theorem k_bounds (k : Int) (a : ℝ) (hk : |(k : ℝ) - a| ≤ 1 / 2 + 1 / 2 ^ 31) (lo hi : Int)
    (hlo : (lo : ℝ) - 1 / 2 + 1 / 2 ^ 31 < a) (hhi : a < (hi : ℝ) + 1 / 2 - 1 / 2 ^ 31) :
    lo ≤ k ∧ k ≤ hi := by
  have h := abs_le.mp hk
  have h1 : (lo : ℝ) - 1 < k := by linarith
  have h2 : (k : ℝ) < hi + 1 := by linarith
  have h1' : lo - 1 < k := by exact_mod_cast h1
  have h2' : k < hi + 1 := by exact_mod_cast h2
  omega

theorem ordinary_within (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| < 256) :
    F64SignedRounding.WithinSteps 1 ((10 : ℝ) ^ value x.toBits)
      (Exp2.exp10Core Exp.expTable x false).toBits := by
  obtain ⟨k, q, j, hk, hiq, hdiff, hkn, hki, hj, hwf, hW, hWe⟩ :=
    core_state x hxf (hx.le.trans (by norm_num))
  obtain ⟨hil, hih⟩ := inverse_bounds
  obtain ⟨-, -, hrpos⟩ := ratio_bounds
  have hxr : |value x.toBits / ratio| ≤ 256 * (426 + 1 / 2 ^ 40) := by
    rw [div_eq_mul_one_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ratio)]
    exact mul_le_mul hx.le hih (by positivity) (by norm_num)
  obtain ⟨hxb1, hxb2⟩ := abs_le.mp hxr
  obtain ⟨hklo, hkhi⟩ := k_bounds k _ hdiff (-109058) 109058 (by norm_num at hxb1 ⊢; linarith)
    (by norm_num at hxb2 ⊢; linarith)
  have hj' := j.isLt
  have hqlo : -853 ≤ q := by omega
  have hqhi : q ≤ 853 := by omega
  obtain ⟨hsf, hsv⟩ := ArmScale.ordinary_scale _ k q j hki hk hj (by omega) (by omega)
  rw [← scale_eq] at hsf hsv
  obtain ⟨hρl, hρu⟩ := rho_bounds _ (rho_arg x k hiq)
  -- the product `s · tmp` is finite, so the sum commutes
  have hH := (ExpTableBounds.entry_bounds j).2.2.2.1
  have hQ : (2 : ℝ) ^ q ≤ (2 : ℝ) ^ (853 : Int) := zpow_le_zpow_right₀ (by norm_num) hqhi
  have hsw : |value (scaleBits (floatShifted x).toBits) * value (tmpFloat x).toBits| <
      (2 : ℝ) ^ 1022 := by
    rw [hsv, abs_mul, abs_mul, abs_of_pos (zpow_pos (by norm_num) _),
      abs_of_pos (by linarith [(ExpTableBounds.entry_bounds j).2.2.1])]
    have h853 : (2 : ℝ) ^ (853 : Int) = 2 ^ 853 := zpow_natCast 2 853
    calc
      _ ≤ (2 : ℝ) ^ 853 * 2 * (1 / 64) := by
        rw [← h853]
        exact mul_le_mul (mul_le_mul hQ hH (by linarith [(ExpTableBounds.entry_bounds j).2.2.1])
          (by positivity)) hW (abs_nonneg _) (by positivity)
      _ < (2 : ℝ) ^ 1022 := by norm_num
  have hpf := (F64MulBounds.mul_real_mixed _ _ hsf hwf hsw).1
  rw [core_eq, ite_eq_right (by decide), F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, not_nan_of_finite hsf]
  simp only [Bool.false_eq_true, ite_false]
  rw [add_comm_finite _ _ hpf hsf, target_eq (value x.toBits) k q j hk]
  exact ArmReconstruction.ordinary_within _ _ q j _ hsf hwf hsv (by omega) (by omega) hW hWe
    hρl hρu

/-- `2 ^ (-2 ^ -43) ≤ 1 - 2 ^ -44` with the exponent's argument `2 ^ -43`. -/
theorem exp_neg_small : Real.exp (-(1 / 2 ^ 43)) ≤ 1 - 1 / 2 ^ 44 := by
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = -(1 / 2 ^ 43) := ⟨_, rfl⟩
  rw [← hydef]
  have hy : |y| ≤ 1 / 2 ^ 43 := by rw [hydef, abs_neg, abs_of_pos (by positivity)]
  have hb := Real.exp_bound (x := y) (hy.trans (by norm_num)) (n := 2) (by norm_num)
  have hs : ∑ i ∈ Finset.range 2, y ^ i / (i.factorial : ℝ) = 1 + y := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one,
      Nat.cast_one, div_one, zero_add, Nat.succ_eq_add_one, Nat.cast_mul]
    ring
  rw [hs] at hb
  have h1 := (abs_le.mp hb).2
  have hy2 : |y| ^ 2 ≤ (1 / 2 ^ 43) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hc : |y| ^ 2 * ((Nat.succ 2 : Nat) / ((Nat.factorial 2 : Nat) * (2 : Nat)) : ℝ) ≤
      (1 / 2 ^ 43) ^ 2 * 1 :=
    mul_le_mul hy2 (by norm_num [Nat.factorial]) (by positivity) (by positivity)
  have hnum : (1 : ℝ) + -(1 / 2 ^ 43) + (1 / 2 ^ 43) ^ 2 * 1 ≤ 1 - 1 / 2 ^ 44 := by norm_num
  rw [hydef] at h1 hc ⊢
  linarith

/-- `10 ^ x ≤ 2 ^ 1024 - 2 ^ 980` below the overflow bound. -/
theorem top_bound (a : ℝ) (ha : a ≤ value belowOflowWord) :
    Real.exp ((a * Real.log 10)) ≤ 2 ^ 1024 - 2 ^ 980 := by
  obtain ⟨hl, hh⟩ := log_ten_enclosure
  obtain ⟨hl2, hh2⟩ := ExpReductionBounds.log_two_enclosure
  have hb := checked_reduction
  have hp := Exp2Approximation.cast_le hb.2.2.2.2.2.2.2.2.1
  push_cast at hp
  rw [PolyBound.ratOfWord_cast] at hp
  have hpos : 0 ≤ value belowOflowWord := by
    have hs : Wasm.IEEE64.scaledValue belowOflowWord = 5422874305198590 * 2 ^ 1030 := by
      unfold belowOflowWord
      decide +kernel
    rw [value, hs]
    positivity
  have hL10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have h1 : a * Real.log 10 ≤ 1024 * Real.log 2 - 1 / 2 ^ 43 := by
    have hal : a * Real.log 10 ≤ value belowOflowWord * Real.log 10 :=
      mul_le_mul_of_nonneg_right ha hL10.le
    have hbl : value belowOflowWord * Real.log 10 ≤ value belowOflowWord * upperLogTen :=
      mul_le_mul_of_nonneg_left hh hpos
    linarith
  have h2 : Real.exp (1024 * Real.log 2) = 2 ^ 1024 := by
    have := RealExpError.exp_pow_two 1024
    push_cast at this
    exact this
  calc
    _ ≤ Real.exp (1024 * Real.log 2 - 1 / 2 ^ 43) := Real.exp_le_exp.mpr h1
    _ = 2 ^ 1024 * Real.exp (-(1 / 2 ^ 43)) := by
      rw [sub_eq_add_neg, Real.exp_add, h2]
    _ ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 44) := mul_le_mul_of_nonneg_left exp_neg_small (by positivity)
    _ = 2 ^ 1024 - 2 ^ 980 := by norm_num

theorem positive_within (x : Float) (hxf : Finite x.toBits) (hxlo : 256 ≤ value x.toBits)
    (hxhi : value x.toBits ≤ value belowOflowWord) :
    F64SignedRounding.WithinSteps 1 ((10 : ℝ) ^ value x.toBits)
      (Exp2.exp10Core Exp.expTable x true).toBits := by
  have hE := top_bound _ hxhi
  have hbelow : value belowOflowWord ≤ 309 := by
    have hs : Wasm.IEEE64.scaledValue belowOflowWord = 5422874305198590 * 2 ^ 1030 := by
      unfold belowOflowWord
      decide +kernel
    rw [value, hs]
    norm_num
  have hx : |value x.toBits| ≤ 400 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨k, q, j, hk, hiq, hdiff, hkn, hki, hj, hwf, hW, hWe⟩ := core_state x hxf hx
  obtain ⟨hil, hih⟩ := inverse_bounds
  obtain ⟨-, -, hrpos⟩ := ratio_bounds
  -- `x / ratio < 131072`, from `10 ^ x ≤ 2 ^ 1024 - 2 ^ 980`
  have hxr : value x.toBits / ratio < 131072 := by
    have hL10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : value x.toBits * Real.log 10 < 1024 * Real.log 2 := by
      by_contra hn
      push Not at hn
      have := Real.exp_le_exp.mpr hn
      have h2 : Real.exp (1024 * Real.log 2) = 2 ^ 1024 := by
        have := RealExpError.exp_pow_two 1024
        push_cast at this
        exact this
      rw [h2] at this
      have : (2 : ℝ) ^ 1024 - 2 ^ 980 < 2 ^ 1024 := by norm_num
      linarith
    rw [ratio, div_div_eq_mul_div, div_lt_iff₀ hL2]
    nlinarith
  have hxr' : 256 * (425 - 1 / 2 ^ 40) ≤ value x.toBits / ratio := by
    rw [div_eq_mul_one_div (value x.toBits) ratio]
    exact mul_le_mul hxlo hil (by norm_num) (by linarith)
  obtain ⟨hklo, hkhi⟩ := k_bounds k _ hdiff 108799 131072 (by norm_num at hxr' ⊢; linarith)
    (by norm_num at hxr ⊢; linarith)
  have hj' := j.isLt
  have hqlo : 849 ≤ q := by omega
  have hqhi : q ≤ 1024 := by omega
  have hguard := ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
  have hk0 : ¬ k < 0 := by omega
  rw [ite_eq_right hk0] at hguard
  obtain ⟨hsf, hsv⟩ := ArmScale.half_scale _ k q j hki hk hj (by omega) hqhi
  have hhalf : ArmScale.halfScale (floatShifted x).toBits =
      scaleBits (floatShifted x).toBits - ((1 : UInt64) <<< (52 : UInt64)) := by
    rw [ArmScale.halfScale, scale_eq]
  rw [hhalf] at hsf hsv
  obtain ⟨hρl, hρu⟩ := rho_bounds _ (rho_arg x k hiq)
  have hE' : (10 : ℝ) ^ value x.toBits ≤ 2 ^ 1024 - 2 ^ 980 := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    exact hE
  rw [target_eq (value x.toBits) k q j hk] at hE' ⊢
  rw [core_eq, ite_eq_left rfl, Exp2Paths.special_positive_eq _ _ _ (by rw [hguard]; rfl),
    F64Bits.toBits_mul, Exp2Paths.two_bits, Exp2Paths.sum_bits _ _ hsf]
  exact ArmSpecial.positive_within _ _ q j _ hsf hwf hsv (by omega) hqhi hW hWe hρl hρu hE'

theorem negative_within (x : Float) (hxf : Finite x.toBits) (hxlo : -350 ≤ value x.toBits)
    (hxhi : value x.toBits ≤ -256) :
    F64SignedRounding.WithinSteps 1 ((10 : ℝ) ^ value x.toBits)
      (Exp2.exp10Core Exp.expTable x true).toBits := by
  have hx : |value x.toBits| ≤ 400 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨k, q, j, hk, hiq, hdiff, hkn, hki, hj, hwf, hW, hWe⟩ := core_state x hxf hx
  obtain ⟨hil, hih⟩ := inverse_bounds
  obtain ⟨-, -, hrpos⟩ := ratio_bounds
  have hr1 : 0 < 1 / ratio := one_div_pos.mpr hrpos
  have hxr : value x.toBits / ratio ≤ -256 * (425 - 1 / 2 ^ 40) := by
    rw [div_eq_mul_one_div (value x.toBits) ratio]
    have h1 := mul_le_mul_of_nonneg_right hxhi hr1.le
    have h2 := mul_le_mul_of_nonneg_left hil (show (0 : ℝ) ≤ 256 by norm_num)
    linarith
  have hxr' : -350 * (426 + 1 / 2 ^ 40) ≤ value x.toBits / ratio := by
    rw [div_eq_mul_one_div (value x.toBits) ratio]
    have h1 := mul_le_mul_of_nonneg_right hxlo hr1.le
    have h2 := mul_le_mul_of_nonneg_left hih (show (0 : ℝ) ≤ 350 by norm_num)
    linarith
  obtain ⟨hklo, hkhi⟩ := k_bounds k _ hdiff (-149101) (-108799)
    (by norm_num at hxr' ⊢; linarith) (by norm_num at hxr ⊢; linarith)
  have hj' := j.isLt
  have hqlo : -1165 ≤ q := by omega
  have hqhi : q ≤ -850 := by omega
  have hguard := ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
  have hk0 : k < 0 := by omega
  rw [ite_eq_left hk0] at hguard
  obtain ⟨hsf, hsv, -, -⟩ :=
    ExpSpecialScale.negative_scale_value _ k q j hki hk hj (by omega) (by omega)
  have hneg : ExpSpecialScale.negativeScale (floatShifted x).toBits =
      scaleBits (floatShifted x).toBits + ((1022 : UInt64) <<< (52 : UInt64)) := by
    rw [ExpSpecialScale.negativeScale, scale_eq]
  rw [hneg] at hsf hsv
  obtain ⟨hρl, hρu⟩ := rho_bounds _ (rho_arg x k hiq)
  rw [core_eq, ite_eq_left rfl, Exp2Paths.special_negative_eq _ _ _ (by rw [hguard]; decide),
    ExpSpecialNegative.negativeResult_bits, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, not_nan_of_finite hsf]
  simp only [Bool.false_eq_true, ite_false]
  rw [target_eq (value x.toBits) k q j hk]
  exact ArmSpecial.negative_within _ _ q j _ hsf hwf hsv (by omega) (by omega) hW hWe hρl hρu

#print axioms inverse_bounds
#print axioms target_eq
#print axioms rho_bounds
#print axioms ordinary_within
#print axioms exp_neg_small
#print axioms top_bound
#print axioms positive_within
#print axioms negative_within

end Verified.Examples.Exp10Paths
