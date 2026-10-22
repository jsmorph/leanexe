import Library.Numerics.Float64.Exp2.Exp2Core

/-!
The three paths of `Exp2.exp2Core` on `Exp.expTable`, each within one step of the reference of
`2 ^ x`: the ordinary reconstruction for `|x| ≤ 928`, the doubled reconstruction for
`928 < x ≤ 1024 - 2 ^ -43`, and the scaled-down reconstruction for `-1075 < x < -928`.
-/

namespace Library.Numerics.Float64.Exp2.Exp2Paths
open CodeLib.IEEE64
open LeanExe.ProofKit Exp2Core

set_option exponentiation.threshold 4096

theorem two_bits : (2.0 : Float).toBits = 0x4000000000000000 := rfl

theorem special_positive_eq (tmp : Float) (sbits ki : UInt64)
    (h : (ki &&& 0x80000000 == 0) = true) :
    Exp2.exp2SpecialCase tmp sbits ki =
      2.0 * (Float.ofBits (sbits - ((1 : UInt64) <<< (52 : UInt64))) +
        Float.ofBits (sbits - ((1 : UInt64) <<< (52 : UInt64))) * tmp) := by
  simp only [Exp2.exp2SpecialCase, h, ite_true]

theorem special_negative_eq (tmp : Float) (sbits ki : UInt64)
    (h : ¬ (ki &&& 0x80000000 == 0) = true) :
    Exp2.exp2SpecialCase tmp sbits ki =
      Library.Numerics.Float64.Exp.ExpSpecialNegative.negativeResult
        (Float.ofBits (sbits + ((1022 : UInt64) <<< (52 : UInt64)))) tmp := by
  simp only [Exp2.exp2SpecialCase, h, Bool.false_eq_true, ite_false]
  rfl

/-- The reconstruction on words, for a finite scale. -/
theorem sum_bits (s : UInt64) (t : Float) (hs : Finite s) :
    (Float.ofBits s + Float.ofBits s * t).toBits =
      Wasm.IEEE64.add s (Wasm.IEEE64.mul s t.toBits) := by
  simp only [F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_ofBits, not_nan_of_finite hs,
    Bool.false_eq_true, ite_false]

/-- The integer `k` is bounded by `128 |x| + 1/2`. -/
theorem k_bounds (a : ℝ) (k : Int) (hk : |(k : ℝ) - 128 * a| ≤ 1 / 2) (lo hi : Int)
    (hlo : (lo : ℝ) - 1 / 2 < 128 * a) (hhi : 128 * a < (hi : ℝ) + 1 / 2) :
    lo ≤ k ∧ k ≤ hi := by
  have h := abs_le.mp hk
  have h1 : (lo : ℝ) - 1 < k := by linarith
  have h2 : (k : ℝ) < hi + 1 := by linarith
  have h1' : lo - 1 < k := by exact_mod_cast h1
  have h2' : k < hi + 1 := by exact_mod_cast h2
  omega

theorem ordinary_within (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| ≤ 928) :
    F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ value x.toBits)
      (Exp2.exp2Core Exp.expTable x false).toBits := by
  obtain ⟨k, q, j, hk, hke, hkn, hkey, hj, -, hwf, hW, hWe, hr⟩ :=
    core_state x hxf (hx.trans (by norm_num))
  have hxb := abs_le.mp hx
  obtain ⟨hklo, hkhi⟩ := k_bounds _ k hke (-118784) 118784 (by push_cast; linarith)
    (by push_cast; linarith)
  have hj' := j.isLt
  have hqlo : -928 ≤ q := by omega
  have hqhi : q ≤ 928 := by omega
  obtain ⟨hsf, hsv⟩ := Library.Numerics.Float64.Exp.ArmScale.ordinary_scale _ k q j hkey hk hj (by omega) (by omega)
  rw [key_scale] at hsf hsv
  obtain ⟨hρl, hρu⟩ := rho_bounds _ hr
  rw [core_eq, ite_eq_right (by decide), sum_bits _ _ hsf, target_eq (value x.toBits) k q j hk]
  exact Library.Numerics.Float64.Exp.ArmReconstruction.ordinary_within _ _ q j _ hsf hwf hsv (by omega) (by omega) hW hWe
    hρl hρu

/-- `2 ^ (-2 ^ -43) ≤ 1 - 2 ^ -44`, as an exponential. -/
theorem exp_top : Real.exp (-(Real.log 2 / 2 ^ 43)) ≤ 1 - 1 / 2 ^ 44 := by
  have hL := Library.Numerics.Float64.Exp.ExpReductionBounds.log_two_coarse_bounds
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = -(Real.log 2 / 2 ^ 43) := ⟨_, rfl⟩
  rw [← hydef]
  have hL0 : 0 ≤ Real.log 2 / 2 ^ 43 := div_nonneg (by linarith [hL.1]) (by positivity)
  have hy : |y| ≤ 1 / 2 ^ 43 := by
    rw [hydef, abs_neg, abs_of_nonneg hL0]
    exact div_le_div_of_nonneg_right (by linarith [hL.2]) (by positivity)
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
  have hyv : y ≤ -((2 / 3) / 2 ^ 43) := by
    rw [hydef, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right hL.1 (by positivity)
  have hnum : (1 : ℝ) + -((2 / 3) / 2 ^ 43) + (1 / 2 ^ 43) ^ 2 * 1 ≤ 1 - 1 / 2 ^ 44 := by
    norm_num
  linarith

/-- `2 ^ a` for `a` at most the double below 1024. -/
theorem top_bound (a : ℝ) (ha : a ≤ 1024 - 1 / 2 ^ 43) : (2 : ℝ) ^ a ≤ 2 ^ 1024 - 2 ^ 980 := by
  have hm : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ ((1024 : ℝ) - 1 / 2 ^ 43) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
  have h1024 : (2 : ℝ) ^ (1024 : ℝ) = 2 ^ 1024 := by exact_mod_cast Real.rpow_natCast 2 1024
  have hsplit : (2 : ℝ) ^ ((1024 : ℝ) - 1 / 2 ^ 43) =
      2 ^ 1024 * Real.exp (-(Real.log 2 / 2 ^ 43)) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), h1024,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  calc
    _ ≤ _ := hm
    _ = _ := hsplit
    _ ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 44) := mul_le_mul_of_nonneg_left exp_top (by positivity)
    _ = 2 ^ 1024 - 2 ^ 980 := by norm_num

theorem positive_within (x : Float) (hxf : Finite x.toBits) (hxlo : 928 < value x.toBits)
    (hxhi : value x.toBits ≤ 1024 - 1 / 2 ^ 43) :
    F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ value x.toBits)
      (Exp2.exp2Core Exp.expTable x true).toBits := by
  have hx : |value x.toBits| ≤ 1100 := by
    rw [abs_le]
    constructor <;> linarith [show (0 : ℝ) < 1 / 2 ^ 43 by positivity]
  obtain ⟨k, q, j, hk, hke, hkn, hkey, hj, hguard, hwf, hW, hWe, hr⟩ := core_state x hxf hx
  obtain ⟨hklo, hkhi⟩ := k_bounds _ k hke 118784 131072 (by push_cast; linarith)
    (by push_cast; linarith [show (0 : ℝ) < 1 / 2 ^ 43 by positivity])
  have hj' := j.isLt
  have hqlo : 928 ≤ q := by omega
  have hqhi : q ≤ 1024 := by omega
  have hk0 : ¬ k < 0 := by omega
  rw [ite_eq_right hk0] at hguard
  obtain ⟨hsf, hsv⟩ := Library.Numerics.Float64.Exp.ArmScale.half_scale _ k q j hkey hk hj (by omega) hqhi
  have hhalf : Library.Numerics.Float64.Exp.ArmScale.halfScale (key (floatShifted x).toBits) =
      Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (floatShifted x).toBits - ((1 : UInt64) <<< (52 : UInt64)) := by
    rw [Library.Numerics.Float64.Exp.ArmScale.halfScale, key_scale]
  rw [hhalf] at hsf hsv
  obtain ⟨hρl, hρu⟩ := rho_bounds _ hr
  have hE := top_bound _ hxhi
  rw [target_eq (value x.toBits) k q j hk] at hE ⊢
  rw [core_eq, ite_eq_left rfl, special_positive_eq _ _ _ (by rw [hguard]; rfl),
    F64Bits.toBits_mul, two_bits, sum_bits _ _ hsf]
  exact Library.Numerics.Float64.Exp.ArmSpecial.positive_within _ _ q j _ hsf hwf hsv (by omega) hqhi hW hWe hρl hρu hE

theorem negative_within (x : Float) (hxf : Finite x.toBits) (hxlo : -1075 < value x.toBits)
    (hxhi : value x.toBits < -928) :
    F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ value x.toBits)
      (Exp2.exp2Core Exp.expTable x true).toBits := by
  have hx : |value x.toBits| ≤ 1100 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨k, q, j, hk, hke, hkn, hkey, hj, hguard, hwf, hW, hWe, hr⟩ := core_state x hxf hx
  obtain ⟨hklo, hkhi⟩ := k_bounds _ k hke (-137600) (-118784) (by push_cast; linarith)
    (by push_cast; linarith)
  have hj' := j.isLt
  have hqlo : -1075 ≤ q := by omega
  have hqhi : q ≤ -928 := by omega
  have hk0 : k < 0 := by omega
  rw [ite_eq_left hk0] at hguard
  obtain ⟨hsf, hsv, -, -⟩ :=
    Library.Numerics.Float64.Exp.ExpSpecialScale.negative_scale_value _ k q j hkey hk hj (by omega) (by omega)
  have hneg : Library.Numerics.Float64.Exp.ExpSpecialScale.negativeScale (key (floatShifted x).toBits) =
      Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (floatShifted x).toBits + ((1022 : UInt64) <<< (52 : UInt64)) := by
    rw [Library.Numerics.Float64.Exp.ExpSpecialScale.negativeScale, key_scale]
  rw [hneg] at hsf hsv
  obtain ⟨hρl, hρu⟩ := rho_bounds _ hr
  rw [core_eq, ite_eq_left rfl, special_negative_eq _ _ _ (by rw [hguard]; decide),
    Library.Numerics.Float64.Exp.ExpSpecialNegative.negativeResult_bits, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, not_nan_of_finite hsf]
  simp only [Bool.false_eq_true, ite_false]
  rw [target_eq (value x.toBits) k q j hk]
  exact Library.Numerics.Float64.Exp.ArmSpecial.negative_within _ _ q j _ hsf hwf hsv (by omega) (by omega) hW hWe hρl hρu

#print axioms two_bits
#print axioms special_positive_eq
#print axioms special_negative_eq
#print axioms ordinary_within
#print axioms exp_top
#print axioms top_bound
#print axioms positive_within
#print axioms negative_within

end Library.Numerics.Float64.Exp2.Exp2Paths
