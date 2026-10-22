import Library.Numerics.Float64.Pow.PowTheorem
import Library.Numerics.Float64.Pow.PowExpSign
import Library.Numerics.Float64.Exp.ExpNegativeFinal
import LeanExe.ProofKit.F64Packing

/-!
The sign of a zero result of `Pow.pow`.  `PowTheorem.pow_within` bounds the results within one
step of `x ^ y`, and `WithinSteps` places both zeros at position 0, so it leaves the sign of a zero
result open.  A zero result within one step of a nonnegative real `E` needs `E · 2 ^ 1074 ≤ 3/2`
(`zero_tiny`), and for `Pow.powExp` that puts its argument below `-512`, where only the underflow
product and the negative branch of `powSpecialCase` remain.  Without the sign bias the underflow
product is `+0` and the negative branch keeps the sign of its positive scale
(`powExp_zero_sign`); with the bias the scale is negated, and so is the result
(`powExp_bias_zero_sign`).
-/

namespace Library.Numerics.Float64.Pow.PowZeroSign
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Exp.ExpSpecialNegative PowExpPaths

set_option exponentiation.threshold 4096

/-! ### Zeros near a nonnegative real -/

/-- A zero word within one step of a nonnegative real `y`: `y` is at most `3/2` units of
`2 ^ -1074`. -/
theorem zero_tiny (y : ℝ) (w : UInt64) (hy : 0 ≤ y) (hw : F64SignedRounding.WithinSteps 1 y w)
    (hz : w.toNat % 2 ^ 63 = 0) : y * 2 ^ 1074 ≤ 3 / 2 := by
  obtain ⟨-, hd⟩ := hw
  rw [PowNegate.position_zero w hz] at hd
  have hRef : F64SignedRounding.roundNearestEven y = F64PositiveRounding.roundNearestEven y := by
    unfold F64SignedRounding.roundNearestEven
    exact ite_eq_left hy
  rw [hRef] at hd
  set R := F64PositiveRounding.roundNearestEven y with hR
  have hspec := F64PositiveRounding.roundNearestEven_spec y hy
  rw [← hR] at hspec
  by_contra hbig
  push Not at hbig
  have h2p : (0 : ℝ) < 2 ^ 1074 := by positivity
  rcases hspec.2 with ⟨-, hne⟩ | ⟨-, heq⟩
  · have hRlim := hne.1.1
    unfold F64NearestNonnegative.limit at hRlim
    rw [F64SignedRounding.position_of_lt R (by omega)] at hd
    have hR1 : R.toNat ≤ 1 := by
      have := abs_le.mp hd
      omega
    have hnear := hne.1.2 2 (by decide)
    have hv2 : value (2 : UInt64) = 2 / 2 ^ 1074 := by
      have h : Wasm.IEEE64.scaledValue (2 : UInt64) = 2 := by decide +kernel
      rw [value, h]
      norm_num
    have hvR : value R = 0 ∨ value R = 1 / 2 ^ 1074 := by
      rcases (show R.toNat = 0 ∨ R.toNat = 1 by omega) with h | h
      · left
        rw [show R = 0 from UInt64.toNat_inj.mp (by rw [h]; rfl), F64Magnitude.value_zero]
      · right
        have h1 : Wasm.IEEE64.scaledValue (1 : UInt64) = 1 := by decide +kernel
        rw [show R = 1 from UInt64.toNat_inj.mp (by rw [h]; rfl), value, h1]
        norm_num
    rw [hv2] at hnear
    have hy' : 3 / 2 / 2 ^ 1074 < y := by
      rw [div_lt_iff₀ h2p]
      linarith
    have hu : (0 : ℝ) < 1 / 2 ^ 1074 := by positivity
    rcases hvR with h | h <;> rw [h] at hnear
    · rcases le_or_gt (2 / 2 ^ 1074) y with h2 | h2
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hnear
        linarith
      · rw [abs_of_nonpos (by linarith), abs_of_pos (by linarith)] at hnear
        linarith
    · rcases le_or_gt (2 / 2 ^ 1074) y with h2 | h2
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hnear
        linarith
      · rw [abs_of_nonpos (by linarith), abs_of_pos (by linarith)] at hnear
        linarith
  · rw [heq, F64SignedRounding.position_of_lt _ (by decide)] at hd
    have := abs_le.mp hd
    simp only [F64PositiveRounding.positiveInfinity, UInt64.reduceToNat] at this
    omega

/-- `exp L` exceeds `3/2` units of `2 ^ -1074` from `L > -700` on. -/
theorem exp_large (L : ℝ) (hL : -700 < L) : 3 / 2 < Real.exp L * 2 ^ 1074 := by
  have h2 : Real.exp (1074 * Real.log 2) = 2 ^ 1074 := by
    rw [show (1074 : ℝ) = ((1074 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
  have hl := Library.Numerics.Float64.Exp.ExpReductionBounds.log_two_coarse_bounds.1
  rw [← h2, ← Real.exp_add]
  have h1 : (1 : ℝ) ≤ L + 1074 * Real.log 2 := by linarith
  have he := Real.exp_le_exp.mpr h1
  have hone := Real.add_one_le_exp (1 : ℝ)
  linarith

/-! ### Products -/

theorem signMask_sign (b : Bool) : Wasm.IEEE64.sign (Wasm.IEEE64.signMask b) = b := by
  cases b <;> decide

/-- A finite product of finite words has the sign of the exact product. -/
theorem mul_sign (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hf : Finite (Wasm.IEEE64.mul a b)) :
    Wasm.IEEE64.sign (Wasm.IEEE64.mul a b) = (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
  have hcases : Wasm.IEEE64.mul a b =
      Wasm.IEEE64.signMask (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) ∨
      ∃ m, Wasm.IEEE64.mul a b =
        Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) m := by
    simp only [Wasm.IEEE64.mul, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
      ite_false]
    split
    · left; rfl
    · unfold Wasm.IEEE64.roundDyadicMagnitude
      split
      · left; rfl
      · right; exact ⟨_, rfl⟩
  rcases hcases with h | ⟨m, h⟩
  · rw [h, signMask_sign]
  · rw [h] at hf ⊢
    exact (F64Packing.pack_finite_spec _ m hf).2

theorem zero_finite (w : UInt64) (hz : w.toNat % 2 ^ 63 = 0) : Finite w := by
  have hT := w.toNat_lt
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent
  simp only [bne_iff_ne, ne_eq]
  simp only [Nat.reducePow] at hz hT ⊢
  omega

theorem scale_down_finite : Finite (0x0010000000000000 : UInt64) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem scale_down_sign : Wasm.IEEE64.sign (0x0010000000000000 : UInt64) = false := by decide

/-! ### The exponential without the bias -/

/-- The argument of a zero result: `x ≤ -512`, so its exponent field is at least 1032, and `x`
is negative. -/
theorem zero_argument (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits)
    (htail : |value xtail.toBits| ≤ 17 / 2 ^ 28 * |value x.toBits|)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ |L| / 2 ^ 65)
    (hz : (Pow.powExp Exp.expTable x xtail 0).toBits.toNat % 2 ^ 63 = 0) :
    value x.toBits ≤ -512 ∧ 1032 ≤ Wasm.IEEE64.exponent x.toBits := by
  have hw := PowExpTheorem.powExp_within x xtail L hxf htf htail hL
  have ht := zero_tiny _ _ (Real.exp_pos L).le hw hz
  have hL700 : L ≤ -700 := by
    by_contra h
    push Not at h
    linarith [exp_large L h]
  set X := value x.toBits
  set T := value xtail.toBits
  have hLa : |L| = -L := abs_of_neg (by linarith)
  rw [hLa] at hL
  have h1 := (abs_le.mp hL).2
  have hX : X ≤ -512 := by
    rcases le_or_gt 0 X with h | h
    · rw [abs_of_nonneg h] at htail
      have := (abs_le.mp htail).1
      nlinarith
    · rw [abs_of_neg h] at htail
      have := (abs_le.mp htail).1
      nlinarith
  refine ⟨hX, ?_⟩
  by_contra he
  push Not at he
  have hm := F64Magnitude.magnitude_lt x.toBits 1032 9 (by norm_num) (by norm_num) he
  rw [abs_lt] at hm
  norm_num at hm
  linarith [hm.1]

/-- **A zero result of `powExp` without the bias is `+0`.** -/
theorem powExp_zero_sign (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits)
    (htail : |value xtail.toBits| ≤ 17 / 2 ^ 28 * |value x.toBits|)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ |L| / 2 ^ 65)
    (hz : (Pow.powExp Exp.expTable x xtail 0).toBits.toNat % 2 ^ 63 = 0) :
    Wasm.IEEE64.sign (Pow.powExp Exp.expTable x xtail 0).toBits = false := by
  obtain ⟨hX, he⟩ := zero_argument x xtail L hxf htf htail hL hz
  have hf : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hzf := zero_finite _ hz
  rcases (show Wasm.IEEE64.exponent x.toBits = 1032 ∨ 1033 ≤ Wasm.IEEE64.exponent x.toBits by
    omega) with he | he
  · -- the special path, `-1024 < x ≤ -512`, with a negative `k`
    have hhi := F64Magnitude.magnitude_lt x.toBits 1033 10 (by norm_num) (by norm_num) (by omega)
    norm_num at hhi
    have hT13 : |value xtail.toBits| ≤ 1 / 2 ^ 13 := by
      calc
        _ ≤ 17 / 2 ^ 28 * |value x.toBits| := htail
        _ ≤ 17 / 2 ^ 28 * 1024 := by gcongr
        _ ≤ 1 / 2 ^ 13 := by norm_num
    rw [PowExpBranches.special_selected _ x xtail he] at hz hzf ⊢
    obtain ⟨k, q, j, hk, hki, hj, hkn, hid, htmf, htmb⟩ :=
      PowExpFar.far_state x xtail hxf htf hhi.le hT13
    have hkneg : k < 0 := by
      by_contra hk0
      push Not at hk0
      have hl0 : 0 < Real.log 2 := by linarith [Library.Numerics.Float64.Exp.ExpReductionBounds.log_two_coarse_bounds.1]
      have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
      have := mul_nonneg hkR (div_pos hl0 (by norm_num : (0 : ℝ) < 128)).le
      have := (abs_le.mp hid).1
      linarith
    have hguard := Library.Numerics.Float64.Exp.ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
    rw [ite_eq_left hkneg] at hguard
    have hg : ¬ (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits &&& 0x80000000 == 0) = true := by
      rw [hguard]
      decide
    have hqb := Library.Numerics.Float64.Exp.ExpFarRange.quotient_bounds_far k q j hk hkn
    have hq : q ≤ -23 := PowExpSign.quotient_le _ k q j hk hid (by linarith)
    obtain ⟨hsf, hsv, hslo, hshi⟩ :=
      Library.Numerics.Float64.Exp.ExpSpecialScale.negative_scale_value _ k q j hki hk hj (by omega) hq
    obtain ⟨hpf, hPm, hyf, hyl, -⟩ := PowExpFar.far_sum _ _ hsf htmf hslo hshi htmb
    set s := Library.Numerics.Float64.Exp.ExpSpecialScale.negativeScale (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits) with hsdef
    set p := Wasm.IEEE64.mul s (PowExpCore.tmpFloat x xtail).toBits
    have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
    have hypos : 0 < value (Wasm.IEEE64.add s p) := by linarith
    rw [PowExpCore.core_eq] at hz hzf ⊢
    simp only [ite_true] at hz hzf ⊢
    rw [PowExpSpecial.scale_word, Library.Numerics.Float64.Exp.ExpCoreBounds.floatShifted_bits] at hz hzf ⊢
    have hsd : Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits) +
        ((1022 : UInt64) <<< (52 : UInt64)) = s := rfl
    have hnb := negative_bits (PowExpCore.tmpFloat x xtail)
      (Library.Numerics.Float64.Exp.ExpScaleBits.scaleBits (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits))
      (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits) hg (by rw [hsd]; exact hsf)
      (by rw [hsd]; exact sign_of_pos _ hS) (by rw [hsd]; exact hyf) (by rw [hsd]; exact hypos)
    rw [hsd] at hnb
    rw [hnb] at hzf ⊢
    rw [lt_one_iff _ hyf] at hzf ⊢
    by_cases hy1 : value (Wasm.IEEE64.add s p) < 1
    · rw [decide_eq_true hy1, ite_eq_left rfl] at hzf ⊢
      have hS2 : value s ≤ (2 : ℝ) ^ 1000 := hshi
      obtain ⟨hcf, ⟨R, hR, hRl, hRu⟩, -⟩ := comp_sum_bounds s p hsf hpf hS hS2 hPm hy1
      exact (Library.Numerics.Float64.Exp.ExpSpecialNegative.comp_final _ hcf R hR hRl hRu).2.1
    · rw [decide_eq_false hy1, ite_eq_right Bool.false_ne_true] at hzf ⊢
      rw [mul_sign _ _ scale_down_finite hyf hzf, scale_down_sign, sign_of_pos _ hypos]
      rfl
  · -- the underflow product
    rw [PowExpSign.big_sel _ _ _ _ he]
    have hs : (x.toBits >>> 63 == 1) = true := by
      rw [PowExpTheorem.sign_shift_one]
      have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
        simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq,
          show Wasm.IEEE64.exponent x.toBits ≠ 0 by omega, ite_false]
        positivity
      exact (F64Magnitude.sign_value _ hmag).mpr (by linarith)
    rw [ite_eq_left hs, ite_eq_right PowExpSign.zero_bias, PowExpBranches.underflow_bits]
    decide

/-! ### The exponential with the bias -/

/-- The compensated value of the negative branch as a word: `z - 1` for the sum `z` of
`Library.Numerics.Float64.Exp.ExpSpecialNegative.compSum`. -/
theorem comp_value_bits (s : UInt64) (tmp : Float) (hsf : Finite s) (one' : Float)
    (hone : one'.toBits = one) :
    (one' + (Float.ofBits s + Float.ofBits s * tmp) +
        (one' - (one' + (Float.ofBits s + Float.ofBits s * tmp)) +
          (Float.ofBits s + Float.ofBits s * tmp) +
          (Float.ofBits s - (Float.ofBits s + Float.ofBits s * tmp) + Float.ofBits s * tmp)) -
        one').toBits =
      Wasm.IEEE64.sub (compSum s (Wasm.IEEE64.mul s tmp.toBits)) one := by
  simp only [F64Bits.toBits_sub, F64Bits.toBits_add, F64Bits.toBits_mul, ofBits_finite s hsf, hone]
  rfl

/-- The sign of `negBranch` with the bias: with a positive scale whose sum with its product is
positive and finite, a zero result of the biased branch is `-0`. -/
theorem negBranch_bias_sign (tmp : Float) (s : UInt64) (hsf : Finite s) (hS : 0 < value s)
    (hS2 : value s ≤ (2 : ℝ) ^ 1000)
    (hpf : Finite (Wasm.IEEE64.mul s tmp.toBits))
    (hP : |value (Wasm.IEEE64.mul s tmp.toBits)| ≤ value s / 32)
    (hyf : Finite (Wasm.IEEE64.add s (Wasm.IEEE64.mul s tmp.toBits)))
    (hypos : 0 < value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s tmp.toBits)))
    (hz : (PowExpSign.negBranch tmp (Wasm.IEEE64.negate s)).toBits.toNat % 2 ^ 63 = 0) :
    Wasm.IEEE64.sign (PowExpSign.negBranch tmp (Wasm.IEEE64.negate s)).toBits = true := by
  have hss : Wasm.IEEE64.sign s = false := sign_of_pos _ hS
  have hSb : (Float.ofBits s).toBits = s := ofBits_finite s hsf
  have hYu : (Float.ofBits s + Float.ofBits s * tmp).toBits =
      Wasm.IEEE64.add s (Wasm.IEEE64.mul s tmp.toBits) := by
    rw [F64Bits.toBits_add, F64Bits.toBits_mul, hSb]
  have hS' := PowSignRel.fofBits s
  have hY := PowSignRel.fadd hS' (PowSignRel.fmul_left tmp hS')
  have hYn : Wasm.IEEE64.isNaN (Float.ofBits s + Float.ofBits s * tmp).toBits = false := by
    rw [hYu]
    exact not_nan_of_finite hyf
  have hYm : Wasm.IEEE64.scaledMagnitude (Float.ofBits s + Float.ofBits s * tmp).toBits ≠ 0 := by
    rw [hYu]
    intro h0
    have := PowExpSign.value_mag_zero _ h0
    linarith
  have hYb := PowSignRel.eq_negate _ _ hY hYn hYm
  have hdf : Finite (0x0010000000000000 : UInt64) := scale_down_finite
  unfold PowExpSign.negBranch at hz ⊢
  dsimp only at hz ⊢
  rw [PowSignRel.fabs hY] at hz ⊢
  rw [F64Bits.toBits_mul, ofBits_finite _ hdf] at hz ⊢
  have hzf := zero_finite _ hz
  by_cases h1 : (Float.ofBits s + Float.ofBits s * tmp).abs < 1.0
  · rw [ite_eq_left h1] at hz hzf ⊢
    have hY1 : value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s tmp.toBits)) < 1 := by
      have := (F64Bits.lt_iff _ _).mp h1
      rw [F64Bits.toBits_abs, hYu, abs_of_sign _ (sign_of_pos _ hypos),
        show (1.0 : Float).toBits = one from rfl, lt_one_iff _ hyf] at this
      simpa using this
    obtain ⟨hcf, ⟨R, hR, hRl, hRu⟩, -⟩ := comp_sum_bounds s _ hsf hpf hS hS2 hP hY1
    obtain ⟨hdf', hds0⟩ := F64GridExact.sub_grid_exact _ one hcf one_finite
      ((R : Int) - 2 ^ 52) 1022 (by rw [hR, one_scaled]; ring) (by omega) (by norm_num)
    have hds : Wasm.IEEE64.scaledValue
        (Wasm.IEEE64.sub (compSum s (Wasm.IEEE64.mul s tmp.toBits)) one) =
        ((R : Int) - 2 ^ 52) * 2 ^ 1022 := by
      rw [hds0, hR, one_scaled]
      ring
    have hone_u : (if Float.ofBits s + Float.ofBits s * tmp < 0.0 then -1.0 else 1.0 :
        Float).toBits = one := by
      rw [ite_eq_right]
      · rfl
      · rw [F64Bits.lt_iff, PowSignRel.zero_word, hYu, lt_zero_false _ hyf hypos]
        simp
    have h1rel := PowSignRel.one_rel hY hYn hYm
    have hlo := PowSignRel.fadd (PowSignRel.fsub hS' hY) (PowSignRel.fmul_left tmp hS')
    have hhi := PowSignRel.fadd h1rel hY
    have hlo2 := PowSignRel.fadd (PowSignRel.fadd (PowSignRel.fsub h1rel hhi) hY) hlo
    have hy := PowSignRel.fsub (PowSignRel.fadd hhi hlo2) h1rel
    unfold PowExpSign.compTail at hz hzf ⊢
    dsimp only at hz hzf ⊢
    rw [PowSignRel.fbeq_zero hy] at hz hzf ⊢
    have hyu := comp_value_bits s tmp hsf _ hone_u
    rw [F64Bits.beq_eq, PowSignRel.zero_word, hyu] at hz hzf ⊢
    have hsv0 : Wasm.IEEE64.scaledValue (0 : UInt64) = 0 := by decide +kernel
    have heq : Wasm.IEEE64.eq (Wasm.IEEE64.sub (compSum s (Wasm.IEEE64.mul s tmp.toBits)) one) 0 =
        decide ((R : Int) - 2 ^ 52 = 0) := by
      unfold Wasm.IEEE64.eq
      rw [not_nan_of_finite hdf', show Wasm.IEEE64.isNaN 0 = false by decide +kernel, hds, hsv0]
      simp only [Bool.or_false, Bool.false_eq_true, ite_false]
      by_cases h0 : (R : Int) - 2 ^ 52 = 0
      · rw [h0, zero_mul]
        exact (decide_eq_true rfl).symm
      · have hne : (((R : Int) - 2 ^ 52) * 2 ^ 1022 == 0) = false := by
          rw [beq_eq_false_iff_ne]
          exact mul_ne_zero h0 (pow_ne_zero _ (by norm_num))
        rw [hne]
        exact (decide_eq_false h0).symm
    rw [heq] at hz hzf ⊢
    by_cases h0 : (R : Int) - 2 ^ 52 = 0
    · rw [decide_eq_true h0, ite_eq_left rfl] at hzf ⊢
      have hw : Wasm.IEEE64.negate s &&& 0x8000000000000000 = 0x8000000000000000 := by
        apply UInt64.toNat_inj.mp
        have hsT : s.toNat < 2 ^ 63 := by
          simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hss
        rw [UInt64.toNat_and, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl,
          PowCheckint.and_pow, F64SignedRounding.negate_toNat, hss]
        simp only [Bool.false_eq_true, ite_false]
        omega
      rw [hw, F64Bits.toBits_ofBits] at hzf ⊢
      simp only [show Wasm.IEEE64.isNaN 0x8000000000000000 = false by decide, Bool.false_eq_true,
        ite_false] at hzf ⊢
      rw [mul_sign _ _ hdf (by unfold CodeLib.IEEE64.Finite; decide) hzf, scale_down_sign]
      decide
    · rw [decide_eq_false h0, ite_eq_right Bool.false_ne_true] at hzf ⊢
      have hyn : Wasm.IEEE64.isNaN
          (Wasm.IEEE64.sub (compSum s (Wasm.IEEE64.mul s tmp.toBits)) one) = false :=
        not_nan_of_finite hdf'
      have hym : Wasm.IEEE64.scaledMagnitude
          (Wasm.IEEE64.sub (compSum s (Wasm.IEEE64.mul s tmp.toBits)) one) ≠ 0 := by
        intro hm
        have := natAbs_scaledValue (Wasm.IEEE64.sub (compSum s (Wasm.IEEE64.mul s tmp.toBits)) one)
        rw [hm, hds] at this
        exact h0 (by
          have h' := Int.natAbs_eq_zero.mp this
          rcases mul_eq_zero.mp h' with h | h
          · exact h
          · exact absurd h (pow_ne_zero _ (by norm_num)))
      rw [← hyu] at hyn hym
      have hyb := PowSignRel.eq_negate _ _ hy hyn hym
      rw [hyb, hyu] at hzf ⊢
      have hus : Wasm.IEEE64.sign
          (Wasm.IEEE64.sub (compSum s (Wasm.IEEE64.mul s tmp.toBits)) one) = false := by
        by_contra hs
        have hs' : Wasm.IEEE64.sign
            (Wasm.IEEE64.sub (compSum s (Wasm.IEEE64.mul s tmp.toBits)) one) = true := by
          simpa using hs
        have h := hds
        simp only [Wasm.IEEE64.scaledValue, hs', ite_true] at h
        have hR0 : (0 : Int) < ((R : Int) - 2 ^ 52) * 2 ^ 1022 :=
          mul_pos (by omega) (pow_pos (by norm_num) _)
        have hnn : (0 : Int) ≤ (Wasm.IEEE64.scaledMagnitude
            (Wasm.IEEE64.sub (compSum s (Wasm.IEEE64.mul s tmp.toBits)) one) : Int) :=
          Int.natCast_nonneg _
        linarith
      have hnf := PowNegate.negrel_finite _ _ (Or.inl rfl) hdf'
      rw [mul_sign _ _ hdf hnf hzf, scale_down_sign, (F64Sign.fields_negate _).2.2, hus]
      rfl
  · rw [ite_eq_right h1] at hz hzf ⊢
    rw [hYb, hYu] at hzf ⊢
    have hnf := PowNegate.negrel_finite _ _ (Or.inl rfl) hyf
    rw [mul_sign _ _ hdf hnf hzf, scale_down_sign, (F64Sign.fields_negate _).2.2,
      sign_of_pos _ hypos]
    rfl

/-- **A zero result of `powExp` with the bias is `-0`.** -/
theorem powExp_bias_zero_sign (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits)
    (htail : |value xtail.toBits| ≤ 17 / 2 ^ 28 * |value x.toBits|)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ |L| / 2 ^ 65)
    (hz : (Pow.powExp Exp.expTable x xtail PowExpSign.bias).toBits.toNat % 2 ^ 63 = 0) :
    Wasm.IEEE64.sign (Pow.powExp Exp.expTable x xtail PowExpSign.bias).toBits = true := by
  have hrel := PowExpSign.powExp_rel x xtail hxf htf htail
  have hzu : (Pow.powExp Exp.expTable x xtail 0).toBits.toNat % 2 ^ 63 = 0 := by
    rcases hrel with (h | ⟨-, h⟩) | ⟨hn, -⟩
    · rw [h] at hz
      rwa [← PowSignRel.mag_zero, PowSignRel.mag_negate, PowSignRel.mag_zero] at hz
    · exact h
    · rw [(PowSignRel.zero_not_nan _ hz).1] at hn
      exact absurd hn (by decide)
  obtain ⟨hX, he⟩ := zero_argument x xtail L hxf htf htail hL hzu
  have hf : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  rcases (show Wasm.IEEE64.exponent x.toBits = 1032 ∨ 1033 ≤ Wasm.IEEE64.exponent x.toBits by
    omega) with he | he
  · have hhi := F64Magnitude.magnitude_lt x.toBits 1033 10 (by norm_num) (by norm_num) (by omega)
    norm_num at hhi
    have hT13 : |value xtail.toBits| ≤ 1 / 2 ^ 13 := by
      calc
        _ ≤ 17 / 2 ^ 28 * |value x.toBits| := htail
        _ ≤ 17 / 2 ^ 28 * 1024 := by gcongr
        _ ≤ 1 / 2 ^ 13 := by norm_num
    obtain ⟨k, q, j, hk, hki, hj, hkn, hid, htmf, htmb⟩ :=
      PowExpFar.far_state x xtail hxf htf hhi.le hT13
    have hkneg : k < 0 := by
      by_contra hk0
      push Not at hk0
      have hl0 : 0 < Real.log 2 := by linarith [Library.Numerics.Float64.Exp.ExpReductionBounds.log_two_coarse_bounds.1]
      have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
      have := mul_nonneg hkR (div_pos hl0 (by norm_num : (0 : ℝ) < 128)).le
      have := (abs_le.mp hid).1
      linarith
    have hguard := Library.Numerics.Float64.Exp.ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
    rw [ite_eq_left hkneg] at hguard
    have hg : ¬ (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits &&& 0x80000000 == 0) = true := by
      rw [hguard]
      decide
    have hqb := Library.Numerics.Float64.Exp.ExpFarRange.quotient_bounds_far k q j hk hkn
    have hq : q ≤ -23 := PowExpSign.quotient_le _ k q j hk hid (by linarith)
    obtain ⟨hsf, hsv, hslo, hshi⟩ :=
      Library.Numerics.Float64.Exp.ExpSpecialScale.negative_scale_value _ k q j hki hk hj (by omega) hq
    obtain ⟨hpf, hPm, hyf, hyl, -⟩ := PowExpFar.far_sum _ _ hsf htmf hslo hshi htmb
    have hS : 0 < value (Library.Numerics.Float64.Exp.ExpSpecialScale.negativeScale (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits)) :=
      lt_of_lt_of_le (by positivity) hslo
    have hypos : 0 < value (Wasm.IEEE64.add
        (Library.Numerics.Float64.Exp.ExpSpecialScale.negativeScale (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits))
        (Wasm.IEEE64.mul (Library.Numerics.Float64.Exp.ExpSpecialScale.negativeScale (Library.Numerics.Float64.Exp.ExpCoreState.shiftedBits x.toBits))
          (PowExpCore.tmpFloat x xtail).toBits)) := by linarith
    rw [PowExpSign.special_sel _ _ _ _ he, PowExpSign.core_bias] at hz ⊢
    simp only [ite_true] at hz ⊢
    rw [Library.Numerics.Float64.Exp.ExpCoreBounds.floatShifted_bits, PowExpSign.special_neg _ _ _ hg, PowExpSign.negate_add,
      PowExpSpecial.scale_word] at hz ⊢
    exact negBranch_bias_sign _ _ hsf hS hshi hpf hPm hyf hypos hz
  · rw [PowExpSign.big_sel _ _ _ _ he]
    have hs : (x.toBits >>> 63 == 1) = true := by
      rw [PowExpTheorem.sign_shift_one]
      have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
        simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq,
          show Wasm.IEEE64.exponent x.toBits ≠ 0 by omega, ite_false]
        positivity
      exact (F64Magnitude.sign_value _ hmag).mpr (by linarith)
    rw [ite_eq_left hs, ite_eq_left PowExpSign.bias_ne, F64Bits.toBits_mul, F64Bits.toBits_ofBits,
      F64Bits.toBits_ofBits]
    decide +kernel

/-! ### The main path and `pow` -/

/-- `powMain` for `x ≠ 1`: a zero result has the sign of the bias. -/
theorem main_zero (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616)
    (hX1 : ¬ (E = 1023 ∧ f = 0)) (y : Float) (hyf : Finite y.toBits)
    (hy1 : 1 / 2 ^ 65 ≤ |value y.toBits|) (hy2 : |value y.toBits| < 2 ^ 63) (sb : UInt64)
    (hsb : sb = 0 ∨ sb = PowExpSign.bias)
    (hz : (Pow.powMain Pow.powLogTable Exp.expTable ix y y.toBits sb).toBits.toNat % 2 ^ 63 = 0) :
    Wasm.IEEE64.sign (Pow.powMain Pow.powLogTable Exp.expTable ix y y.toBits sb).toBits =
      (sb != 0) := by
  set X := ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075)
  obtain ⟨h1f, h2f, hlog, htail⟩ := PowLogFinal.log_within ix E f hE1 hE2 hf hix hX1
  obtain ⟨hL1, hL2⟩ := PowMainPath.log_bounds E f hE1 hE2 (by simpa using hf) hX1
  simp only [Pow.powMain] at hz ⊢
  generalize hP : Pow.powLog Pow.powLogTable ix = P at h1f h2f hlog htail hz ⊢
  obtain ⟨hiF, loF⟩ := P
  simp only at h1f h2f hlog htail hz ⊢
  set Y := value hiF.toBits
  set T := value loF.toBits
  set lX := Real.log X
  have hY1 : 1 / 2 ^ 54 ≤ |Y| := by
    have h1 := abs_sub_abs_le_abs_sub lX (Y + T)
    rw [abs_sub_comm] at h1
    have h2 := abs_add_le Y T
    have h3 : 7 / 8 / 2 ^ 65 * |lX| ≤ |lX| / 4 := by linarith [abs_nonneg lX]
    linarith [abs_nonneg Y]
  have hY2 : |Y| ≤ 800 := by
    have h1 := abs_sub_abs_le_abs_sub (Y + T) lX
    have h2 := abs_sub_abs_le_abs_sub Y (-T)
    rw [sub_neg_eq_add, abs_neg] at h2
    have h3 : 7 / 8 / 2 ^ 65 * |lX| ≤ 745 := by linarith [abs_nonneg lX]
    linarith [abs_nonneg Y]
  obtain ⟨hef, helf, hprod, helo⟩ := PowProduct.product_error y hiF loF hyf h1f h2f hy1 hy2
    hY1 hY2 htail
  set ehi := Float.ofBits (y.toBits &&& 0xFFFFFFFFF8000000) *
    Float.ofBits (hiF.toBits &&& 0xFFFFFFFFF8000000)
  set elo := (y - Float.ofBits (y.toBits &&& 0xFFFFFFFFF8000000)) *
      Float.ofBits (hiF.toBits &&& 0xFFFFFFFFF8000000) +
    y * (hiF - Float.ofBits (hiF.toBits &&& 0xFFFFFFFFF8000000) + loF)
  set yv := value y.toBits
  have hL : |value ehi.toBits + value elo.toBits - yv * lX| ≤ |yv * lX| / 2 ^ 65 := by
    have h1 : |yv * (Y + T) - yv * lX| ≤ |yv| * (7 / 8 / 2 ^ 65 * |lX|) := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    have h2 : |yv * (Y + T)| ≤ |yv| * (|lX| * (1 + 1 / 2 ^ 65)) := by
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := abs_sub_abs_le_abs_sub (Y + T) lX
      linarith [abs_nonneg lX]
    have h3 := abs_sub_le (value ehi.toBits + value elo.toBits) (yv * (Y + T)) (yv * lX)
    have hprod' : |value ehi.toBits + value elo.toBits - yv * (Y + T)| ≤
        |yv * (Y + T)| / 2 ^ 74 := hprod
    rw [abs_mul yv lX]
    have h4 := mul_nonneg (abs_nonneg yv) (abs_nonneg lX)
    linarith
  rcases hsb with rfl | rfl
  · rw [powExp_zero_sign ehi elo (yv * lX) hef helf helo hL hz]
    rfl
  · rw [powExp_bias_zero_sign ehi elo (yv * lX) hef helf helo hL hz]
    exact PowExpSign.bias_ne.symm

/-- `powMain` for `x = 1` gives no zero. -/
theorem main_one_ne (y : Float) (hyf : Wasm.IEEE64.exponent y.toBits < 2047)
    (hey : 1 ≤ Wasm.IEEE64.exponent y.toBits) (sb : UInt64)
    (hsb : sb = 0 ∨ sb = PowExpSign.bias) :
    ¬ (Pow.powMain Pow.powLogTable Exp.expTable 0x3FF0000000000000 y y.toBits sb).toBits.toNat %
      2 ^ 63 = 0 := by
  rcases hsb with rfl | rfl
  · rw [PowPositive.main_one y hyf hey]
    decide
  · intro hz
    have hr := PowMainSign.main_rel_one y hyf hey
    rw [PowPositive.main_one y hyf hey] at hr
    rcases hr with (h | ⟨-, h⟩) | ⟨-, h⟩
    · rw [h] at hz
      exact absurd hz (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)

/-- `powMain` on the normalized word of a positive finite `x`: a zero result has the sign of the
bias. -/
theorem main_zero_any (x y : Float) (hxf : Finite x.toBits) (hx : 0 < value x.toBits)
    (hyf : Finite y.toBits) (hy1 : 1 / 2 ^ 65 ≤ |value y.toBits|)
    (hy2 : |value y.toBits| < 2 ^ 63) (sb : UInt64) (hsb : sb = 0 ∨ sb = PowExpSign.bias)
    (hz : (Pow.powMain Pow.powLogTable Exp.expTable (PowMainSign.normWord x) y y.toBits
      sb).toBits.toNat % 2 ^ 63 = 0) :
    Wasm.IEEE64.sign (Pow.powMain Pow.powLogTable Exp.expTable (PowMainSign.normWord x) y
      y.toBits sb).toBits = (sb != 0) := by
  have hs := PowExpPaths.sign_of_pos _ hx
  have hT : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hxexp : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hx0 : x.toBits ≠ 0 := by
    intro h
    rw [h, F64Magnitude.value_zero] at hx
    exact lt_irrefl _ hx
  have hyexp : Wasm.IEEE64.exponent y.toBits < 2047 := by
    have h := hyf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent y.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hey1 : 958 ≤ Wasm.IEEE64.exponent y.toBits := PowProduct.exponent_of_abs _ 958
    (by norm_num) (by norm_num at hy1 ⊢; exact hy1)
  have ht := PowBranches.top_word x.toBits hT
  by_cases hxe : 1 ≤ Wasm.IEEE64.exponent x.toBits
  · have htop : (x.toBits >>> 52 == 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro h
      rw [h] at ht
      change 0 = _ at ht
      omega
    simp only [PowMainSign.normWord, htop, Bool.false_eq_true, ite_false] at hz ⊢
    by_cases hx1 : x.toBits = 0x3FF0000000000000
    · rw [hx1] at hz
      exact absurd hz (main_one_ne y hyexp (by omega) sb hsb)
    · have hix : (x.toBits.toNat : Int) =
          ((Wasm.IEEE64.exponent x.toBits : Int) * 4503599627370496 +
            Wasm.IEEE64.fraction x.toBits) % 18446744073709551616 := by
        simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
        simp only [Nat.reducePow] at hT ⊢
        omega
      have hne : ¬ ((Wasm.IEEE64.exponent x.toBits : Int) = 1023 ∧
          Wasm.IEEE64.fraction x.toBits = 0) := by
        rintro ⟨h1, h2⟩
        apply hx1
        apply UInt64.toNat_inj.mp
        have h1' : Wasm.IEEE64.exponent x.toBits = 1023 := by exact_mod_cast h1
        simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at h1' h2
        simp only [Nat.reducePow] at hT h1' h2 ⊢
        change _ = 4607182418800017408
        omega
      exact main_zero x.toBits _ _ (by omega) (by omega) (Nat.mod_lt _ (by norm_num)) hix hne y
        hyf hy1 hy2 sb hsb hz
  · have he0 : Wasm.IEEE64.exponent x.toBits = 0 := by omega
    have hs52 : x.toBits.toNat < 2 ^ 52 := by
      have : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 = 0 := he0
      simp only [Nat.reducePow] at hT this ⊢
      omega
    have h0 : 0 < x.toBits.toNat := by
      by_contra hn
      exact hx0 (UInt64.toNat_inj.mp (by simp; omega))
    have htop0 : (x.toBits >>> 52 == 0) = true := by
      rw [he0] at ht
      simp only [beq_iff_eq]
      exact UInt64.toNat_inj.mp (by rw [ht]; rfl)
    simp only [PowMainSign.normWord, htop0, ite_true] at hz ⊢
    obtain ⟨E', f', hE1', hE2', hf', hix', -⟩ := PowSubnormal.subnormal_word x hs52 h0
    exact main_zero _ E' f' hE1' (by omega) (by simpa using hf') (by simpa using hix')
      (by omega) y hyf hy1 hy2 sb hsb hz

/-- A zero result of `pow` for a positive `x` is `+0`. -/
theorem pos_zero_sign (x y : Float) (hxf : Finite x.toBits) (hx : 0 < value x.toBits)
    (hyf : Finite y.toBits) (hy0 : 2 * y.toBits ≠ 0)
    (hz : (Pow.pow x y).toBits.toNat % 2 ^ 63 = 0) :
    Wasm.IEEE64.sign (Pow.pow x y).toBits = false := by
  have hW := PowTheoremPos.pow_pos_within x y hxf hx hyf
  have hTiny := zero_tiny _ _ (Real.rpow_nonneg hx.le _) hW hz
  obtain ⟨E, f, hE1, hE2, hf, hXv, hone⟩ := PowTheoremPos.positive_rep x hxf hx
  have hs := PowExpPaths.sign_of_pos _ hx
  have hT : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hxexp : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hyexp : Wasm.IEEE64.exponent y.toBits < 2047 := by
    have h := hyf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent y.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hx0 : x.toBits ≠ 0 := by
    intro h
    rw [h, F64Magnitude.value_zero] at hx
    exact lt_irrefl _ hx
  rcases (show Wasm.IEEE64.exponent y.toBits < 958 ∨ 1086 ≤ Wasm.IEEE64.exponent y.toBits ∨
      (958 ≤ Wasm.IEEE64.exponent y.toBits ∧ Wasm.IEEE64.exponent y.toBits < 1086) by omega)
    with hey | hey | ⟨hey1, hey2⟩
  · -- `|y| < 2 ^ -65`: `x ^ y` is near 1
    exfalso
    have hYb : |value y.toBits| ≤ 1 / 2 ^ 65 := by
      have := F64Magnitude.magnitude_lt y.toBits 958 (-65) (by norm_num) (by norm_num) hey
      have h65 : (2 : ℝ) ^ (-65 : Int) = 1 / 2 ^ 65 := by norm_num
      rw [h65] at this
      exact this.le
    have hlog : |Real.log (value x.toBits)| ≤ 745 := by
      by_cases hx1 : x.toBits = 0x3FF0000000000000
      · rw [hx1, PowPositive.one_word_value, Real.log_one, abs_zero]
        norm_num
      · rw [hXv]
        exact (PowMainPath.log_bounds E f hE1 hE2 hf (fun h' => hx1 (hone.mpr h'))).2
    have ht : |Real.log (value x.toBits) * value y.toBits| ≤ 745 / 2 ^ 65 := by
      rw [abs_mul]
      calc
        _ ≤ 745 * (1 / 2 ^ 65) := mul_le_mul hlog hYb (abs_nonneg _) (by norm_num)
        _ = 745 / 2 ^ 65 := by ring
    rw [Real.rpow_def_of_pos hx] at hTiny
    have he := Real.add_one_le_exp (Real.log (value x.toBits) * value y.toBits)
    have := (abs_le.mp ht).1
    have h2 : (1 / 2 : ℝ) * 2 ^ 1074 ≤ Real.exp (Real.log (value x.toBits) * value y.toBits) *
        2 ^ 1074 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (745 : ℝ) / 2 ^ 65 ≤ 1 / 2 := by norm_num
      linarith
    have h3 : (3 / 2 : ℝ) < 1 / 2 * 2 ^ 1074 := by norm_num
    linarith
  · -- `|y| ≥ 2 ^ 63`: the overflow and underflow products
    have hw := Library.Numerics.Float64.Exp.ExpBranches.exponent_word_spec y.toBits
    simp only [Library.Numerics.Float64.Exp.ExpBranches.exponentWord] at hw
    have hc : ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [UInt64.toNat_sub_of_le ((y.toBits >>> 52) &&& 0x7ff) 0x3be
        (UInt64.le_iff_toNat_le.mpr (by rw [hw]; change 958 ≤ _; omega)), hw]
      simp only [UInt64.reduceSub, UInt64.reduceToNat]
      omega
    have hnlt : ¬ ((y.toBits >>> 52) &&& 0x7ff) < 0x3be := by
      intro h
      have := UInt64.lt_iff_toNat_lt.mp h
      rw [hw] at this
      change _ < 958 at this
      omega
    rw [Pow.pow, PowBranches.positive_special _ _ x y hT hx0 hxexp hyexp hy0 (Or.inr hc),
      ite_eq_left hc] at hz ⊢
    by_cases hx1 : x.toBits = 0x3FF0000000000000
    · rw [ite_eq_left (by simp [hx1])] at hz
      exact absurd hz (by decide)
    rw [ite_eq_right (by simp [hx1]), ite_eq_right (by simpa using hnlt)]
    split_ifs
    · rw [PowExpBranches.overflow_bits]; decide
    · rw [PowExpBranches.underflow_bits]; decide
    · rw [PowExpBranches.underflow_bits]; decide
    · rw [PowExpBranches.overflow_bits]; decide
  · -- the main path
    have hY1 : 1 / 2 ^ 65 ≤ |value y.toBits| := by
      have := F64Magnitude.magnitude_ge y.toBits 958 (-65) (by norm_num) (by norm_num)
        (by norm_num) hey1
      have h65 : (2 : ℝ) ^ (-65 : Int) = 1 / 2 ^ 65 := by norm_num
      rwa [h65] at this
    have hY2 : |value y.toBits| < 2 ^ 63 := by
      have := F64Magnitude.magnitude_lt y.toBits 1086 63 (by norm_num) (by norm_num) hey2
      simpa using this
    rw [PowNegBase.pos_path x y hT hx0 hxexp hyexp hy0,
      PowNegBase.tail_main _ _ _ _ _ _ _ (PowBranches.y_guard y.toBits hey1 hey2)] at hz ⊢
    exact main_zero_any x y hxf hx hyf hY1 hY2 0 (Or.inl rfl) hz

/-- **The sign of a zero result of `pow`**: for finite `x` and `y` with a real `x ^ y`, a zero
result is `-0` exactly when `x` has its sign bit set and `y` is an odd integer, as C99's Annex F
prescribes. -/
theorem pow_zero_sign (x y : Float) (hxf : Finite x.toBits) (hyf : Finite y.toBits)
    (hreal : 0 < value x.toBits ∨ (value x.toBits < 0 ∧ ∃ n : Int, value y.toBits = n) ∨
      (value x.toBits = 0 ∧ 0 ≤ value y.toBits))
    (hz : (Pow.pow x y).toBits.toNat % 2 ^ 63 = 0) :
    (Wasm.IEEE64.sign (Pow.pow x y).toBits = true ↔
      Wasm.IEEE64.sign x.toBits = true ∧ ∃ n : Int, value y.toBits = n ∧ n % 2 = 1) := by
  have hxexp : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hyexp : Wasm.IEEE64.exponent y.toBits < 2047 := by
    have h := hyf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent y.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  by_cases hy0 : 2 * y.toBits = 0
  · rw [PowPositive.y_zero x y hxexp hy0] at hz
    exact absurd hz (by decide)
  have hymag : 0 < Wasm.IEEE64.scaledMagnitude y.toBits :=
    Nat.pos_of_ne_zero (fun h => hy0 (PowTheorem.two_mul_of_low _ ((PowSignRel.mag_zero _).mp h)))
  obtain ⟨-, hc1, hc2⟩ := PowCheckint.checkint_spec y.toBits hyexp hymag
  rcases hreal with hx | ⟨hx, n, hn⟩ | ⟨hx, hy⟩
  · rw [pos_zero_sign x y hxf hx hyf hy0 hz, PowExpPaths.sign_of_pos _ hx]
    simp
  · have hxmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [PowExpSign.value_mag_zero _ h0] at hx
      exact lt_irrefl _ hx
    have hs : Wasm.IEEE64.sign x.toBits = true := (F64Magnitude.sign_value _ hxmag).mpr hx
    have hx0 : 2 * x.toBits ≠ 0 :=
      PowNegBase.low_ne _ (fun h => absurd ((PowSignRel.mag_zero _).mpr h) hxmag.ne')
    obtain ⟨hnT, hn0, hne, hnf, hnv⟩ := PowNegBase.neg_facts x hxf hs hx0
    have hxpos : 0 < value (-x).toBits := by rw [hnv]; linarith
    rcases Int.emod_two_eq_zero_or_one n with he | ho
    · have hc : Pow.checkint y.toBits = 2 := hc2.mpr ⟨n, hn, he⟩
      rw [PowNegBase.even_eq x y hxf hs hx0 hyf hy0 hc] at hz ⊢
      rw [pos_zero_sign (-x) y hnf hxpos hyf hy0 hz]
      refine iff_of_false (by decide) ?_
      rintro ⟨-, m, hm, hm1⟩
      have h1 := hc1.mpr ⟨m, hm, hm1⟩
      rw [hc] at h1
      exact absurd h1 (by decide)
    · have hc : Pow.checkint y.toBits = 1 := hc1.mpr ⟨n, hn, ho⟩
      obtain ⟨hey1, hey2⟩ := PowNegBase.odd_exponent y.toBits hc
      have hY1 : 1 / 2 ^ 65 ≤ |value y.toBits| := by
        have := F64Magnitude.magnitude_ge y.toBits 958 (-65) (by norm_num) (by norm_num)
          (by norm_num) hey1
        have h65 : (2 : ℝ) ^ (-65 : Int) = 1 / 2 ^ 65 := by norm_num
        rwa [h65] at this
      have hY2 : |value y.toBits| < 2 ^ 63 := by
        have := F64Magnitude.magnitude_lt y.toBits 1086 63 (by norm_num) (by norm_num) hey2
        simpa using this
      rw [PowNegBase.pow_neg_word x y hxf hs hx0 hyf hy0 (by rw [hc]; decide), hc,
        ite_eq_left (by decide : ((1 : UInt64) == 1) = true),
        PowNegBase.tail_main _ _ _ _ _ _ _ (PowBranches.y_guard y.toBits hey1 hey2)] at hz ⊢
      have h := main_zero_any (-x) y hnf hxpos hyf hY1 hY2 PowExpSign.bias (Or.inr rfl) hz
      rw [PowExpSign.bias_ne] at h
      exact iff_of_true h ⟨hs, n, hn, ho⟩
  · have hx0 : x.toBits = 0 ∨ x.toBits = 0x8000000000000000 :=
      PowSpecial.two_mul_zero _ (PowTheorem.two_mul_of_low _
        ((PowSignRel.mag_zero _).mp (PowTheorem.mag_of_value_zero _ hx)))
    have hy' : 0 < value y.toBits := by
      rcases hy.lt_or_eq with h | h
      · exact h
      · exact absurd (PowTheorem.mag_of_value_zero _ h.symm) hymag.ne'
    have hsy := PowExpPaths.sign_of_pos _ hy'
    rw [PowSpecial.zero_base x y hx0 hyf hy0, hsy, ite_eq_right Bool.false_ne_true]
    by_cases hcase : Wasm.IEEE64.sign x.toBits = true ∧ Pow.checkint y.toBits = 1
    · rw [ite_eq_left hcase]
      exact iff_of_true (by decide) ⟨hcase.1, hc1.mp hcase.2⟩
    · rw [ite_eq_right hcase]
      exact iff_of_false (by decide) (fun h => hcase ⟨h.1, hc1.mpr h.2⟩)

#print axioms zero_tiny
#print axioms exp_large
#print axioms mul_sign
#print axioms zero_argument
#print axioms powExp_zero_sign
#print axioms comp_value_bits
#print axioms negBranch_bias_sign
#print axioms powExp_bias_zero_sign
#print axioms main_zero
#print axioms main_one_ne
#print axioms main_zero_any
#print axioms pos_zero_sign
#print axioms pow_zero_sign

end Library.Numerics.Float64.Pow.PowZeroSign
