import Verified.Examples.PowSignRel
import Verified.Examples.PowExpTheorem
import Verified.Examples.PowCheckint

/-!
`Pow.powExp` with `signBias = 0x800 << 7` against `signBias = 0`.  The bias adds `2 ^ 63` to the
scale bits, which negates the scale, and the branches below `2 ^ -54` and from 1024 on negate
their results.  Every operation after the scale keeps `PowSignRel.Rel`, except the sign test of
the compensated sum of `powSpecialCase`, which needs the scaled result `S + S tmp` to be neither a
zero nor a NaN.  For a negative `k` that result is positive and finite, so the biased result is
related to the unbiased one, and it lies within one step of `-exp L` when the unbiased one lies
within one step of `exp L`.
-/

namespace Verified.Examples.PowExpSign
open CodeLib.IEEE64 LeanExe.ProofKit ExpBranches PowSignRel

set_option exponentiation.threshold 4096

/-- The bias of `pow` for a negative base and an odd exponent. -/
def bias : UInt64 := (0x800 : UInt64) <<< 7

theorem bias_eq : bias = 0x40000 := by decide

theorem bias_ne : (bias != 0) = true := by decide

theorem zero_bias : ¬ ((0 : UInt64) != 0) = true := by decide

theorem shift_bias (k : UInt64) : (k + bias) <<< (45 : UInt64) =
    (k <<< (45 : UInt64)) + 0x8000000000000000 := by
  have hk := k.toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [bias_eq, UInt64.toNat_shiftLeft, UInt64.toNat_add, UInt64.reduceToNat,
    Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow] at hk ⊢
  omega

theorem add_sign (w : UInt64) : w + 0x8000000000000000 = Wasm.IEEE64.negate w := by
  apply UInt64.toNat_inj.mp
  have hT := w.toNat_lt
  rw [UInt64.toNat_add, F64SignedRounding.negate_toNat]
  cases hs : Wasm.IEEE64.sign w
  · have h : w.toNat < 2 ^ 63 := by simpa [Wasm.IEEE64.sign] using hs
    simp only [Bool.false_eq_true, ite_false, UInt64.reduceToNat]
    simp only [Nat.reducePow] at hT h ⊢
    omega
  · have h : 2 ^ 63 ≤ w.toNat := by simpa [Wasm.IEEE64.sign] using hs
    simp only [ite_true, UInt64.reduceToNat]
    simp only [Nat.reducePow] at hT h ⊢
    omega

theorem negate_add (w c : UInt64) : Wasm.IEEE64.negate w + c = Wasm.IEEE64.negate (w + c) := by
  rw [← add_sign, ← add_sign]
  have hw := w.toNat_lt
  have hc := c.toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow] at hw hc ⊢
  omega

theorem negate_sub (w c : UInt64) : Wasm.IEEE64.negate w - c = Wasm.IEEE64.negate (w - c) := by
  rw [← add_sign, ← add_sign]
  have hw := w.toNat_lt
  have hc := c.toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.reduceToNat, Nat.reducePow] at hw hc ⊢
  omega

private theorem sub_guard (a : UInt64) (hlo : 969 ≤ a.toNat) :
    (a - 969).toNat = a.toNat - 969 :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)

theorem tiny_sel (tab : Array UInt64) (x xtail : Float) (sb : UInt64)
    (hx : Wasm.IEEE64.exponent x.toBits < 969) :
    Pow.powExp tab x xtail sb = if sb != 0 then -(1.0 + x) else 1.0 + x := by
  have hs : (exponentWord x.toBits - 969).toNat =
      2 ^ 64 - 969 + Wasm.IEEE64.exponent x.toBits := by
    rw [UInt64.toNat_sub, exponent_word_spec]
    change (2 ^ 64 - 969 + Wasm.IEEE64.exponent x.toBits) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hg1 : exponentWord x.toBits - 969 ≥ (63 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hs]
    change 63 ≤ _
    omega
  have hg2 : exponentWord x.toBits - 969 ≥ (0x80000000 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hs]
    change 0x80000000 ≤ _
    omega
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Pow.powExp, exponentWord, hc] at hg1 hg2 ⊢
  rw [ite_eq_left hg1, ite_eq_left hg2]

theorem ordinary_sel (tab : Array UInt64) (x xtail : Float) (sb : UInt64)
    (hlo : 969 ≤ Wasm.IEEE64.exponent x.toBits) (hhi : Wasm.IEEE64.exponent x.toBits < 1032) :
    Pow.powExp tab x xtail sb = Pow.powExpCore tab x xtail sb false := by
  have hw := exponent_word_spec x.toBits
  have hg : ¬ exponentWord x.toBits - 969 ≥ (63 : UInt64) := by
    intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [sub_guard _ (by omega)] at hn
    change 63 ≤ _ at hn
    omega
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Pow.powExp, exponentWord, hc] at hg ⊢
  rw [ite_eq_right hg]

theorem special_sel (tab : Array UInt64) (x xtail : Float) (sb : UInt64)
    (he : Wasm.IEEE64.exponent x.toBits = 1032) :
    Pow.powExp tab x xtail sb = Pow.powExpCore tab x xtail sb true := by
  have hw := exponent_word_spec x.toBits
  have hg1 : exponentWord x.toBits - 969 ≥ (63 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [sub_guard _ (by omega)]
    change 63 ≤ _
    omega
  have hg2 : ¬ exponentWord x.toBits - 969 ≥ (0x80000000 : UInt64) := by
    intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [sub_guard _ (by omega)] at hn
    change 0x80000000 ≤ _ at hn
    omega
  have hg3 : ¬ exponentWord x.toBits ≥ (0x409 : UInt64) := by
    intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    change 0x409 ≤ _ at hn
    omega
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Pow.powExp, exponentWord, hc] at hg1 hg2 hg3 ⊢
  rw [ite_eq_left hg1, ite_eq_right hg2, ite_eq_right hg3]

theorem big_sel (tab : Array UInt64) (x xtail : Float) (sb : UInt64)
    (he : 1033 ≤ Wasm.IEEE64.exponent x.toBits) :
    Pow.powExp tab x xtail sb =
      if x.toBits >>> 63 == 1 then
        (if sb != 0 then Float.ofBits 0x9000000000000000 else Float.ofBits 0x1000000000000000) *
          Float.ofBits 0x1000000000000000
      else (if sb != 0 then Float.ofBits 0xF000000000000000 else Float.ofBits 0x7000000000000000) *
          Float.ofBits 0x7000000000000000 := by
  have hw := exponent_word_spec x.toBits
  have hlt : Wasm.IEEE64.exponent x.toBits < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have hg1 : exponentWord x.toBits - 969 ≥ (63 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [sub_guard _ (by omega)]
    change 63 ≤ _
    omega
  have hg2 : ¬ exponentWord x.toBits - 969 ≥ (0x80000000 : UInt64) := by
    intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [sub_guard _ (by omega)] at hn
    change 0x80000000 ≤ _ at hn
    omega
  have hg3 : exponentWord x.toBits ≥ (0x409 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    change 0x409 ≤ _
    omega
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Pow.powExp, exponentWord, hc] at hg1 hg2 hg3 ⊢
  rw [ite_eq_left hg1, ite_eq_right hg2, ite_eq_left hg3]

/-- The core with the bias: the scale bits negated. -/
theorem core_bias (x xtail : Float) (special : Bool) :
    Pow.powExpCore Exp.expTable x xtail bias special =
      if special then
        Pow.powSpecialCase (PowExpCore.tmpFloat x xtail)
          (Wasm.IEEE64.negate (PowExpCore.scaleWord x)) (ExpCoreBounds.floatShifted x).toBits
      else Float.ofBits (Wasm.IEEE64.negate (PowExpCore.scaleWord x)) +
        Float.ofBits (Wasm.IEEE64.negate (PowExpCore.scaleWord x)) *
          PowExpCore.tmpFloat x xtail := by
  have h : ∀ (a k : UInt64), a + (k + bias) <<< (45 : UInt64) =
      Wasm.IEEE64.negate (a + k <<< (45 : UInt64)) := by
    intro a k
    rw [shift_bias, ← add_sign]
    apply UInt64.toNat_inj.mp
    have ha := a.toNat_lt
    have hk := (k <<< (45 : UInt64)).toNat_lt
    simp only [UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow] at ha hk ⊢
    omega
  cases special <;> simp only [Pow.powExpCore, h, Bool.false_eq_true, ite_false, ite_true] <;> rfl

/-- The compensated sum of `Pow.powSpecialCase` for a scaled result `Y` below 1 in magnitude. -/
def compTail (S Y one tmp : Float) (sb : UInt64) : Float :=
  let lo := S - Y + S * tmp
  let hi := one + Y
  let lo := one - hi + Y + lo
  let y := hi + lo - one
  if y == 0.0 then Float.ofBits (sb &&& 0x8000000000000000) else y

/-- The branch of `Pow.powSpecialCase` for a negative `k`, on the corrected scale bits `sb`. -/
def negBranch (tmp : Float) (sb : UInt64) : Float :=
  let S := Float.ofBits sb
  let Y := S + S * tmp
  Float.ofBits 0x0010000000000000 *
    (if Y.abs < 1.0 then compTail S Y (if Y < 0.0 then -1.0 else 1.0) tmp sb else Y)

theorem special_neg (tmp : Float) (sbits ki : UInt64)
    (hg : ¬ (ki &&& 0x80000000 == 0) = true) :
    Pow.powSpecialCase tmp sbits ki =
      negBranch tmp (sbits + ((1022 : UInt64) <<< (52 : UInt64))) := by
  unfold Pow.powSpecialCase
  rw [ite_eq_right hg]
  rfl

theorem special_pos (tmp : Float) (sbits ki : UInt64) (hg : (ki &&& 0x80000000 == 0) = true) :
    Pow.powSpecialCase tmp sbits ki =
      (Float.ofBits (sbits - ((1009 : UInt64) <<< (52 : UInt64))) +
        Float.ofBits (sbits - ((1009 : UInt64) <<< (52 : UInt64))) * tmp) *
          Float.ofBits 0x7F00000000000000 := by
  unfold Pow.powSpecialCase
  rw [ite_eq_left hg]
  simp only [PowExpPaths.upward_test, Bool.and_false, Bool.false_eq_true, ite_false]

theorem sign_word (sb : UInt64) :
    (Float.ofBits (sb &&& 0x8000000000000000)).toBits.toNat % 2 ^ 63 = 0 := by
  have hz : (sb &&& 0x8000000000000000).toNat % 2 ^ 63 = 0 := by
    rw [UInt64.toNat_and, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 by rfl,
      PowCheckint.and_pow]
    simp
  rw [F64Bits.toBits_ofBits, (zero_not_nan _ hz).1]
  exact hz

theorem comp_rel {S S' Y Y' one one' : Float} (tmp : Float) (sb : UInt64)
    (hS : Rel S'.toBits S.toBits) (hY : Rel Y'.toBits Y.toBits)
    (h1 : Rel one'.toBits one.toBits) :
    Rel (compTail S' Y' one' tmp (Wasm.IEEE64.negate sb)).toBits
      (compTail S Y one tmp sb).toBits := by
  have hlo := fadd (fsub hS hY) (fmul_left tmp hS)
  have hhi := fadd h1 hY
  have hlo2 := fadd (fadd (fsub h1 hhi) hY) hlo
  have hy := fsub (fadd hhi hlo2) h1
  simp only [compTail]
  rw [fbeq_zero hy]
  split_ifs
  · exact zero_rel _ _ (sign_word _) (sign_word _)
  · exact hy

theorem neg_rel (tmp : Float) (sb : UInt64)
    (hn : Wasm.IEEE64.isNaN (Float.ofBits sb + Float.ofBits sb * tmp).toBits = false)
    (hz : Wasm.IEEE64.scaledMagnitude (Float.ofBits sb + Float.ofBits sb * tmp).toBits ≠ 0) :
    Rel (negBranch tmp (Wasm.IEEE64.negate sb)).toBits (negBranch tmp sb).toBits := by
  have hS := fofBits sb
  have hY := fadd hS (fmul_left tmp hS)
  simp only [negBranch]
  apply fmul_right
  rw [fabs hY]
  by_cases h1 : (Float.ofBits sb + Float.ofBits sb * tmp).abs < 1.0
  · rw [ite_eq_left h1, ite_eq_left h1]
    exact comp_rel tmp sb hS hY (one_rel hY hn hz)
  · rw [ite_eq_right h1, ite_eq_right h1]
    exact hY

theorem core_ordinary (x xtail : Float) :
    Rel (Pow.powExpCore Exp.expTable x xtail bias false).toBits
      (Pow.powExpCore Exp.expTable x xtail 0 false).toBits := by
  rw [core_bias, PowExpCore.core_eq]
  simp only [Bool.false_eq_true, ite_false]
  exact fadd (fofBits _) (fmul_left _ (fofBits _))

theorem core_special (x xtail : Float)
    (hy : ¬ ((ExpCoreBounds.floatShifted x).toBits &&& 0x80000000 == 0) = true →
      Wasm.IEEE64.isNaN
          (Float.ofBits (PowExpCore.scaleWord x + ((1022 : UInt64) <<< (52 : UInt64))) +
            Float.ofBits (PowExpCore.scaleWord x + ((1022 : UInt64) <<< (52 : UInt64))) *
              PowExpCore.tmpFloat x xtail).toBits = false ∧
        Wasm.IEEE64.scaledMagnitude
          (Float.ofBits (PowExpCore.scaleWord x + ((1022 : UInt64) <<< (52 : UInt64))) +
            Float.ofBits (PowExpCore.scaleWord x + ((1022 : UInt64) <<< (52 : UInt64))) *
              PowExpCore.tmpFloat x xtail).toBits ≠ 0) :
    Rel (Pow.powExpCore Exp.expTable x xtail bias true).toBits
      (Pow.powExpCore Exp.expTable x xtail 0 true).toBits := by
  rw [core_bias, PowExpCore.core_eq]
  simp only [ite_true]
  by_cases hg : ((ExpCoreBounds.floatShifted x).toBits &&& 0x80000000 == 0) = true
  · rw [special_pos _ _ _ hg, special_pos _ _ _ hg, negate_sub]
    exact fmul_left _ (fadd (fofBits _) (fmul_left _ (fofBits _)))
  · rw [special_neg _ _ _ hg, special_neg _ _ _ hg, negate_add]
    exact neg_rel _ _ (hy hg).1 (hy hg).2

/-- A negative `k` in the special range comes from `x ≤ -512`, with quotient `q ≤ -23`. -/
theorem quotient_le (xv : ℝ) (k q : Int) (j : Fin 128) (hk : k = 128 * q + j.val)
    (hid : |xv - k * (Real.log 2 / 128)| ≤ 1 / 320) (hxv : xv ≤ -512) : q ≤ -23 := by
  by_contra hn
  push Not at hn
  have hkI : -2816 ≤ k := by have := j.isLt; omega
  have hkR : (-2816 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkI
  have hl := ExpReductionBounds.log_two_coarse_bounds.2
  have hl0 : 0 < Real.log 2 := by linarith [ExpReductionBounds.log_two_coarse_bounds.1]
  have hm : (-2816 : ℝ) * (Real.log 2 / 128) ≤ k * (Real.log 2 / 128) :=
    mul_le_mul_of_nonneg_right hkR (div_pos hl0 (by norm_num)).le
  have h1 := (abs_le.mp hid).1
  linarith

theorem value_mag_zero (w : UInt64) (h : Wasm.IEEE64.scaledMagnitude w = 0) : value w = 0 := by
  have hs : Wasm.IEEE64.scaledValue w = 0 := by
    have := natAbs_scaledValue w
    rw [h] at this
    exact Int.natAbs_eq_zero.mp this
  rw [value, hs]
  simp

/-- In the special range, a negative `k` gives a positive finite scaled result `S + S tmp`. -/
theorem special_y (x xtail : Float) (hxf : Finite x.toBits) (htf : Finite xtail.toBits)
    (hlo : 512 ≤ |value x.toBits|) (hhi : |value x.toBits| < 1024)
    (ht : |value xtail.toBits| ≤ 1 / 2 ^ 13)
    (hg : ¬ ((ExpCoreBounds.floatShifted x).toBits &&& 0x80000000 == 0) = true) :
    Wasm.IEEE64.isNaN
        (Float.ofBits (PowExpCore.scaleWord x + ((1022 : UInt64) <<< (52 : UInt64))) +
          Float.ofBits (PowExpCore.scaleWord x + ((1022 : UInt64) <<< (52 : UInt64))) *
            PowExpCore.tmpFloat x xtail).toBits = false ∧
      Wasm.IEEE64.scaledMagnitude
        (Float.ofBits (PowExpCore.scaleWord x + ((1022 : UInt64) <<< (52 : UInt64))) +
          Float.ofBits (PowExpCore.scaleWord x + ((1022 : UInt64) <<< (52 : UInt64))) *
            PowExpCore.tmpFloat x xtail).toBits ≠ 0 := by
  obtain ⟨k, q, j, hk, hki, hj, hkn, hid, htmf, htmb⟩ :=
    PowExpFar.far_state x xtail hxf htf hhi.le ht
  have hguard := ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
  rw [ExpCoreBounds.floatShifted_bits] at hg
  have hkneg : k < 0 := by
    by_contra hk0
    rw [ite_eq_right hk0] at hguard
    rw [hguard] at hg
    exact hg (by decide)
  have hxneg : value x.toBits ≤ -512 := by
    have h1 := (abs_le.mp hid).2
    have hl0 : 0 < Real.log 2 := by linarith [ExpReductionBounds.log_two_coarse_bounds.1]
    have hkR : (k : ℝ) < 0 := by exact_mod_cast hkneg
    have hkl : (k : ℝ) * (Real.log 2 / 128) < 0 :=
      mul_neg_of_neg_of_pos hkR (div_pos hl0 (by norm_num))
    rcases le_or_gt 0 (value x.toBits) with h | h
    · rw [abs_of_nonneg h] at hlo
      linarith
    · rw [abs_of_neg h] at hlo
      linarith
  have hq := quotient_le _ k q j hk hid hxneg
  have hqb := ExpFarRange.quotient_bounds_far k q j hk hkn
  obtain ⟨hsf, -, hslo, hshi⟩ :=
    ExpSpecialScale.negative_scale_value _ k q j hki hk hj (by omega) hq
  obtain ⟨-, -, hyf, hyl, -⟩ := PowExpFar.far_sum _ _ hsf htmf hslo hshi htmb
  have hsd : PowExpCore.scaleWord x + ((1022 : UInt64) <<< (52 : UInt64)) =
      ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits) := by
    rw [PowExpSpecial.scale_word]
    rfl
  rw [hsd, F64Bits.toBits_add, F64Bits.toBits_mul, PowExpPaths.ofBits_finite _ hsf]
  refine ⟨not_nan_of_finite hyf, fun h0 => ?_⟩
  have hS : 0 < value (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits)) :=
    lt_of_lt_of_le (by positivity) hslo
  rw [value_mag_zero _ h0] at hyl
  linarith

/-- `powExp` with the bias against `powExp` without it, for the arguments that `pow` passes. -/
theorem powExp_rel (x xtail : Float) (hxf : Finite x.toBits) (htf : Finite xtail.toBits)
    (htail : |value xtail.toBits| ≤ 17 / 2 ^ 28 * |value x.toBits|) :
    Rel (Pow.powExp Exp.expTable x xtail bias).toBits
      (Pow.powExp Exp.expTable x xtail 0).toBits := by
  have hf : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  rcases (show Wasm.IEEE64.exponent x.toBits < 969 ∨
      (969 ≤ Wasm.IEEE64.exponent x.toBits ∧ Wasm.IEEE64.exponent x.toBits < 1032) ∨
      Wasm.IEEE64.exponent x.toBits = 1032 ∨ 1033 ≤ Wasm.IEEE64.exponent x.toBits by omega)
    with he | ⟨he1, he2⟩ | he | he
  · rw [tiny_sel _ _ _ _ he, tiny_sel _ _ _ _ he, ite_eq_left bias_ne, ite_eq_right zero_bias]
    exact fneg _
  · rw [ordinary_sel _ _ _ _ he1 he2, ordinary_sel _ _ _ _ he1 he2]
    exact core_ordinary x xtail
  · rw [special_sel _ _ _ _ he, special_sel _ _ _ _ he]
    have hlo := F64Magnitude.magnitude_ge x.toBits 1032 9 (by norm_num) (by norm_num)
      (by norm_num) he.ge
    have hhi := F64Magnitude.magnitude_lt x.toBits 1033 10 (by norm_num) (by norm_num) (by omega)
    norm_num at hlo hhi
    have hT13 : |value xtail.toBits| ≤ 1 / 2 ^ 13 := by
      calc
        _ ≤ 17 / 2 ^ 28 * |value x.toBits| := htail
        _ ≤ 17 / 2 ^ 28 * 1024 := by gcongr
        _ ≤ 1 / 2 ^ 13 := by norm_num
    exact core_special x xtail (special_y x xtail hxf htf hlo hhi hT13)
  · rw [big_sel _ _ _ _ he, big_sel _ _ _ _ he, ite_eq_left bias_ne, ite_eq_left bias_ne,
      ite_eq_right zero_bias, ite_eq_right zero_bias]
    split_ifs
    · rw [show (0x9000000000000000 : UInt64) = Wasm.IEEE64.negate 0x1000000000000000 by decide]
      exact fmul_left _ (fofBits _)
    · rw [show (0xF000000000000000 : UInt64) = Wasm.IEEE64.negate 0x7000000000000000 by decide]
      exact fmul_left _ (fofBits _)

/-- `powExp` with the bias lies within one step of `-exp L` under the conditions of
`PowExpTheorem.powExp_within`. -/
theorem powExp_neg_within (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits)
    (htail : |value xtail.toBits| ≤ 17 / 2 ^ 28 * |value x.toBits|)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ |L| / 2 ^ 65) :
    F64SignedRounding.WithinSteps 1 (-Real.exp L)
      (Pow.powExp Exp.expTable x xtail bias).toBits :=
  within_rel 1 _ _ _ (powExp_rel x xtail hxf htf htail)
    (PowExpTheorem.powExp_within x xtail L hxf htf htail hL)

#print axioms shift_bias
#print axioms add_sign
#print axioms negate_add
#print axioms negate_sub
#print axioms tiny_sel
#print axioms ordinary_sel
#print axioms special_sel
#print axioms big_sel
#print axioms core_bias
#print axioms special_neg
#print axioms special_pos
#print axioms comp_rel
#print axioms neg_rel
#print axioms core_special
#print axioms quotient_le
#print axioms special_y
#print axioms powExp_rel
#print axioms powExp_neg_within

end Verified.Examples.PowExpSign
