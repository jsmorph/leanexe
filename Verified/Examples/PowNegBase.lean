import Verified.Examples.PowMainSign
import Verified.Examples.PowCheckint

/-!
`Pow.pow` for a negative finite `x` and a finite nonzero `y`.  A `y` that is not an integer gives
the canonical NaN `(x - x) / (x - x)`.  For an integer `y`, `powWith` clears the sign bit of `x`
and continues as for `-x`, with the sign bias set for an odd `y`: an even `y` gives exactly
`pow (-x) y`, and an odd `y` gives a word related to `pow (-x) y` by `PowSignRel.Rel`.  With
`Real.rpow_intCast`, the result lies within one step of `x ^ y = (-1) ^ y |x| ^ y`.
-/

namespace Verified.Examples.PowNegBase
open CodeLib.IEEE64 LeanExe.ProofKit PowSignRel

set_option exponentiation.threshold 4096

/-- The end of `Pow.powWith` after its tests on zeros, infinities, NaNs, and negative bases, for
the bits `ix` of `|x|`, their top bits `topx`, and the sign bias `sb`. -/
def tailPath (logTab expTab : Array UInt64) (x y : Float) (ix topx sb : UInt64) : Float :=
  let iy := y.toBits
  let topy := iy >>> 52
  if (topy &&& 0x7ff) - 0x3be ≥ 0x43e - 0x3be then
    if ix == 0x3FF0000000000000 then 1.0
    else if (topy &&& 0x7ff) < 0x3be then
      if ix > 0x3FF0000000000000 then 1.0 + y else 1.0 - y
    else if ix > 0x3FF0000000000000 then
      if topy < 0x800 then Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000
      else Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
    else if topy < 0x800 then
      Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
    else Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000
  else
    let ix := if topx == 0 then
        ((x * Float.ofBits 0x4330000000000000).toBits &&& (0x7fffffffffffffff : UInt64)) -
          ((52 : UInt64) <<< 52)
      else ix
    Pow.powMain logTab expTab ix y iy sb

theorem top_neg (w : UInt64) (hs : Wasm.IEEE64.sign w = true) :
    (w >>> 52) - 1 ≥ (0x7ff : UInt64) - 1 := by
  have hT := w.toNat_lt
  have h2 : 2 ^ 63 ≤ w.toNat := by simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hs
  have h1 : (w >>> 52).toNat = w.toNat / 2 ^ 52 := by
    rw [UInt64.toNat_shiftRight]
    change w.toNat >>> 52 = _
    rw [Nat.shiftRight_eq_div_pow]
  apply UInt64.le_iff_toNat_le.mpr
  rw [UInt64.toNat_sub_of_le (w >>> 52) 1 (UInt64.le_iff_toNat_le.mpr (by
    rw [h1]
    change 1 ≤ _
    simp only [Nat.reducePow] at h2 hT ⊢
    omega)), h1]
  simp only [UInt64.reduceSub, UInt64.reduceToNat]
  simp only [Nat.reducePow] at h2 hT ⊢
  omega

/-- The path of `powWith` for a negative finite nonzero `x`, a finite nonzero `y`, and `checkint`
not 0. -/
theorem neg_path (x y : Float) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hxf : Wasm.IEEE64.exponent x.toBits < 2047) (hx0 : 2 * x.toBits ≠ 0)
    (hyf : Wasm.IEEE64.exponent y.toBits < 2047) (hy0 : 2 * y.toBits ≠ 0)
    (hc : Pow.checkint y.toBits ≠ 0) :
    Pow.pow x y = tailPath Pow.powLogTable Exp.expTable x y (x.toBits &&& 0x7fffffffffffffff)
      ((x.toBits >>> 52) &&& 0x7ff)
      (if Pow.checkint y.toBits == 1 then (0x800 : UInt64) <<< 7 else 0) := by
  have hzy := PowBranches.zeroinfnan_false y.toBits hyf hy0
  have hzx := PowBranches.zeroinfnan_false x.toBits hxf hx0
  have hs1 : (x.toBits >>> 63 == 1) = true := by
    rw [PowExpTheorem.sign_shift_one]
    exact hs
  have hc0 : (Pow.checkint y.toBits == 0) = false := beq_eq_false_iff_ne.mpr hc
  have hcond : (decide ((x.toBits >>> 52) - 1 ≥ (0x7ff : UInt64) - 1) ||
      decide (((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be)) = true := by
    simp only [top_neg x.toBits hs, decide_true, Bool.true_or]
  simp only [Pow.pow, Pow.powWith, tailPath, hcond, ite_true, hzy, hzx, hs1, hc0, Bool.true_and,
    Bool.false_eq_true, ite_false]

/-- The path of `powWith` for a positive finite nonzero `x` and a finite nonzero `y`. -/
theorem pos_path (x y : Float) (hx : x.toBits.toNat < 2 ^ 63) (hx0 : x.toBits ≠ 0)
    (hxf : Wasm.IEEE64.exponent x.toBits < 2047) (hyf : Wasm.IEEE64.exponent y.toBits < 2047)
    (hy0 : 2 * y.toBits ≠ 0) :
    Pow.pow x y = tailPath Pow.powLogTable Exp.expTable x y x.toBits (x.toBits >>> 52) 0 := by
  by_cases hcond : (x.toBits >>> 52) - 1 ≥ (0x7ff : UInt64) - 1 ∨
      ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be
  · rw [Pow.pow, PowBranches.positive_special _ _ x y hx hx0 hxf hyf hy0 hcond]
    rfl
  · obtain ⟨h1, h2⟩ := not_or.mp hcond
    have htop : (x.toBits >>> 52 == 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro h
      apply h1
      rw [h]
      decide
    simp only [Pow.pow, Pow.powWith, h1, h2, decide_false, Bool.or_false, Bool.false_eq_true,
      ite_false, tailPath, htop]

/-- `tailPath` below `2 ^ 63` and from `2 ^ -65` on in `|y|`. -/
theorem tail_main (logTab expTab : Array UInt64) (x y : Float) (ix topx sb : UInt64)
    (h : ¬ ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be) :
    tailPath logTab expTab x y ix topx sb =
      Pow.powMain logTab expTab
        (if topx == 0 then
          ((x * Float.ofBits 0x4330000000000000).toBits &&& (0x7fffffffffffffff : UInt64)) -
            ((52 : UInt64) <<< 52)
        else ix) y y.toBits sb := by
  simp only [tailPath, h, ite_false]

theorem neg_word (w : UInt64) (hs : Wasm.IEEE64.sign w = true) :
    w &&& 0x7fffffffffffffff = Wasm.IEEE64.negate w := by
  have hT := w.toNat_lt
  have hn := F64SignedRounding.negate_toNat w
  rw [hs, ite_eq_left rfl] at hn
  have h2 : 2 ^ 63 ≤ w.toNat := by simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hs
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod, hn]
  simp only [Nat.reducePow] at hT h2 ⊢
  omega

theorem negate_mask (w : UInt64) :
    Wasm.IEEE64.negate w &&& 0x7fffffffffffffff = w &&& 0x7fffffffffffffff := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_and,
    show (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    F64SignedRounding.negate_magnitude]

theorem mask_top (w : UInt64) : (w &&& 0x7fffffffffffffff) >>> 52 = (w >>> 52) &&& 0x7ff := by
  have hT := w.toNat_lt
  apply UInt64.toNat_inj.mp
  have h1 : (w &&& 0x7fffffffffffffff).toNat = w.toNat % 2 ^ 63 := by
    rw [UInt64.toNat_and, show (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have h2 : ((w >>> 52) &&& 0x7ff).toNat = (w >>> 52).toNat % 2 ^ 11 := by
    rw [UInt64.toNat_and, show (0x7ff : UInt64).toNat = 2 ^ 11 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have h3 : ∀ v : UInt64, (v >>> 52).toNat = v.toNat / 2 ^ 52 := by
    intro v
    rw [UInt64.toNat_shiftRight]
    change v.toNat >>> 52 = _
    rw [Nat.shiftRight_eq_div_pow]
  rw [h2, h3, h3, h1]
  simp only [Nat.reducePow] at hT ⊢
  omega

theorem neg_bits (x : Float) (hxf : Finite x.toBits) :
    (-x).toBits = Wasm.IEEE64.negate x.toBits := by
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, not_nan_of_finite hxf]
  rfl

theorem mul_negate (a c : UInt64) (ha : Finite a) (hc : Finite c) :
    Wasm.IEEE64.mul (Wasm.IEEE64.negate a) c = Wasm.IEEE64.negate (Wasm.IEEE64.mul a c) := by
  have ha' : Finite (Wasm.IEEE64.negate a) := PowNegate.negrel_finite _ _ (Or.inl rfl) ha
  rw [mul_finite_rounder _ _ ha' hc, mul_finite_rounder _ _ ha hc, mag_negate,
    (F64Sign.fields_negate a).2.2]
  have h : ((!Wasm.IEEE64.sign a) != Wasm.IEEE64.sign c) =
      !(Wasm.IEEE64.sign a != Wasm.IEEE64.sign c) := by
    cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign c <;> rfl
  rw [h, PowNegate.roundDyadic_not]

/-- The normalization of a subnormal `x` and of `-x` clear the same sign bit. -/
theorem norm_neg (x : Float) (hxf : Finite x.toBits) :
    ((-x) * Float.ofBits 0x4330000000000000).toBits &&& (0x7fffffffffffffff : UInt64) =
      (x * Float.ofBits 0x4330000000000000).toBits &&& (0x7fffffffffffffff : UInt64) := by
  have hc : Finite (0x4330000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  rw [F64Bits.toBits_mul, F64Bits.toBits_mul, neg_bits x hxf, PowExpPaths.ofBits_finite _ hc,
    mul_negate _ _ hxf hc, negate_mask]

theorem tail_neg (x y : Float) (hxf : Finite x.toBits) (ix topx sb : UInt64) :
    tailPath Pow.powLogTable Exp.expTable x y ix topx sb =
      tailPath Pow.powLogTable Exp.expTable (-x) y ix topx sb := by
  simp only [tailPath, norm_neg x hxf]

theorem sub_self_bits (x : Float) (hxf : Finite x.toBits) : (x - x).toBits = 0 := by
  have hn : Finite (Wasm.IEEE64.negate x.toBits) := PowNegate.negrel_finite _ _ (Or.inl rfl) hxf
  rw [F64Bits.toBits_sub]
  unfold Wasm.IEEE64.sub Wasm.IEEE64.add
  simp only [not_nan_of_finite hxf, not_nan_of_finite hn, not_infinite_of_finite hxf,
    not_infinite_of_finite hn, Bool.or_false, Bool.false_eq_true, ite_false, PowNegate.sv_negate,
    add_neg_cancel, beq_self_eq_true, ite_true, (F64Sign.fields_negate x.toBits).2.2]
  cases Wasm.IEEE64.sign x.toBits <;> decide

theorem finite_of_exp (w : UInt64) (h : Wasm.IEEE64.exponent w < 2047) : Finite w := by
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
  omega

theorem exp_of_finite (w : UInt64) (h : Finite w) : Wasm.IEEE64.exponent w < 2047 := by
  have h' := h
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h'
  have : Wasm.IEEE64.exponent w < 2048 := Nat.mod_lt _ (by norm_num)
  omega

/-- A negative finite nonzero `x` and a finite `y` that is not an integer give the canonical
NaN. -/
theorem nonint_nan (x y : Float) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hxf : Wasm.IEEE64.exponent x.toBits < 2047) (hx0 : 2 * x.toBits ≠ 0)
    (hyf : Wasm.IEEE64.exponent y.toBits < 2047) (hy0 : 2 * y.toBits ≠ 0)
    (hc : Pow.checkint y.toBits = 0) :
    (Pow.pow x y).toBits = Wasm.IEEE64.canonicalNaN := by
  have hzy := PowBranches.zeroinfnan_false y.toBits hyf hy0
  have hzx := PowBranches.zeroinfnan_false x.toBits hxf hx0
  have hs1 : (x.toBits >>> 63 == 1) = true := by
    rw [PowExpTheorem.sign_shift_one]
    exact hs
  have hc0 : (Pow.checkint y.toBits == 0) = true := by
    rw [hc]
    rfl
  have hcond : (decide ((x.toBits >>> 52) - 1 ≥ (0x7ff : UInt64) - 1) ||
      decide (((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be)) = true := by
    simp only [top_neg x.toBits hs, decide_true, Bool.true_or]
  simp only [Pow.pow, Pow.powWith, hcond, ite_true, hzy, hzx, hs1, hc0, Bool.true_and,
    Bool.false_eq_true, ite_false]
  rw [F64Bits.toBits_div, sub_self_bits x (finite_of_exp _ hxf)]
  decide

theorem low_zero (w : UInt64) (h : 2 * w = 0) : w.toNat % 2 ^ 63 = 0 := by
  have h1 := congrArg UInt64.toNat h
  simp only [UInt64.toNat_mul, UInt64.reduceToNat] at h1
  have hT := w.toNat_lt
  simp only [Nat.reducePow] at h1 hT ⊢
  omega

theorem low_ne (w : UInt64) (h : w.toNat % 2 ^ 63 ≠ 0) : 2 * w ≠ 0 :=
  fun h0 => h (low_zero w h0)

/-- The facts on `-x` used below, for a negative finite nonzero `x`. -/
theorem neg_facts (x : Float) (hxf : Finite x.toBits) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hx0 : 2 * x.toBits ≠ 0) :
    (-x).toBits.toNat < 2 ^ 63 ∧ (-x).toBits ≠ 0 ∧
      Wasm.IEEE64.exponent (-x).toBits < 2047 ∧ Finite (-x).toBits ∧
      value (-x).toBits = -value x.toBits := by
  have hnb := neg_bits x hxf
  have hT := x.toBits.toNat_lt
  have h2 : 2 ^ 63 ≤ x.toBits.toNat := by
    simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hs
  have hn := F64SignedRounding.negate_toNat x.toBits
  rw [hs, ite_eq_left rfl] at hn
  have hlow : x.toBits.toNat % 2 ^ 63 ≠ 0 := fun h => hx0 (by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mul, UInt64.reduceToNat]
    simp only [Nat.reducePow] at h hT ⊢
    omega)
  have hnf : Finite (-x).toBits := by
    rw [hnb]
    exact PowNegate.negrel_finite _ _ (Or.inl rfl) hxf
  refine ⟨?_, ?_, exp_of_finite _ hnf, hnf, by rw [hnb, PowNegate.value_negate]⟩
  · rw [hnb, hn]
    simp only [Nat.reducePow] at hT h2 ⊢
    omega
  · rw [hnb]
    intro h
    have := congrArg UInt64.toNat h
    rw [hn] at this
    simp only [Nat.reducePow] at hT h2 hlow this
    change _ = 0 at this
    omega

theorem pow_neg_word (x y : Float) (hxf : Finite x.toBits) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hx0 : 2 * x.toBits ≠ 0) (hyf : Finite y.toBits) (hy0 : 2 * y.toBits ≠ 0)
    (hc : Pow.checkint y.toBits ≠ 0) :
    Pow.pow x y = tailPath Pow.powLogTable Exp.expTable (-x) y (-x).toBits ((-x).toBits >>> 52)
      (if Pow.checkint y.toBits == 1 then (0x800 : UInt64) <<< 7 else 0) := by
  rw [neg_path x y hs (exp_of_finite _ hxf) hx0 (exp_of_finite _ hyf) hy0 hc, tail_neg x y hxf,
    neg_bits x hxf, ← neg_word _ hs, mask_top]

/-- An even integer `y` gives exactly `pow (-x) y`. -/
theorem even_eq (x y : Float) (hxf : Finite x.toBits) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hx0 : 2 * x.toBits ≠ 0) (hyf : Finite y.toBits) (hy0 : 2 * y.toBits ≠ 0)
    (hc : Pow.checkint y.toBits = 2) : Pow.pow x y = Pow.pow (-x) y := by
  obtain ⟨hnT, hn0, hne, -, -⟩ := neg_facts x hxf hs hx0
  rw [pow_neg_word x y hxf hs hx0 hyf hy0 (by rw [hc]; decide),
    pos_path (-x) y hnT hn0 hne (exp_of_finite _ hyf) hy0, hc,
    ite_eq_right (by decide : ¬ ((2 : UInt64) == 1) = true)]

theorem odd_exponent (w : UInt64) (h : Pow.checkint w = 1) :
    958 ≤ Wasm.IEEE64.exponent w ∧ Wasm.IEEE64.exponent w < 1086 := by
  have hw := ExpBranches.exponent_word_spec w
  simp only [ExpBranches.exponentWord] at hw
  constructor
  · by_contra hn
    have hlt : (w >>> 52) &&& 0x7ff < (0x3ff : UInt64) := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [hw]
      change _ < 1023
      omega
    have h0 : Pow.checkint w = 0 := by
      rw [PowCheckint.checkint_eq, ite_eq_left hlt]
    rw [h0] at h
    exact absurd h (by decide)
  · by_contra hn
    have h1 : ¬ (w >>> 52) &&& 0x7ff < (0x3ff : UInt64) := by
      intro h'
      have := UInt64.lt_iff_toNat_lt.mp h'
      rw [hw] at this
      change _ < 1023 at this
      omega
    have h2' : (w >>> 52) &&& 0x7ff > (1075 : UInt64) := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [hw]
      change 1075 < _
      omega
    have h0 : Pow.checkint w = 2 := by
      rw [PowCheckint.checkint_eq, ite_eq_right h1, ite_eq_left h2']
    rw [h0] at h
    exact absurd h (by decide)

/-- An odd integer `y` gives a word related to `pow (-x) y`. -/
theorem odd_rel (x y : Float) (hxf : Finite x.toBits) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hx0 : 2 * x.toBits ≠ 0) (hyf : Finite y.toBits) (hy0 : 2 * y.toBits ≠ 0)
    (hc : Pow.checkint y.toBits = 1) :
    Rel (Pow.pow x y).toBits (Pow.pow (-x) y).toBits := by
  obtain ⟨hnT, hn0, hne, hnf, hnv⟩ := neg_facts x hxf hs hx0
  obtain ⟨hey1, hey2⟩ := odd_exponent y.toBits hc
  have hyg := PowBranches.y_guard y.toBits hey1 hey2
  rw [pow_neg_word x y hxf hs hx0 hyf hy0 (by rw [hc]; decide),
    pos_path (-x) y hnT hn0 hne (exp_of_finite _ hyf) hy0, hc,
    ite_eq_left (by decide : ((1 : UInt64) == 1) = true), tail_main _ _ _ _ _ _ _ hyg,
    tail_main _ _ _ _ _ _ _ hyg]
  have hx : 0 < value (-x).toBits := by
    rw [hnv]
    have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
      apply Nat.pos_of_ne_zero
      intro h0
      exact hx0 (by
        apply UInt64.toNat_inj.mp
        have := (mag_zero _).mp h0
        have hT := x.toBits.toNat_lt
        simp only [UInt64.toNat_mul, UInt64.reduceToNat]
        simp only [Nat.reducePow] at this hT ⊢
        change _ = 0
        omega)
    have := (F64Magnitude.sign_value _ hmag).mp hs
    linarith
  have hy1 : 1 / 2 ^ 65 ≤ |value y.toBits| := by
    have := F64Magnitude.magnitude_ge y.toBits 958 (-65) (by norm_num) (by norm_num)
      (by norm_num) hey1
    have h65 : (2 : ℝ) ^ (-65 : Int) = 1 / 2 ^ 65 := by norm_num
    rwa [h65] at this
  have hy2 : |value y.toBits| < 2 ^ 63 := by
    have := F64Magnitude.magnitude_lt y.toBits 1086 63 (by norm_num) (by norm_num) hey2
    simpa using this
  exact PowMainSign.main_rel_any (-x) y hnf hx hyf hy1 hy2

/-- The accuracy of `pow` for a negative finite `x` and a finite integer `y`, against
`Real.rpow`, which equals `x ^ n` there. -/
theorem pow_neg_within (x y : Float) (hxf : Finite x.toBits) (hx : value x.toBits < 0)
    (hyf : Finite y.toBits) (n : Int) (hn : value y.toBits = n) :
    F64SignedRounding.WithinSteps 1 (value x.toBits ^ value y.toBits) (Pow.pow x y).toBits := by
  have hxe := exp_of_finite _ hxf
  have hye := exp_of_finite _ hyf
  have hxmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [PowExpSign.value_mag_zero _ h0] at hx
    exact lt_irrefl _ hx
  have hs : Wasm.IEEE64.sign x.toBits = true := (F64Magnitude.sign_value _ hxmag).mpr hx
  have hx0 : 2 * x.toBits ≠ 0 := by
    intro h
    exact (Nat.pos_iff_ne_zero.mp hxmag) ((mag_zero _).mpr (low_zero _ h))
  have honef : Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  by_cases hy0 : 2 * y.toBits = 0
  · rw [PowPositive.y_zero x y hxe hy0]
    have hYv : value y.toBits = 0 :=
      PowExpSign.value_mag_zero _ ((mag_zero _).mpr (low_zero _ hy0))
    rw [hYv, Real.rpow_zero]
    exact PowPositive.exact_within _ honef 1 PowPositive.one_word_value (by norm_num)
  have hymag : 0 < Wasm.IEEE64.scaledMagnitude y.toBits := by
    apply Nat.pos_of_ne_zero
    intro h0
    exact hy0 (by
      apply UInt64.toNat_inj.mp
      have := (mag_zero _).mp h0
      have hT := y.toBits.toNat_lt
      simp only [UInt64.toNat_mul, UInt64.reduceToNat]
      simp only [Nat.reducePow] at this hT ⊢
      change _ = 0
      omega)
  obtain ⟨hc0, hc1, hc2⟩ := PowCheckint.checkint_spec y.toBits hye hymag
  have hcne : Pow.checkint y.toBits ≠ 0 := fun h => (hc0.mp h) n hn
  obtain ⟨-, -, -, hnf, hnv⟩ := neg_facts x hxf hs hx0
  have hnpos : 0 < value (-x).toBits := by
    rw [hnv]
    linarith
  have hw := PowTheoremPos.pow_pos_within (-x) y hnf hnpos hyf
  rw [hnv, hn, Real.rpow_intCast] at hw
  rw [hn, Real.rpow_intCast]
  have h012 : Pow.checkint y.toBits = 0 ∨ Pow.checkint y.toBits = 1 ∨
      Pow.checkint y.toBits = 2 := by
    rw [PowCheckint.checkint_magnitude y.toBits hye hymag]
    split_ifs <;> decide
  rcases h012 with h0 | h1 | h2
  · exact absurd h0 hcne
  · obtain ⟨m, hm, hmodd⟩ := hc1.mp h1
    have hnm : n = m := by exact_mod_cast hn.symm.trans hm
    have hodd : Odd n := Int.odd_iff.mpr (by rw [hnm]; exact hmodd)
    have h := within_rel 1 _ _ _ (odd_rel x y hxf hs hx0 hyf hy0 h1) hw
    rwa [hodd.neg_zpow, neg_neg] at h
  · obtain ⟨m, hm, hmeven⟩ := hc2.mp h2
    have hnm : n = m := by exact_mod_cast hn.symm.trans hm
    have heven : Even n := Int.even_iff.mpr (by rw [hnm]; exact hmeven)
    rw [even_eq x y hxf hs hx0 hyf hy0 h2]
    rwa [heven.neg_zpow] at hw

#print axioms top_neg
#print axioms neg_path
#print axioms pos_path
#print axioms tail_main
#print axioms neg_word
#print axioms negate_mask
#print axioms mask_top
#print axioms neg_bits
#print axioms mul_negate
#print axioms norm_neg
#print axioms tail_neg
#print axioms sub_self_bits
#print axioms nonint_nan
#print axioms neg_facts
#print axioms pow_neg_word
#print axioms even_eq
#print axioms odd_exponent
#print axioms odd_rel
#print axioms pow_neg_within

end Verified.Examples.PowNegBase
