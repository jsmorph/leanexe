import Verified.Examples.PowNegBase

/-!
The special cases of `Pow.pow`, against C99 Annex F.9.4.4.  `infnanY` is the block of
`Pow.powWith` for a zero, infinite, or NaN `y`, and `infnanX` the block for a zero, infinite, or
NaN `x` and a finite nonzero `y`; `pow` reduces to them by definition.  The theorems state the
result words: 1 for a zero `y` and for `x = 1`, except for a signaling NaN, where the code returns
`x + y`, a NaN; `x x`, negated for a negative `x` and an odd integer `y`, and inverted for a
negative `y`, for a zero or infinite `x`; the limits of `|x| ^ ±∞`; the canonical NaN for a NaN
argument; `1 ± y` for `|y| < 2 ^ -65`; and the overflow or underflow product for `|y| ≥ 2 ^ 63`.
-/

namespace Verified.Examples.PowSpecial
open CodeLib.IEEE64 LeanExe.ProofKit PowSignRel PowNegBase

set_option exponentiation.threshold 4096

/-- The block of `Pow.powWith` for a zero, infinite, or NaN `y`. -/
def infnanY (x y : Float) : Float :=
  if 2 * y.toBits == 0 then if Pow.issignaling x then x + y else 1.0
  else if x.toBits == 0x3FF0000000000000 then if Pow.issignaling y then x + y else 1.0
  else if 2 * x.toBits > 2 * 0x7FF0000000000000 || 2 * y.toBits > 2 * 0x7FF0000000000000 then
    x + y
  else if 2 * x.toBits == 2 * 0x3FF0000000000000 then 1.0
  else if 2 * x.toBits < 2 * 0x3FF0000000000000 then
    if y.toBits >>> 63 == 0 then 0.0 else y * y
  else if y.toBits >>> 63 == 0 then y * y else 0.0

/-- The block of `Pow.powWith` for a zero, infinite, or NaN `x` and a finite nonzero `y`. -/
def infnanX (x y : Float) : Float :=
  if y.toBits >>> 63 == 1 then
    1.0 / (if x.toBits >>> 63 == 1 && Pow.checkint y.toBits == 1 then -(x * x) else x * x)
  else if x.toBits >>> 63 == 1 && Pow.checkint y.toBits == 1 then -(x * x) else x * x

theorem two_mul_toNat (w : UInt64) : (2 * w).toNat = 2 * (w.toNat % 2 ^ 63) := by
  rw [UInt64.toNat_mul]
  have := w.toNat_lt
  simp only [UInt64.reduceToNat, Nat.reducePow] at this ⊢
  omega

theorem two_mul_zero (w : UInt64) (h : 2 * w = 0) : w = 0 ∨ w = 0x8000000000000000 := by
  have h1 := low_zero w h
  have hT := w.toNat_lt
  simp only [Nat.reducePow] at h1 hT
  rcases (show w.toNat = 0 ∨ w.toNat = 9223372036854775808 by omega) with h2 | h2
  · exact Or.inl (UInt64.toNat_inj.mp (by rw [h2]; rfl))
  · exact Or.inr (UInt64.toNat_inj.mp (by rw [h2]; rfl))

theorem zeroinfnan_exp (w : UInt64) (h : Pow.zeroinfnan w = true) :
    Wasm.IEEE64.exponent w = 0 ∨ Wasm.IEEE64.exponent w = 2047 := by
  have hT := w.toNat_lt
  simp only [Pow.zeroinfnan, decide_eq_true_eq, ge_iff_le] at h
  have hn := UInt64.le_iff_toNat_le.mp h
  simp only [UInt64.toNat_sub, UInt64.toNat_mul, UInt64.reduceToNat] at hn
  have he : Wasm.IEEE64.exponent w = w.toNat / 2 ^ 52 % 2 ^ 11 := rfl
  rw [he]
  simp only [Nat.reducePow] at hT hn ⊢
  omega

theorem zeroinfnan_top (w : UInt64) (h : Wasm.IEEE64.exponent w = 2047) :
    Pow.zeroinfnan w = true := by
  have hT := w.toNat_lt
  have he : w.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := h
  simp only [Pow.zeroinfnan, decide_eq_true_eq, ge_iff_le]
  apply UInt64.le_iff_toNat_le.mpr
  simp only [UInt64.toNat_sub, UInt64.toNat_mul, UInt64.reduceToNat]
  simp only [Nat.reducePow] at hT he ⊢
  omega

theorem ytest_of (w : UInt64)
    (h : Wasm.IEEE64.exponent w < 958 ∨ 1086 ≤ Wasm.IEEE64.exponent w) :
    ((w >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be := by
  have hw := ExpBranches.exponent_word_spec w
  simp only [ExpBranches.exponentWord] at hw
  have hlt : Wasm.IEEE64.exponent w < 2048 := Nat.mod_lt _ (by norm_num)
  have hs : (((w >>> 52) &&& 0x7ff) - 0x3be).toNat =
      (2 ^ 64 - 958 + Wasm.IEEE64.exponent w) % 2 ^ 64 := by
    rw [UInt64.toNat_sub, hw]
    rfl
  apply UInt64.le_iff_toNat_le.mpr
  rw [hs]
  change 128 ≤ _
  simp only [Nat.reducePow]
  omega

theorem xtest_of (w : UInt64) (h : Wasm.IEEE64.exponent w = 0 ∨
    Wasm.IEEE64.exponent w = 2047 ∨ Wasm.IEEE64.sign w = true) :
    (w >>> 52) - 1 ≥ (0x7ff : UInt64) - 1 := by
  have hT := w.toNat_lt
  have h1 : (w >>> 52).toNat = w.toNat / 2 ^ 52 := by
    rw [UInt64.toNat_shiftRight]
    change w.toNat >>> 52 = _
    rw [Nat.shiftRight_eq_div_pow]
  have hs : ((w >>> 52) - 1).toNat = (2 ^ 64 - 1 + w.toNat / 2 ^ 52) % 2 ^ 64 := by
    rw [UInt64.toNat_sub, h1]
    rfl
  apply UInt64.le_iff_toNat_le.mpr
  rw [hs]
  change 2046 ≤ _
  have he : Wasm.IEEE64.exponent w = w.toNat / 2 ^ 52 % 2 ^ 11 := rfl
  have hsg : Wasm.IEEE64.sign w = decide (2 ^ 63 ≤ w.toNat) := rfl
  rw [he, hsg] at h
  simp only [decide_eq_true_eq, Nat.reducePow] at h hT ⊢
  omega

/-- `pow` reduces to `infnanY` for a zero, infinite, or NaN `y`. -/
theorem pow_y_special (x y : Float) (hz : Pow.zeroinfnan y.toBits = true) :
    Pow.pow x y = infnanY x y := by
  have hyt := ytest_of y.toBits (by rcases zeroinfnan_exp _ hz with h | h <;> omega)
  have hcond : (decide ((x.toBits >>> 52) - 1 ≥ (0x7ff : UInt64) - 1) ||
      decide (((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be)) = true := by
    simp only [hyt, decide_true, Bool.or_true]
  simp only [Pow.pow, Pow.powWith, hcond, ite_true, hz]
  rfl

/-- `pow` reduces to `infnanX` for a zero, infinite, or NaN `x` and a finite nonzero `y`. -/
theorem pow_x_special (x y : Float) (hzy : Pow.zeroinfnan y.toBits = false)
    (hzx : Pow.zeroinfnan x.toBits = true) : Pow.pow x y = infnanX x y := by
  have hxt := xtest_of x.toBits (by rcases zeroinfnan_exp _ hzx with h | h <;> simp [h])
  have hcond : (decide ((x.toBits >>> 52) - 1 ≥ (0x7ff : UInt64) - 1) ||
      decide (((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be)) = true := by
    simp only [hxt, decide_true, Bool.true_or]
  simp only [Pow.pow, Pow.powWith, hcond, ite_true, hzy, hzx, Bool.false_eq_true, ite_false]
  rfl

/-- A signaling NaN is a NaN. -/
theorem signaling_nan (x : Float) (h : Pow.issignaling x = true) :
    Wasm.IEEE64.isNaN x.toBits = true := by
  have hT := x.toBits.toNat_lt
  have hhigh := PowPositive.xor_high x.toBits
  have htT := (x.toBits ^^^ 0x0008000000000000).toNat_lt
  have hlow : (x.toBits ^^^ 0x0008000000000000).toNat % 2 ^ 52 =
      (x.toBits.toNat % 2 ^ 52) ^^^ 2 ^ 51 := by
    rw [UInt64.toNat_xor, show (0x0008000000000000 : UInt64).toNat = 2 ^ 51 by rfl]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_mod_two_pow,
      Nat.testBit_two_pow]
    by_cases hj : j < 52
    · simp [hj]
    · have hj' : ¬ (51 = j) := by omega
      simp [hj, hj']
  simp only [Pow.issignaling, decide_eq_true_eq, gt_iff_lt] at h
  have hn := UInt64.lt_iff_toNat_lt.mp h
  simp only [two_mul_toNat] at hn
  unfold Wasm.IEEE64.isNaN
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  have he : Wasm.IEEE64.exponent x.toBits = x.toBits.toNat / 2 ^ 52 % 2 ^ 11 := rfl
  have hf : Wasm.IEEE64.fraction x.toBits = x.toBits.toNat % 2 ^ 52 := rfl
  rw [he, hf]
  by_cases ha : x.toBits.toNat % 2 ^ 52 = 0
  · rw [ha, Nat.zero_xor] at hlow
    exfalso
    simp only [UInt64.reduceToNat, Nat.reducePow] at hT hhigh htT hlow hn
    omega
  · refine ⟨?_, ha⟩
    simp only [UInt64.reduceToNat, Nat.reducePow] at hT hhigh htT hn ⊢
    omega

/-- `pow x (±0)`: 1, or `x + y` for a signaling NaN `x`. -/
theorem zero_exp (x y : Float) (hy0 : 2 * y.toBits = 0) :
    Pow.pow x y = if Pow.issignaling x then x + y else 1.0 := by
  rw [pow_y_special x y (PowBranches.zeroinfnan_zero _ hy0)]
  unfold infnanY
  rw [ite_eq_left (by simp [hy0])]

/-- Annex F: `pow (x, ±0) = 1` for every `x` other than a signaling NaN. -/
theorem zero_exp_one (x y : Float) (hy0 : 2 * y.toBits = 0) (hs : Pow.issignaling x = false) :
    (Pow.pow x y).toBits = 0x3FF0000000000000 := by
  rw [zero_exp x y hy0, hs, ite_eq_right Bool.false_ne_true]
  exact ExpSpecialNegative.one_bits

/-- Annex F gives 1 for a signaling NaN `x` as well; the code returns the canonical NaN. -/
theorem zero_exp_snan (x y : Float) (hy0 : 2 * y.toBits = 0) (hs : Pow.issignaling x = true) :
    (Pow.pow x y).toBits = Wasm.IEEE64.canonicalNaN := by
  rw [zero_exp x y hy0, hs, ite_eq_left rfl, F64Bits.toBits_add]
  simp [Wasm.IEEE64.add, signaling_nan x hs]

/-- Annex F: `pow (+1, y) = 1` for every `y` other than a signaling NaN, for which the code
returns `x + y`, a NaN. -/
theorem one_base (x y : Float) (hx : x.toBits = 0x3FF0000000000000) :
    (Pow.pow x y).toBits =
      if Pow.issignaling y then (x + y).toBits else 0x3FF0000000000000 := by
  have hxs : Pow.issignaling x = false := by
    unfold Pow.issignaling
    rw [hx]
    decide
  have hxone : (x.toBits == 0x3FF0000000000000) = true := by simp [hx]
  have hye : Wasm.IEEE64.exponent y.toBits < 2048 := Nat.mod_lt _ (by norm_num)
  by_cases hy0 : 2 * y.toBits = 0
  · have hys : Pow.issignaling y = false := by
      unfold Pow.issignaling
      rcases two_mul_zero _ hy0 with h | h <;> rw [h] <;> decide
    rw [zero_exp_one x y hy0 hxs, hys, ite_eq_right Bool.false_ne_true]
  by_cases hy2047 : Wasm.IEEE64.exponent y.toBits = 2047
  · rw [pow_y_special x y (zeroinfnan_top _ hy2047)]
    unfold infnanY
    rw [ite_eq_right (by simpa using hy0), ite_eq_left hxone]
    split_ifs
    · rfl
    · exact ExpSpecialNegative.one_bits
  · have hyf : Wasm.IEEE64.exponent y.toBits < 2047 := by omega
    rw [PowPositive.not_signaling y hyf, ite_eq_right Bool.false_ne_true]
    have hxT : x.toBits.toNat < 2 ^ 63 := by
      rw [hx]
      decide
    rw [pos_path x y hxT (by rw [hx]; decide) (by rw [hx]; decide) hyf hy0]
    by_cases hyt : ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be
    · simp only [tailPath, hyt, ite_true, hxone]
      exact ExpSpecialNegative.one_bits
    · rw [tail_main _ _ _ _ _ _ _ hyt]
      have htop : (x.toBits >>> 52 == 0) = false := by
        rw [hx]
        decide
      rw [htop, ite_eq_right Bool.false_ne_true, hx]
      have hey : 958 ≤ Wasm.IEEE64.exponent y.toBits := by
        by_contra hn
        exact hyt (ytest_of _ (Or.inl (by omega)))
      exact PowPositive.main_one y hyf (by omega)

theorem pow_x_special' (x y : Float) (hx : 2 * x.toBits = 0 ∨ Wasm.IEEE64.exponent x.toBits = 2047)
    (hyf : Finite y.toBits) (hy0 : 2 * y.toBits ≠ 0) : Pow.pow x y = infnanX x y := by
  apply pow_x_special x y (PowBranches.zeroinfnan_false _ (exp_of_finite _ hyf) hy0)
  rcases hx with h | h
  · exact PowBranches.zeroinfnan_zero _ h
  · exact zeroinfnan_top _ h

theorem infnanX_bits (x y : Float) (x2 nx2 r rn : UInt64) (hx2 : (x * x).toBits = x2)
    (hnx2 : (-(x * x)).toBits = nx2) (hr : Wasm.IEEE64.div 0x3FF0000000000000 x2 = r)
    (hrn : Wasm.IEEE64.div 0x3FF0000000000000 nx2 = rn) :
    (infnanX x y).toBits =
      if Wasm.IEEE64.sign y.toBits then
        (if Wasm.IEEE64.sign x.toBits ∧ Pow.checkint y.toBits = 1 then rn else r)
      else if Wasm.IEEE64.sign x.toBits ∧ Pow.checkint y.toBits = 1 then nx2 else x2 := by
  unfold infnanX
  rw [PowExpTheorem.sign_shift_one, PowExpTheorem.sign_shift_one]
  simp only [Bool.and_eq_true, beq_iff_eq]
  split_ifs <;> simp only [F64Bits.toBits_div, ExpSpecialNegative.one_bits, hx2, hnx2] <;>
    first | exact hr | exact hrn

/-- Annex F for `x = ±0` and a finite nonzero `y`: `±∞` for an odd integer `y < 0` (the sign of
`x`), `+∞` for any other `y < 0`, `±0` for an odd integer `y > 0`, and `+0` for any other
`y > 0`.  `checkint y = 1` exactly when `y` is an odd integer (`PowCheckint.checkint_spec`). -/
theorem zero_base (x y : Float) (hx : x.toBits = 0 ∨ x.toBits = 0x8000000000000000)
    (hyf : Finite y.toBits) (hy0 : 2 * y.toBits ≠ 0) :
    (Pow.pow x y).toBits =
      if Wasm.IEEE64.sign y.toBits then
        (if Wasm.IEEE64.sign x.toBits ∧ Pow.checkint y.toBits = 1 then 0xFFF0000000000000
          else 0x7FF0000000000000)
      else if Wasm.IEEE64.sign x.toBits ∧ Pow.checkint y.toBits = 1 then 0x8000000000000000
      else 0 := by
  have hx2 : 2 * x.toBits = 0 := by rcases hx with h | h <;> rw [h] <;> decide
  have hxx : (x * x).toBits = 0 := by
    rw [F64Bits.toBits_mul]
    rcases hx with h | h <;> rw [h] <;> decide +kernel
  have hnx : (-(x * x)).toBits = 0x8000000000000000 := by
    rw [F64Bits.toBits_neg, hxx]
    decide +kernel
  rw [pow_x_special' x y (Or.inl hx2) hyf hy0]
  exact infnanX_bits x y 0 0x8000000000000000 0x7FF0000000000000 0xFFF0000000000000 hxx hnx
    (by decide +kernel) (by decide +kernel)

/-- Annex F for `x = ±∞` and a finite nonzero `y`: `-0` for `x = -∞` and an odd integer `y < 0`,
`+0` for any other `y < 0`, `-∞` for `x = -∞` and an odd integer `y > 0`, and `+∞` for any
other `y > 0`. -/
theorem inf_base (x y : Float)
    (hx : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000)
    (hyf : Finite y.toBits) (hy0 : 2 * y.toBits ≠ 0) :
    (Pow.pow x y).toBits =
      if Wasm.IEEE64.sign y.toBits then
        (if Wasm.IEEE64.sign x.toBits ∧ Pow.checkint y.toBits = 1 then 0x8000000000000000
          else 0)
      else if Wasm.IEEE64.sign x.toBits ∧ Pow.checkint y.toBits = 1 then 0xFFF0000000000000
      else 0x7FF0000000000000 := by
  have hxe : Wasm.IEEE64.exponent x.toBits = 2047 := by
    rcases hx with h | h <;> rw [h] <;> decide
  have hxx : (x * x).toBits = 0x7FF0000000000000 := by
    rw [F64Bits.toBits_mul]
    rcases hx with h | h <;> rw [h] <;> decide +kernel
  have hnx : (-(x * x)).toBits = 0xFFF0000000000000 := by
    rw [F64Bits.toBits_neg, hxx]
    decide +kernel
  rw [pow_x_special' x y (Or.inr hxe) hyf hy0]
  exact infnanX_bits x y 0x7FF0000000000000 0xFFF0000000000000 0 0x8000000000000000 hxx hnx
    (by decide +kernel) (by decide +kernel)

theorem not_nan_low (w : UInt64) (h : Wasm.IEEE64.isNaN w = false) :
    w.toNat % 2 ^ 63 ≤ 0x7FF0000000000000 := by
  by_contra hn
  have hT := w.toNat_lt
  have he : Wasm.IEEE64.exponent w = 2047 := by
    show w.toNat / 2 ^ 52 % 2 ^ 11 = 2047
    simp only [Nat.reducePow] at hT hn ⊢
    omega
  have hf : Wasm.IEEE64.fraction w ≠ 0 := by
    show w.toNat % 2 ^ 52 ≠ 0
    simp only [Nat.reducePow] at hT hn ⊢
    omega
  have hnan : Wasm.IEEE64.isNaN w = true := by
    unfold Wasm.IEEE64.isNaN
    rw [he]
    simp [hf]
  rw [h] at hnan
  exact absurd hnan (by decide)

/-- Annex F for `y = ±∞` and a `x` other than `+1` and NaN: 1 for `x = -1`; for `|x| < 1`, `+0`
when `y = +∞` and `+∞` when `y = -∞`; for `|x| > 1`, `+∞` when `y = +∞` and `+0` when
`y = -∞`.  `|x|` is compared through the low 63 bits of `x`, which order the magnitudes. -/
theorem inf_exp (x y : Float) (hy : y.toBits = 0x7FF0000000000000 ∨ y.toBits = 0xFFF0000000000000)
    (hxn : Wasm.IEEE64.isNaN x.toBits = false) (hx1 : x.toBits ≠ 0x3FF0000000000000) :
    (Pow.pow x y).toBits =
      if x.toBits.toNat % 2 ^ 63 = 0x3FF0000000000000 then 0x3FF0000000000000
      else if x.toBits.toNat % 2 ^ 63 < 0x3FF0000000000000 then
        (if Wasm.IEEE64.sign y.toBits then 0x7FF0000000000000 else 0)
      else if Wasm.IEEE64.sign y.toBits then 0 else 0x7FF0000000000000 := by
  have hye : Wasm.IEEE64.exponent y.toBits = 2047 := by
    rcases hy with h | h <;> rw [h] <;> decide
  have hlow := not_nan_low x.toBits hxn
  rw [pow_y_special x y (zeroinfnan_top _ hye)]
  unfold infnanY
  have hy0 : ¬ (2 * y.toBits == 0) = true := by rcases hy with h | h <;> rw [h] <;> decide
  have hxo : ¬ (x.toBits == 0x3FF0000000000000) = true := by simpa using hx1
  have hgt : ¬ (2 * x.toBits > 2 * 0x7FF0000000000000 ||
      2 * y.toBits > 2 * 0x7FF0000000000000) = true := by
    have h1 : ¬ 2 * x.toBits > 2 * 0x7FF0000000000000 := by
      intro h
      have := UInt64.lt_iff_toNat_lt.mp h
      simp only [two_mul_toNat, UInt64.reduceToNat, Nat.reducePow] at this hlow
      omega
    have h2 : ¬ 2 * y.toBits > 2 * 0x7FF0000000000000 := by
      rcases hy with h | h <;> rw [h] <;> decide
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact not_or.mpr ⟨h1, h2⟩
  rw [ite_eq_right hy0, ite_eq_right hxo, ite_eq_right hgt]
  have hyy : (y * y).toBits = 0x7FF0000000000000 := by
    rw [F64Bits.toBits_mul]
    rcases hy with h | h <;> rw [h] <;> decide +kernel
  have hys : (y.toBits >>> 63 == 0) = !Wasm.IEEE64.sign y.toBits := by
    rcases hy with h | h <;> rw [h] <;> rfl
  have heq : (2 * x.toBits == 2 * 0x3FF0000000000000) =
      decide (x.toBits.toNat % 2 ^ 63 = 0x3FF0000000000000) := by
    by_cases h : x.toBits.toNat % 2 ^ 63 = 0x3FF0000000000000
    · rw [decide_eq_true h]
      apply beq_iff_eq.mpr
      apply UInt64.toNat_inj.mp
      simp only [two_mul_toNat, h]
      decide
    · rw [decide_eq_false h]
      apply beq_eq_false_iff_ne.mpr
      intro h'
      have := congrArg UInt64.toNat h'
      simp only [two_mul_toNat, UInt64.reduceToNat, Nat.reducePow] at this h
      omega
  have hlt : (2 * x.toBits < 2 * 0x3FF0000000000000) ↔
      x.toBits.toNat % 2 ^ 63 < 0x3FF0000000000000 := by
    rw [UInt64.lt_iff_toNat_lt]
    simp only [two_mul_toNat, UInt64.reduceToNat, Nat.reducePow]
    constructor <;> intro h <;> omega
  rw [heq, hys]
  by_cases h1 : x.toBits.toNat % 2 ^ 63 = 0x3FF0000000000000
  · rw [decide_eq_true h1, ite_eq_left rfl, ite_eq_left h1]
    exact ExpSpecialNegative.one_bits
  · rw [decide_eq_false h1, ite_eq_right Bool.false_ne_true, ite_eq_right h1]
    by_cases h2 : x.toBits.toNat % 2 ^ 63 < 0x3FF0000000000000
    · rw [ite_eq_left (hlt.mpr h2), ite_eq_left h2]
      cases Wasm.IEEE64.sign y.toBits
      · rfl
      · exact hyy
    · rw [ite_eq_right (fun h => h2 (hlt.mp h)), ite_eq_right h2]
      cases Wasm.IEEE64.sign y.toBits
      · exact hyy
      · rfl

/-- Annex F: `pow (-1, ±∞) = 1`. -/
theorem minus_one_inf (x y : Float) (hx : x.toBits = 0xBFF0000000000000)
    (hy : y.toBits = 0x7FF0000000000000 ∨ y.toBits = 0xFFF0000000000000) :
    (Pow.pow x y).toBits = 0x3FF0000000000000 := by
  rw [inf_exp x y hy (by rw [hx]; decide) (by rw [hx]; decide), hx, ite_eq_left (by decide)]

/-- A NaN `x` and a nonzero `y` give the canonical NaN. -/
theorem nan_base (x y : Float) (hxn : Wasm.IEEE64.isNaN x.toBits = true)
    (hy0 : 2 * y.toBits ≠ 0) : (Pow.pow x y).toBits = Wasm.IEEE64.canonicalNaN := by
  have hxe : Wasm.IEEE64.exponent x.toBits = 2047 := by
    unfold Wasm.IEEE64.isNaN at hxn
    simp only [Bool.and_eq_true, beq_iff_eq] at hxn
    exact hxn.1
  by_cases hzy : Pow.zeroinfnan y.toBits = true
  · rw [pow_y_special x y hzy]
    unfold infnanY
    have hy0' : ¬ (2 * y.toBits == 0) = true := by simpa using hy0
    have hxo : ¬ (x.toBits == 0x3FF0000000000000) = true := by
      intro h
      rw [beq_iff_eq.mp h] at hxn
      exact absurd hxn (by decide)
    have hgt : (2 * x.toBits > 2 * 0x7FF0000000000000 ||
        2 * y.toBits > 2 * 0x7FF0000000000000) = true := by
      have h1 : 2 * x.toBits > 2 * 0x7FF0000000000000 := by
        apply UInt64.lt_iff_toNat_lt.mpr
        simp only [two_mul_toNat]
        have hT := x.toBits.toNat_lt
        unfold Wasm.IEEE64.isNaN at hxn
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hxn
        have he : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := hxn.1
        have hf : ¬ x.toBits.toNat % 2 ^ 52 = 0 := hxn.2
        simp only [UInt64.reduceToNat, Nat.reducePow] at hT he hf ⊢
        omega
      rw [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl h1
    rw [ite_eq_right hy0', ite_eq_right hxo, ite_eq_left hgt, F64Bits.toBits_add]
    simp [Wasm.IEEE64.add, hxn]
  · have hzy' : Pow.zeroinfnan y.toBits = false := by simpa using hzy
    rw [pow_x_special x y hzy' (zeroinfnan_top _ hxe)]
    have hxx : (x * x).toBits = Wasm.IEEE64.canonicalNaN := by
      rw [F64Bits.toBits_mul]
      exact mul_nan_left _ hxn
    have hnx : (-(x * x)).toBits = Wasm.IEEE64.canonicalNaN := by
      rw [F64Bits.toBits_neg, F64Sign.sub_negZero, hxx]
      rfl
    rw [infnanX_bits x y _ _ _ _ hxx hnx rfl rfl]
    split_ifs <;> rfl

/-- A NaN `y` and an `x` other than `+1` give the canonical NaN. -/
theorem nan_exp (x y : Float) (hyn : Wasm.IEEE64.isNaN y.toBits = true)
    (hx1 : x.toBits ≠ 0x3FF0000000000000) :
    (Pow.pow x y).toBits = Wasm.IEEE64.canonicalNaN := by
  have hye : Wasm.IEEE64.exponent y.toBits = 2047 := by
    unfold Wasm.IEEE64.isNaN at hyn
    simp only [Bool.and_eq_true, beq_iff_eq] at hyn
    exact hyn.1
  rw [pow_y_special x y (zeroinfnan_top _ hye)]
  unfold infnanY
  have hy0 : ¬ (2 * y.toBits == 0) = true := by
    intro h
    have h0 := low_zero _ (beq_iff_eq.mp h)
    have := (zero_not_nan _ h0).1
    rw [this] at hyn
    exact absurd hyn (by decide)
  have hxo : ¬ (x.toBits == 0x3FF0000000000000) = true := by simpa using hx1
  have hgt : (2 * x.toBits > 2 * 0x7FF0000000000000 ||
      2 * y.toBits > 2 * 0x7FF0000000000000) = true := by
    have h2 : 2 * y.toBits > 2 * 0x7FF0000000000000 := by
      apply UInt64.lt_iff_toNat_lt.mpr
      simp only [two_mul_toNat]
      have hT := y.toBits.toNat_lt
      unfold Wasm.IEEE64.isNaN at hyn
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hyn
      have he : y.toBits.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := hyn.1
      have hf : ¬ y.toBits.toNat % 2 ^ 52 = 0 := hyn.2
      simp only [UInt64.reduceToNat, Nat.reducePow] at hT he hf ⊢
      omega
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact Or.inr h2
  rw [ite_eq_right hy0, ite_eq_right hxo, ite_eq_left hgt, F64Bits.toBits_add]
  simp [Wasm.IEEE64.add, hyn]

/-- `tailPath` from `2 ^ 63` on or below `2 ^ -65` in `|y|`. -/
theorem tail_special (x y : Float) (ix topx sb : UInt64)
    (h : ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be) :
    tailPath Pow.powLogTable Exp.expTable x y ix topx sb =
      if ix == 0x3FF0000000000000 then 1.0
      else if ((y.toBits >>> 52) &&& 0x7ff) < 0x3be then
        (if ix > 0x3FF0000000000000 then 1.0 + y else 1.0 - y)
      else if ix > 0x3FF0000000000000 then
        (if y.toBits >>> 52 < 0x800 then
          Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000
        else Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000)
      else if y.toBits >>> 52 < 0x800 then
        Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
      else Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000 := by
  simp only [tailPath, h, ite_true]

/-- `|y| < 2 ^ -65`, nonzero, and a positive finite `x ≠ 1`: `1 + y` for `x > 1` and `1 - y`
for `x < 1`. -/
theorem tiny_exp (x y : Float) (hxf : Finite x.toBits) (hx : 0 < value x.toBits)
    (hx1 : x.toBits ≠ 0x3FF0000000000000) (hy0 : 2 * y.toBits ≠ 0)
    (hey : Wasm.IEEE64.exponent y.toBits < 958) :
    Pow.pow x y = if x.toBits > 0x3FF0000000000000 then 1.0 + y else 1.0 - y := by
  have hs := PowExpPaths.sign_of_pos _ hx
  have hT : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hx0 : x.toBits ≠ 0 := by
    intro h
    rw [h, F64Magnitude.value_zero] at hx
    exact lt_irrefl _ hx
  have hyt := ytest_of y.toBits (Or.inl hey)
  have hlt : ((y.toBits >>> 52) &&& 0x7ff) < (0x3be : UInt64) := by
    have hw := ExpBranches.exponent_word_spec y.toBits
    simp only [ExpBranches.exponentWord] at hw
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [hw]
    exact hey
  rw [pos_path x y hT hx0 (exp_of_finite _ hxf) (by omega) hy0, tail_special _ _ _ _ _ hyt,
    ite_eq_right (by simpa using hx1), ite_eq_left hlt]

/-- `|y| ≥ 2 ^ 63`, finite, and a positive finite `x ≠ 1`: positive infinity when `x > 1` and
`y > 0` or `x < 1` and `y < 0`, and positive zero otherwise. -/
theorem huge_exp (x y : Float) (hxf : Finite x.toBits) (hx : 0 < value x.toBits)
    (hx1 : x.toBits ≠ 0x3FF0000000000000) (hyf : Finite y.toBits)
    (hey : 1086 ≤ Wasm.IEEE64.exponent y.toBits) :
    (Pow.pow x y).toBits =
      if x.toBits > 0x3FF0000000000000 then
        (if Wasm.IEEE64.sign y.toBits then 0 else 0x7FF0000000000000)
      else if Wasm.IEEE64.sign y.toBits then 0x7FF0000000000000 else 0 := by
  have hs := PowExpPaths.sign_of_pos _ hx
  have hT : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hx0 : x.toBits ≠ 0 := by
    intro h
    rw [h, F64Magnitude.value_zero] at hx
    exact lt_irrefl _ hx
  have hy0 : 2 * y.toBits ≠ 0 := by
    intro h
    have := (zero_fields _ (low_zero _ h)).1
    omega
  have hyt := ytest_of y.toBits (Or.inr hey)
  have hnlt : ¬ ((y.toBits >>> 52) &&& 0x7ff) < (0x3be : UInt64) := by
    have hw := ExpBranches.exponent_word_spec y.toBits
    simp only [ExpBranches.exponentWord] at hw
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    rw [hw] at this
    change _ < 958 at this
    omega
  rw [pos_path x y hT hx0 (exp_of_finite _ hxf) (exp_of_finite _ hyf) hy0,
    tail_special _ _ _ _ _ hyt, ite_eq_right (by simpa using hx1), ite_eq_right hnlt]
  have htop : (y.toBits >>> 52 < 0x800) ↔ Wasm.IEEE64.sign y.toBits = false :=
    PowTheoremPos.sign_top _
  by_cases hgt : x.toBits > 0x3FF0000000000000
  · rw [ite_eq_left hgt, ite_eq_left hgt]
    cases hsy : Wasm.IEEE64.sign y.toBits
    · rw [ite_eq_left (htop.mpr hsy), PowExpBranches.overflow_bits]
      rfl
    · rw [ite_eq_right (fun h => by rw [htop.mp h] at hsy; exact absurd hsy (by decide)),
        PowExpBranches.underflow_bits]
      rfl
  · rw [ite_eq_right hgt, ite_eq_right hgt]
    cases hsy : Wasm.IEEE64.sign y.toBits
    · rw [ite_eq_left (htop.mpr hsy), PowExpBranches.underflow_bits]
      rfl
    · rw [ite_eq_right (fun h => by rw [htop.mp h] at hsy; exact absurd hsy (by decide)),
        PowExpBranches.overflow_bits]
      rfl

/-- Annex F: a negative finite `x` and a finite `y` that is not an integer give a NaN, here the
canonical NaN. -/
theorem neg_nonint (x y : Float) (hxf : Finite x.toBits) (hx : value x.toBits < 0)
    (hyf : Finite y.toBits) (hy : ∀ n : Int, value y.toBits ≠ n) :
    (Pow.pow x y).toBits = Wasm.IEEE64.canonicalNaN := by
  have hxmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [PowExpSign.value_mag_zero _ h0] at hx
    exact lt_irrefl _ hx
  have hs : Wasm.IEEE64.sign x.toBits = true := (F64Magnitude.sign_value _ hxmag).mpr hx
  have hx0 : 2 * x.toBits ≠ 0 := by
    intro h
    exact (Nat.pos_iff_ne_zero.mp hxmag) ((mag_zero _).mpr (low_zero _ h))
  have hymag : 0 < Wasm.IEEE64.scaledMagnitude y.toBits := by
    apply Nat.pos_of_ne_zero
    intro h0
    exact hy 0 (by rw [PowExpSign.value_mag_zero _ h0]; simp)
  have hy0 : 2 * y.toBits ≠ 0 := by
    intro h
    exact (Nat.pos_iff_ne_zero.mp hymag) ((mag_zero _).mpr (low_zero _ h))
  have hc := (PowCheckint.checkint_spec y.toBits (exp_of_finite _ hyf) hymag).1.mpr hy
  exact nonint_nan x y hs (exp_of_finite _ hxf) hx0 (exp_of_finite _ hyf) hy0 hc

#print axioms two_mul_toNat
#print axioms two_mul_zero
#print axioms zeroinfnan_exp
#print axioms zeroinfnan_top
#print axioms ytest_of
#print axioms xtest_of
#print axioms pow_y_special
#print axioms pow_x_special
#print axioms signaling_nan
#print axioms zero_exp
#print axioms zero_exp_one
#print axioms zero_exp_snan
#print axioms one_base
#print axioms infnanX_bits
#print axioms zero_base
#print axioms inf_base
#print axioms not_nan_low
#print axioms inf_exp
#print axioms minus_one_inf
#print axioms nan_base
#print axioms nan_exp
#print axioms tail_special
#print axioms tiny_exp
#print axioms huge_exp
#print axioms neg_nonint

end Verified.Examples.PowSpecial
