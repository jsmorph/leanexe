import Verified.Examples.ExpBranches
import Verified.Examples.Pow

/-!
The branches of `Pow.powWith` for a positive finite `x` and a finite `y`.  For a normal `x` and
`2 ^ -65 ≤ |y| < 2 ^ 63` (exponent field of `y` from 958 to 1085), no special case runs and the
result is `powMain` on the bits of `x`.  Otherwise, for a positive `x`: a zero `y` gives 1; a
nonzero `|y| < 2 ^ -65` gives 1 for `x = 1`, `1 + y` for `x > 1`, and `1 - y` for `x < 1`; a
finite `|y| ≥ 2 ^ 63` gives 1 for `x = 1` and otherwise the overflow or underflow product; and a
subnormal `x` with `y` in range gives `powMain` on the bits of `x` normalized with the exponent
`-52`.
-/

namespace Verified.Examples.PowBranches
open CodeLib.IEEE64 LeanExe.ProofKit ExpBranches

set_option exponentiation.threshold 4096

theorem top_word (w : UInt64) (hw : w.toNat < 2 ^ 63) :
    (w >>> 52).toNat = Wasm.IEEE64.exponent w := by
  rw [UInt64.toNat_shiftRight]
  change w.toNat >>> 52 = w.toNat / 2 ^ 52 % 2 ^ 11
  rw [Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow] at hw ⊢
  omega

theorem x_guard (w : UInt64) (hw : w.toNat < 2 ^ 63) (he1 : 1 ≤ Wasm.IEEE64.exponent w)
    (he2 : Wasm.IEEE64.exponent w ≤ 2046) :
    ¬ (w >>> 52) - 1 ≥ (0x7ff : UInt64) - 1 := by
  have ht := top_word w hw
  intro h
  have hn := UInt64.le_iff_toNat_le.mp h
  rw [UInt64.toNat_sub_of_le (w >>> 52) 1 (UInt64.le_iff_toNat_le.mpr (by rw [ht]; exact he1)),
    ht] at hn
  simp only [UInt64.reduceSub, UInt64.reduceToNat] at hn
  omega

theorem y_guard (w : UInt64) (he1 : 958 ≤ Wasm.IEEE64.exponent w)
    (he2 : Wasm.IEEE64.exponent w < 1086) :
    ¬ ((w >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be := by
  have hw := exponent_word_spec w
  simp only [exponentWord] at hw
  intro h
  have hn := UInt64.le_iff_toNat_le.mp h
  rw [UInt64.toNat_sub_of_le ((w >>> 52) &&& 0x7ff) 0x3be
    (UInt64.le_iff_toNat_le.mpr (by rw [hw]; exact he1)), hw] at hn
  simp only [UInt64.reduceSub, UInt64.reduceToNat] at hn
  omega

/-- The main path: a positive normal `x` and `2 ^ -65 ≤ |y| < 2 ^ 63`. -/
theorem main_selected (tab1 tab2 : Array UInt64) (x y : Float) (hx : x.toBits.toNat < 2 ^ 63)
    (hex1 : 1 ≤ Wasm.IEEE64.exponent x.toBits) (hex2 : Wasm.IEEE64.exponent x.toBits ≤ 2046)
    (hey1 : 958 ≤ Wasm.IEEE64.exponent y.toBits) (hey2 : Wasm.IEEE64.exponent y.toBits < 1086) :
    Pow.powWith tab1 tab2 x y = Pow.powMain tab1 tab2 x.toBits y y.toBits 0 := by
  have h1 := x_guard x.toBits hx hex1 hex2
  have h2 := y_guard y.toBits hey1 hey2
  simp only [Pow.powWith]
  rw [ite_eq_right (by simp only [h1, h2, decide_false, Bool.or_false, Bool.false_eq_true,
    not_false_eq_true])]

theorem zeroinfnan_false (w : UInt64) (hf : Wasm.IEEE64.exponent w < 2047) (h0 : 2 * w ≠ 0) :
    Pow.zeroinfnan w = false := by
  have hT := w.toNat_lt
  have h0' : (2 * w).toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by rw [h]; rfl))
  have he : w.toNat / 2 ^ 52 % 2 ^ 11 < 2047 := hf
  simp only [Pow.zeroinfnan, decide_eq_false_iff_not, ge_iff_le]
  intro h
  have hn := UInt64.le_iff_toNat_le.mp h
  simp only [UInt64.toNat_sub, UInt64.toNat_mul, UInt64.reduceToNat] at h0' hn
  simp only [Nat.reducePow] at hT h0' he hn
  omega

theorem zeroinfnan_zero (w : UInt64) (h0 : 2 * w = 0) : Pow.zeroinfnan w = true := by
  simp only [Pow.zeroinfnan, h0]
  decide

/-- The special block for a positive finite nonzero `x` and a finite nonzero `y`. -/
theorem positive_special (tab1 tab2 : Array UInt64) (x y : Float) (hx : x.toBits.toNat < 2 ^ 63)
    (hx0 : x.toBits ≠ 0) (hxf : Wasm.IEEE64.exponent x.toBits < 2047)
    (hyf : Wasm.IEEE64.exponent y.toBits < 2047) (hy0 : 2 * y.toBits ≠ 0)
    (hcond : (x.toBits >>> 52) - 1 ≥ (0x7ff : UInt64) - 1 ∨
      ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be) :
    Pow.powWith tab1 tab2 x y =
      if ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be then
        (if x.toBits == 0x3FF0000000000000 then 1.0
          else if ((y.toBits >>> 52) &&& 0x7ff) < 0x3be then
            (if x.toBits > 0x3FF0000000000000 then 1.0 + y else 1.0 - y)
          else if x.toBits > 0x3FF0000000000000 then
            (if y.toBits >>> 52 < 0x800 then
              Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000
            else Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000)
          else if y.toBits >>> 52 < 0x800 then
            Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
          else Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000)
      else Pow.powMain tab1 tab2
        (if x.toBits >>> 52 == 0 then
          ((x * Float.ofBits 0x4330000000000000).toBits &&& (0x7fffffffffffffff : UInt64)) -
            ((52 : UInt64) <<< 52)
        else x.toBits) y y.toBits 0 := by
  have hx0' : 2 * x.toBits ≠ 0 := by
    intro h
    apply hx0
    apply UInt64.toNat_inj.mp
    have := congrArg UInt64.toNat h
    simp only [UInt64.toNat_mul, UInt64.reduceToNat] at this
    simp only [Nat.reducePow] at hx this
    change x.toBits.toNat = 0
    omega
  have hzy := zeroinfnan_false y.toBits hyf hy0
  have hzx := zeroinfnan_false x.toBits hxf hx0'
  have hs : (x.toBits >>> 63 == 1) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_shiftRight] at this
    change x.toBits.toNat >>> 63 = 1 at this
    rw [Nat.shiftRight_eq_div_pow] at this
    omega
  have hc : (decide ((x.toBits >>> 52) - 1 ≥ (0x7ff : UInt64) - 1) ||
      decide (((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be)) = true := by
    rcases hcond with h | h <;> simp only [h, decide_true, Bool.true_or, Bool.or_true]
  simp only [Pow.powWith, hc, ite_true, hzy, hzx, hs, Bool.false_and, Bool.false_eq_true,
    ite_false]

#print axioms top_word
#print axioms x_guard
#print axioms y_guard
#print axioms main_selected
#print axioms zeroinfnan_false
#print axioms zeroinfnan_zero
#print axioms positive_special

end Verified.Examples.PowBranches
