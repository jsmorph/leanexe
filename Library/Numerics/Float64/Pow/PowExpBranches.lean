import Library.Numerics.Float64.Exp.ExpBranches
import Library.Numerics.Float64.Pow.Compiled

/-!
The branches of `Pow.powExp` with `signBias = 0`.  The exponent field `abstop` of `x` selects
`1 + x` below `2 ^ -54`, `powExpCore` without the special flag below 512, with it below 1024,
and from 1024 on the products of `__math_uflow` and `__math_oflow`, by the sign of `x`.
-/

namespace Library.Numerics.Float64.Pow.PowExpBranches
open CodeLib.IEEE64
open LeanExe.ProofKit Library.Numerics.Float64.Exp.ExpBranches

set_option exponentiation.threshold 4096

private theorem sub_guard (a : UInt64) (hlo : 969 ≤ a.toNat) :
    (a - 969).toNat = a.toNat - 969 :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)

private theorem bias_zero : ((0 : UInt64) != 0) = false := rfl

theorem tiny_selected (tab : Array UInt64) (x xtail : Float)
    (hx : Wasm.IEEE64.exponent x.toBits < 969) :
    Pow.powExp tab x xtail 0 = 1.0 + x := by
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
  simp only [bias_zero, Bool.false_eq_true, ite_false]

theorem ordinary_selected (tab : Array UInt64) (x xtail : Float)
    (hlo : 969 ≤ Wasm.IEEE64.exponent x.toBits) (hhi : Wasm.IEEE64.exponent x.toBits < 1032) :
    Pow.powExp tab x xtail 0 = Pow.powExpCore tab x xtail 0 false := by
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

theorem special_selected (tab : Array UInt64) (x xtail : Float)
    (he : Wasm.IEEE64.exponent x.toBits = 1032) :
    Pow.powExp tab x xtail 0 = Pow.powExpCore tab x xtail 0 true := by
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

/-- From exponent field 1033 on: the overflow product for positive `x`, the underflow product
for negative `x`. -/
theorem big_selected (tab : Array UInt64) (x xtail : Float)
    (he : 1033 ≤ Wasm.IEEE64.exponent x.toBits) :
    Pow.powExp tab x xtail 0 =
      if x.toBits >>> 63 == 1 then
        Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
      else Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000 := by
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
  simp only [bias_zero, Bool.false_eq_true, ite_false]

theorem overflow_bits :
    (Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000).toBits =
      0x7FF0000000000000 := by
  rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits]
  decide +kernel

theorem underflow_bits :
    (Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000).toBits = 0 := by
  rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits]
  decide +kernel

#print axioms tiny_selected
#print axioms ordinary_selected
#print axioms special_selected
#print axioms big_selected
#print axioms overflow_bits
#print axioms underflow_bits

end Library.Numerics.Float64.Pow.PowExpBranches
