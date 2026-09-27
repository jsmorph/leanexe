import Project.ProofKit.F64ExactArithmetic
import Project.ProofKit.F64OrderComplete

namespace Project.ProofKit.F64OneSubtract
open CodeLib.IEEE64

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

theorem sub_exact_scaled (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (n k : Nat) (hn : n < 2^53)
    (hz : (Wasm.IEEE64.scaledValue a-Wasm.IEEE64.scaledValue b).natAbs = n*2^k)
    (hm : n*2^k < 2^2097) :
    Finite (Wasm.IEEE64.sub a b) ∧
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a b) =
      Wasm.IEEE64.scaledValue a-Wasm.IEEE64.scaledValue b := by
  have hneg := negate_spec b hb
  simpa only [Wasm.IEEE64.sub, hneg.2, ← sub_eq_add_neg] using
    F64ExactArithmetic.add_exact_scaled a (Wasm.IEEE64.negate b) ha hneg.1 n k hn
      (by simpa only [hneg.2, ← sub_eq_add_neg] using hz) hm

theorem one_interval_scaled (a : UInt64)
    (hl : 0x3FF0000000000000 ≤ a) (hu : a ≤ 0x4000000000000000) :
    Finite a ∧ ∃ n : Nat, n ≤ 2^52 ∧
      Wasm.IEEE64.scaledValue a = (2 : Int)^1074+(n : Int)*2^1022 := by
  have ha : Finite a := (F64Order.positiveBits_spec a (by
    simp only [F64Order.positiveBits, Bool.and_eq_true_iff, decide_eq_true_eq,
      UInt64.lt_iff_toNat_lt]
    have hl' := UInt64.le_iff_toNat_le.mp hl
    have hu' := UInt64.le_iff_toNat_le.mp hu
    change 0 < a.toNat ∧ a.toNat < 0x7FF0000000000000
    change 0x3FF0000000000000 ≤ a.toNat at hl'
    change a.toNat ≤ 0x4000000000000000 at hu'
    omega)).1
  refine ⟨ha, ?_⟩
  by_cases ht : a = 0x4000000000000000
  · subst a
    refine ⟨2^52, le_rfl, ?_⟩
    norm_num [Wasm.IEEE64.scaledValue, Wasm.IEEE64.sign,
      Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  · have hl' := UInt64.le_iff_toNat_le.mp hl
    have hu' := UInt64.le_iff_toNat_le.mp hu
    have ht' : a.toNat ≠ 0x4000000000000000 := by
      intro he
      exact ht (UInt64.toNat_inj.mp he)
    change 0x3FF0000000000000 ≤ a.toNat at hl'
    change a.toNat ≤ 0x4000000000000000 at hu'
    let n := a.toNat-0x3FF0000000000000
    have hn : n < 2^52 := by dsimp [n]; omega
    have hs : Wasm.IEEE64.sign a = false := by
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
      omega
    have he : Wasm.IEEE64.exponent a = 1023 := by
      dsimp [Wasm.IEEE64.exponent]
      omega
    have hf : Wasm.IEEE64.fraction a = n := by
      dsimp [Wasm.IEEE64.fraction, n]
      omega
    refine ⟨n, hn.le, ?_⟩
    simp only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Wasm.IEEE64.scaledMagnitude, he, hf]
    change (((2^52+n)*2^1022 : Nat) : Int) = (2 : Int)^1074+(n : Int)*2^1022
    push_cast
    rw [add_mul]
    rfl

theorem subtract_one_exact (a : UInt64)
    (hl : 0x3FF0000000000000 ≤ a) (hu : a ≤ 0x4000000000000000) :
    Finite (Wasm.IEEE64.sub a 0x3FF0000000000000) ∧
    value (Wasm.IEEE64.sub a 0x3FF0000000000000) = value a-1 ∧
    Finite (Wasm.IEEE64.sub 0x3FF0000000000000 a) ∧
    value (Wasm.IEEE64.sub 0x3FF0000000000000 a) = 1-value a := by
  obtain ⟨ha, n, hn, hv⟩ := one_interval_scaled a hl hu
  have hone : Wasm.IEEE64.scaledValue 0x3FF0000000000000 = (2 : Int)^1074 := by decide
  have hmax : n*2^1022 < 2^2097 := by
    calc
      _ ≤ 2^52*2^1022 := Nat.mul_le_mul_right _ hn
      _ < _ := by norm_num
  have hn' : n < 2^53 := by omega
  have hpos : (Wasm.IEEE64.scaledValue a-Wasm.IEEE64.scaledValue 0x3FF0000000000000).natAbs =
      n*2^1022 := by
    rw [hv, hone]
    simp only [add_sub_cancel_left, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    rfl
  have hneg : (Wasm.IEEE64.scaledValue 0x3FF0000000000000-Wasm.IEEE64.scaledValue a).natAbs =
      n*2^1022 := by
    rw [show Wasm.IEEE64.scaledValue 0x3FF0000000000000-Wasm.IEEE64.scaledValue a =
      -(Wasm.IEEE64.scaledValue a-Wasm.IEEE64.scaledValue 0x3FF0000000000000) by omega,
      Int.natAbs_neg]
    exact hpos
  have hp := sub_exact_scaled a _ ha (by rfl) n 1022 hn' hpos hmax
  have hm := sub_exact_scaled _ a (by rfl) ha n 1022 hn' hneg hmax
  refine ⟨hp.1, ?_, hm.1, ?_⟩
  · simp only [value, hp.2, hone, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
    field_simp
  · simp only [value, hm.2, hone, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
    field_simp

#print axioms subtract_one_exact
end Project.ProofKit.F64OneSubtract
