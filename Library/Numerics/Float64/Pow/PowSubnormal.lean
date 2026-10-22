import Library.Numerics.Float64.Pow.PowMainPath

/-!
A positive subnormal `x`.  `Pow.powWith` multiplies it by `2 ^ 52`, exactly, clears the sign bit,
and subtracts `52` from the exponent field, wrapping into the sign bit: the word stands for
`(2 ^ 52 + f) 2 ^ (E - 1075)` with `E = p - 51` for the position `p` of the leading bit of the
fraction field, and `E · 2 ^ 52 + f` equal to the word modulo `2 ^ 64`, as
`PowLogFinal.log_within` takes it.
-/

namespace Library.Numerics.Float64.Pow.PowSubnormal
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem two52_scaled : Wasm.IEEE64.scaledValue 0x4330000000000000 = 1 * 2 ^ 1126 := by
  decide +kernel

/-- The normalized word of a positive subnormal `x`. -/
theorem subnormal_word (x : Float) (hs : x.toBits.toNat < 2 ^ 52) (h0 : 0 < x.toBits.toNat) :
    ∃ (E : Int) (f : Nat), -51 ≤ E ∧ E ≤ 0 ∧ f < 2 ^ 52 ∧
      ((((x * Float.ofBits 0x4330000000000000).toBits &&& (0x7fffffffffffffff : UInt64)) -
        ((52 : UInt64) <<< 52)).toNat : Int) = (E * 2 ^ 52 + f) % 2 ^ 64 ∧
      value x.toBits = ((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075) := by
  set g := x.toBits.toNat
  have hexp : Wasm.IEEE64.exponent x.toBits = 0 := by
    show g / 2 ^ 52 % 2 ^ 11 = 0
    simp only [Nat.reducePow] at hs ⊢
    omega
  have hfrac : Wasm.IEEE64.fraction x.toBits = g := by
    show g % 2 ^ 52 = g
    exact Nat.mod_eq_of_lt hs
  have hsign : Wasm.IEEE64.sign x.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    show g < 2 ^ 63
    simp only [Nat.reducePow] at hs ⊢
    omega
  have hmag : Wasm.IEEE64.scaledMagnitude x.toBits = g * 2 ^ 0 := by
    simp only [Wasm.IEEE64.scaledMagnitude, hexp, hfrac, beq_self_eq_true, ite_true, pow_zero,
      mul_one]
  have hxf : Finite x.toBits := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hexp]
    decide
  have htf : Finite (0x4330000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  obtain ⟨hpf, hpv, hpm, hps⟩ := F64ExactProduct.mul_exact_scaled x.toBits 0x4330000000000000
    hxf htf g 1 0 1126 hmag (by rw [PowLogReduce.magnitude_of_value _ 1 1126 two52_scaled]; rfl)
    (by simp only [Nat.reducePow] at hs ⊢; omega) (by norm_num) (by norm_num)
  have hpb : (x * Float.ofBits 0x4330000000000000).toBits =
      Wasm.IEEE64.mul x.toBits 0x4330000000000000 := by
    rw [F64Bits.toBits_mul, PowExpPaths.ofBits_finite _ htf]
  rw [hpb]
  set prod := Wasm.IEEE64.mul x.toBits 0x4330000000000000
  -- the leading bit of `g`
  have hg0 : g ≠ 0 := by omega
  set p := Nat.log2 g
  have hp1 : 2 ^ p ≤ g := Nat.log2_self_le hg0
  have hp2 : g < 2 ^ (p + 1) := Nat.lt_log2_self
  have hp52 : p < 52 := by
    by_contra hn
    have : 2 ^ 52 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set R := g * 2 ^ (52 - p)
  have hR1 : 2 ^ 52 ≤ R := by
    calc
      2 ^ 52 = 2 ^ p * 2 ^ (52 - p) := by rw [← pow_add]; congr 1; omega
      _ ≤ R := Nat.mul_le_mul_right _ hp1
  have hR2 : R < 2 ^ 53 := by
    calc
      R < 2 ^ (p + 1) * 2 ^ (52 - p) := Nat.mul_lt_mul_of_pos_right hp2 (by positivity)
      _ = 2 ^ 53 := by rw [← pow_add]; congr 1; omega
  have hsp : Wasm.IEEE64.sign prod = false := by rw [hps, hsign]; rfl
  have hm : Wasm.IEEE64.scaledMagnitude prod = R * 2 ^ p := by
    rw [hpm]
    show g * 1 * 2 ^ (0 + 1126 - 1074) = g * 2 ^ (52 - p) * 2 ^ p
    rw [mul_one, mul_assoc, ← pow_add, show 0 + 1126 - 1074 = 52 - p + p by omega]
  have hpsv : Wasm.IEEE64.scaledValue prod = (R : Int) * 2 ^ p := by
    simp only [Wasm.IEEE64.scaledValue, hsp, Bool.false_eq_true, ite_false, hm]
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hword := F64BinadeWord.binade_word_toNat prod R p hsp hpsv hR1 hR2
  have hand : (prod &&& (0x7fffffffffffffff : UInt64)).toNat = prod.toNat := by
    rw [UInt64.toNat_and, show (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    apply Nat.mod_eq_of_lt
    rw [hword]
    simp only [Nat.reducePow] at hR2 ⊢
    omega
  refine ⟨(p : Int) - 51, R - 2 ^ 52, by omega, by omega, by omega, ?_, ?_⟩
  · rw [UInt64.toNat_sub, hand, hword, show ((52 : UInt64) <<< 52).toNat = 52 * 2 ^ 52 by rfl]
    simp only [Nat.reducePow] at hR1 hR2 ⊢
    push_cast
    omega
  · rw [value, show Wasm.IEEE64.scaledValue x.toBits = (g : Int) by
      simp only [Wasm.IEEE64.scaledValue, hsign, Bool.false_eq_true, ite_false, hmag, pow_zero,
        mul_one]]
    rw [Int.cast_natCast]
    have hN : ((2 ^ 52 + (R - 2 ^ 52) : Nat) : ℝ) = (g : ℝ) * 2 ^ (52 - p) := by
      rw [show 2 ^ 52 + (R - 2 ^ 52) = R by omega]
      show ((g * 2 ^ (52 - p) : Nat) : ℝ) = _
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hz : (2 : ℝ) ^ ((p : Int) - 51 - 1075) = 2 ^ p / 2 ^ 1126 := by
      rw [show (p : Int) - 51 - 1075 = (p : Int) - 1126 by ring, zpow_sub₀ (by norm_num),
        zpow_natCast]
      norm_num
    have h1 : (2 : ℝ) ^ 1126 = 2 ^ 1074 * (2 ^ (52 - p) * 2 ^ p) := by
      rw [← pow_add, ← pow_add, show 1074 + (52 - p + p) = 1126 by omega]
    rw [hN, hz, h1]
    field_simp

#print axioms two52_scaled
#print axioms subnormal_word

end Library.Numerics.Float64.Pow.PowSubnormal
