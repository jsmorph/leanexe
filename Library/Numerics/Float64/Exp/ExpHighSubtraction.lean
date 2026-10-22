import Library.Numerics.Float64.Exp.ExpReductionExact
import LeanExe.ProofKit.F64NormalizedMagnitude

namespace Library.Numerics.Float64.Exp.ExpHighSubtraction
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem add_high_grid_exact (x y : UInt64) (hxf : Finite x) (hyf : Finite y)
    (he : Wasm.IEEE64.exponent x ≤ 1032) (b : Int)
    (hy : Wasm.IEEE64.scaledValue y = b * 2 ^ 1031)
    (hr : |value x + value y| ≤ |value x|) :
    Finite (Wasm.IEEE64.add x y) ∧
    value (Wasm.IEEE64.add x y) = value x + value y := by
  let shift := Wasm.IEEE64.exponent x - 1
  let sig := if Wasm.IEEE64.exponent x = 0 then Wasm.IEEE64.fraction x
    else 2 ^ 52 + Wasm.IEEE64.fraction x
  let signedSig : Int := if Wasm.IEEE64.sign x then -(sig : Int) else sig
  have hs : shift ≤ 1031 := by dsimp [shift]; omega
  have hf : Wasm.IEEE64.fraction x < 2 ^ 52 :=
    Nat.mod_lt _ (by positivity)
  have hsig : sig ≤ 2 ^ 53 := by dsimp [sig]; split_ifs <;> omega
  have hmag : Wasm.IEEE64.scaledMagnitude x = sig * 2 ^ shift := by
    by_cases h0 : Wasm.IEEE64.exponent x = 0
    · simp [Wasm.IEEE64.scaledMagnitude, sig, shift, h0]
    · simp [Wasm.IEEE64.scaledMagnitude, sig, shift, h0]
  have hx : Wasm.IEEE64.scaledValue x = signedSig * 2 ^ shift := by
    simp only [Wasm.IEEE64.scaledValue, hmag, Int.natCast_mul, Int.natCast_pow,
      Nat.cast_ofNat]
    dsimp [signedSig]
    cases Wasm.IEEE64.sign x <;> simp
  let sumSig := signedSig + b * (2 : Int) ^ (1031 - shift)
  have hsum : Wasm.IEEE64.scaledValue x + Wasm.IEEE64.scaledValue y =
      sumSig * 2 ^ shift := by
    rw [hx, hy, show (2 : Int) ^ 1031 =
      2 ^ (1031 - shift) * 2 ^ shift by rw [← pow_add, Nat.sub_add_cancel hs]]
    dsimp [sumSig]
    ring
  have hd : 0 < (2 : ℝ) ^ 1074 := by positivity
  have hxm : |value x| = (Wasm.IEEE64.scaledMagnitude x : ℝ) / (2 : ℝ) ^ 1074 := by
    rw [value, abs_div, abs_of_pos hd, ← Int.cast_abs, Int.abs_eq_natAbs,
      natAbs_scaledValue]
    norm_num
  have hsumR : value x + value y =
      ((Wasm.IEEE64.scaledValue x + Wasm.IEEE64.scaledValue y : Int) : ℝ) /
        (2 : ℝ) ^ 1074 := by
    simp only [value, Int.cast_add, add_div]
  rw [hsumR, hxm, abs_div, abs_of_pos hd] at hr
  have hR : |((Wasm.IEEE64.scaledValue x + Wasm.IEEE64.scaledValue y : Int) : ℝ)| ≤
      (Wasm.IEEE64.scaledMagnitude x : ℝ) := by
    have h := (div_le_iff₀ hd).mp hr
    have hc : ((Wasm.IEEE64.scaledMagnitude x : ℝ) / (2 : ℝ) ^ 1074) *
        (2 : ℝ) ^ 1074 = (Wasm.IEEE64.scaledMagnitude x : ℝ) := by field_simp
    rw [hc] at h
    exact h
  rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] at hR
  have hN : (Wasm.IEEE64.scaledValue x + Wasm.IEEE64.scaledValue y).natAbs ≤
      Wasm.IEEE64.scaledMagnitude x := by exact_mod_cast hR
  have hsumAbs : (Wasm.IEEE64.scaledValue x + Wasm.IEEE64.scaledValue y).natAbs =
      sumSig.natAbs * 2 ^ shift := by
    rw [hsum, Int.natAbs_mul, Int.natAbs_pow]
    rfl
  rw [hsumAbs, hmag] at hN
  have hsumSig : sumSig.natAbs ≤ sig := by
    by_contra h
    have hg : sig < sumSig.natAbs := lt_of_not_ge h
    exact (not_lt_of_ge hN) (Nat.mul_lt_mul_of_pos_right hg (by positivity))
  have hp := LeanExe.ProofKit.F64GridExact.grid_add_exact x y hxf hyf sumSig shift hsum
    (hsumSig.trans hsig) (hs.trans (by norm_num))
  refine ⟨hp.1, ?_⟩
  rw [value, hp.2]
  simp only [Int.cast_add, value, add_div]

#print axioms add_high_grid_exact

theorem input_exponent_bound (x : UInt64) (hx : |value x| ≤ 768) :
    Wasm.IEEE64.exponent x ≤ 1032 := by
  by_contra hn
  have he : 1033 ≤ Wasm.IEEE64.exponent x := by omega
  have h0 : Wasm.IEEE64.exponent x ≠ 0 := by omega
  have hp : (2 : Nat) ^ 1032 ≤ 2 ^ (Wasm.IEEE64.exponent x - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hm : (2 : Nat) ^ 1084 ≤ Wasm.IEEE64.scaledMagnitude x := by
    simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, h0, ite_false]
    calc
      _ = (2 : Nat) ^ 52 * 2 ^ 1032 := by norm_num
      _ ≤ (2 ^ 52 + Wasm.IEEE64.fraction x) * 2 ^ (Wasm.IEEE64.exponent x - 1) :=
        Nat.mul_le_mul (by omega) hp
  have hr : (2 : ℝ) ^ 1084 ≤ (Wasm.IEEE64.scaledMagnitude x : ℝ) := by
    exact_mod_cast hm
  have hlarge : (1024 : ℝ) ≤ |value x| := by
    rw [LeanExe.ProofKit.F64NormalizedMagnitude.abs_value_scaledMagnitude]
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 1074)).mpr
    have hnum : (1024 : ℝ) * 2 ^ 1074 = 2 ^ 1084 := by norm_num
    rw [hnum]
    exact hr
  linarith only [hx, hlarge]

#print axioms input_exponent_bound

end Library.Numerics.Float64.Exp.ExpHighSubtraction
