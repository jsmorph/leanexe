import Project.ProofKit.F64NormalScale
import Project.ProofKit.F64OrderComplete

namespace Project.ProofKit.F64NormalScale
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem positive_normal_value (a : UInt64) (hs : Wasm.IEEE64.sign a = false)
    (he : 0 < Wasm.IEEE64.exponent a) :
    value a = ((2 : ℝ)^52 + Wasm.IEEE64.fraction a) *
      (2 : ℝ)^((Wasm.IEEE64.exponent a : Int)-1075) := by
  have hn : Wasm.IEEE64.exponent a ≠ 0 := by omega
  simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
    Wasm.IEEE64.scaledMagnitude, beq_iff_eq, ite_eq_right hn]
  push_cast
  have hpow : (2 : ℝ)^((Wasm.IEEE64.exponent a : Int)-1075) =
      (2 : ℝ)^(Wasm.IEEE64.exponent a-1)/2^1074 := by
    have hidx : (Wasm.IEEE64.exponent a : Int)-1075 =
        ((Wasm.IEEE64.exponent a-1 : Nat) : Int)-1074 := by omega
    rw [hidx, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    rfl
  rw [hpow]
  ring

theorem encoded_positive_value (e f : Nat) (he : 0 < e) (hu : e < 2047) (hf : f < 2^52) :
    value (Wasm.IEEE64.encodeFinite false e f) =
      ((2 : ℝ)^52+f)*(2 : ℝ)^((e : Int)-1075) := by
  rw [positive_normal_value _
    (sign_encodeFinite false e f (by omega) hf)
    (by rw [exponent_encodeFinite false e f (by omega) hf]; exact he),
    fraction_encodeFinite false e f (by omega) hf,
    exponent_encodeFinite false e f (by omega) hf]

theorem mul_power_value (a : UInt64) (ha : Finite a) (hs : Wasm.IEEE64.sign a = false)
    (he : 0 < Wasm.IEEE64.exponent a) (e : Nat) (hel : 0 < e) (heu : e < 2047)
    (hl : 1024 ≤ Wasm.IEEE64.exponent a+e) (hu : Wasm.IEEE64.exponent a+e < 3070) :
    let result := Wasm.IEEE64.mul a (Wasm.IEEE64.encodeFinite false e 0)
    Finite result ∧ value result = value a*(2 : ℝ)^((e : Int)-1023) := by
  rw [mul_power_word a ha he e hel heu hl, ite_eq_right (by omega), hs]
  have hf : Wasm.IEEE64.fraction a < 2^52 := Nat.mod_lt _ (by positivity)
  refine ⟨finite_encodeFinite false _ _ (by omega) hf, ?_⟩
  rw [encoded_positive_value _ _ (by omega) (by omega) hf, positive_normal_value a hs he,
    mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  apply congrArg (fun t : ℝ => ((2 : ℝ)^52+Wasm.IEEE64.fraction a)*t)
  apply congrArg (fun j : Int => (2 : ℝ)^j)
  omega

theorem mul_finite_comm (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.mul a b = Wasm.IEEE64.mul b a := by
  rw [mul_finite_rounder a b ha hb, mul_finite_rounder b a hb ha, Nat.mul_comm]
  cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl

theorem positive_sign (a : UInt64) (ha : Finite a) (hp : 0 < value a) :
    Wasm.IEEE64.sign a = false := by
  have h := F64Order.positiveBits_of_finite_value_pos a ha hp
  simp only [F64Order.positiveBits, Bool.and_eq_true_iff, decide_eq_true_eq,
    UInt64.lt_iff_toNat_lt] at h
  simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
  change ¬2^63 ≤ a.toNat
  change 0 < a.toNat ∧ a.toNat < 0x7FF0000000000000 at h
  omega

theorem normal_of_value (a : UInt64) (ha : Finite a)
    (hl : (2 : ℝ)^(-1022 : Int) ≤ value a) :
    Wasm.IEEE64.sign a = false ∧ 0 < Wasm.IEEE64.exponent a := by
  have hp : 0 < value a := (by positivity : (0 : ℝ) < 2^(-1022 : Int)).trans_le hl
  have hs := positive_sign a ha hp
  refine ⟨hs, ?_⟩
  by_contra hn
  have he : Wasm.IEEE64.exponent a = 0 := by omega
  have hf : (Wasm.IEEE64.fraction a : ℝ) < (2 : ℝ)^52 := by
    exact_mod_cast (Nat.mod_lt a.toNat (by positivity : 0 < 2^52))
  have hv : value a = (Wasm.IEEE64.fraction a : ℝ)/(2 : ℝ)^1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hs, Wasm.IEEE64.scaledMagnitude, he]
  rw [hv] at hl
  have hl' : (2 : ℝ)^52 ≤ Wasm.IEEE64.fraction a := by
    calc
      _ = (2 : ℝ)^(-1022 : Int)*(2 : ℝ)^1074 := by norm_num
      _ ≤ _ := (le_div_iff₀ (by positivity)).mp hl
  linarith only [hl', hf]

theorem positive_binade (a : UInt64) (hs : Wasm.IEEE64.sign a = false)
    (he : 0 < Wasm.IEEE64.exponent a) :
    (2 : ℝ)^((Wasm.IEEE64.exponent a : Int)-1023) ≤ value a ∧
      value a < (2 : ℝ)^((Wasm.IEEE64.exponent a : Int)-1022) := by
  have hf : (Wasm.IEEE64.fraction a : ℝ) < (2 : ℝ)^52 := by
    exact_mod_cast (Nat.mod_lt a.toNat (by positivity : 0 < 2^52))
  have hp : 0 < (2 : ℝ)^((Wasm.IEEE64.exponent a : Int)-1075) := by positivity
  have hlo : (2 : ℝ)^((Wasm.IEEE64.exponent a : Int)-1023) =
      (2 : ℝ)^52 * (2 : ℝ)^((Wasm.IEEE64.exponent a : Int)-1075) := by
    rw [← zpow_natCast,
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  have hhi : (2 : ℝ)^((Wasm.IEEE64.exponent a : Int)-1022) =
      (2 : ℝ)^53 * (2 : ℝ)^((Wasm.IEEE64.exponent a : Int)-1075) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [positive_normal_value a hs he, hlo, hhi]
  constructor
  · nlinarith [Nat.cast_nonneg (α := ℝ) (Wasm.IEEE64.fraction a)]
  · nlinarith

#print axioms mul_power_value
#print axioms normal_of_value
#print axioms positive_binade
end Project.ProofKit.F64NormalScale
