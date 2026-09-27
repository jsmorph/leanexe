import Project.ProofKit.F64ExactArithmetic

namespace Project.ProofKit.F64NormalScale
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem pack_normal (negative : Bool) (n k : Nat) (hl : 2^52 ≤ n) (hu : n < 2^53) :
    Wasm.IEEE64.roundScaledMagnitude negative (n*2^k) =
      if 2047 ≤ k+1 then Wasm.IEEE64.infinity negative
      else Wasm.IEEE64.encodeFinite negative (k+1) (n-2^52) := by
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero, Nat.mul_one, Wasm.IEEE64.roundScaledMagnitude,
      hu, show ¬n < 2^52 by omega, ite_false, ite_true,
      Nat.zero_add, show ¬2047 ≤ 1 by decide]
  have hn : n ≠ 0 := by omega
  have hlog : Nat.log2 n = 52 := (Nat.log2_eq_iff hn).mpr ⟨hl, hu⟩
  have hshift : Nat.log2 (n*2^k)-52 = k := by
    rw [F64DyadicBounds.log2_mul_two_pow _ _ hn, hlog]
    omega
  have hmin : 2^53 ≤ n*2^k := by
    calc
      _ = 2^52 * 2^1 := by norm_num
      _ ≤ n*2^k := Nat.mul_le_mul hl (Nat.pow_le_pow_right (by decide) (by omega))
  have hr : Wasm.IEEE32.roundShift (n*2^k) k = n :=
    F64DyadicBounds.roundShift_mul_two_pow n k (by omega)
  simp only [Wasm.IEEE64.roundScaledMagnitude,
    show ¬n*2^k < 2^52 by omega, show ¬n*2^k < 2^53 by omega,
    ite_false, hshift, hr, beq_iff_eq, show n ≠ 2^53 by omega, ite_false]

theorem mul_power_word (a : UInt64) (ha : Finite a) (he : 0 < Wasm.IEEE64.exponent a)
    (e : Nat) (hel : 0 < e) (heu : e < 2047) (hl : 1024 ≤ Wasm.IEEE64.exponent a + e) :
    Wasm.IEEE64.mul a (Wasm.IEEE64.encodeFinite false e 0) =
      if 3070 ≤ Wasm.IEEE64.exponent a + e then Wasm.IEEE64.infinity (Wasm.IEEE64.sign a)
      else Wasm.IEEE64.encodeFinite (Wasm.IEEE64.sign a)
        (Wasm.IEEE64.exponent a+e-1023) (Wasm.IEEE64.fraction a) := by
  let n := 2^52 + Wasm.IEEE64.fraction a
  let k := Wasm.IEEE64.exponent a+e-1024
  have hf : Wasm.IEEE64.fraction a < 2^52 := Nat.mod_lt _ (by positivity)
  have hn : 2^52 ≤ n ∧ n < 2^53 := by dsimp [n]; omega
  have hb := finite_encodeFinite false e 0 heu (by norm_num)
  have hs := sign_encodeFinite false e 0 (by omega) (by norm_num)
  have hm := scaledMagnitude_encodeFinite false e 0 (by omega) (by norm_num)
  have hp : Wasm.IEEE64.scaledMagnitude a *
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.encodeFinite false e 0) = n*2^(1074+k) := by
    rw [hm]
    simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq,
      show Wasm.IEEE64.exponent a ≠ 0 by omega, show e ≠ 0 by omega, ite_false, Nat.add_zero]
    change (n*2^(Wasm.IEEE64.exponent a-1))*(2^52*2^(e-1)) = _
    calc
      _ = n * (2^(Wasm.IEEE64.exponent a-1) * 2^52 * 2^(e-1)) := by ring
      _ = n * 2^((Wasm.IEEE64.exponent a-1)+52+(e-1)) := by rw [pow_add, pow_add]
      _ = _ := ?_
    apply congrArg (fun j => n*2^j)
    dsimp [k]
    omega
  rw [mul_finite_rounder a _ ha hb, hs, Bool.bne_false, hp,
    F64ExactArithmetic.dyadic_mul_power _ n 1074 k hn.2, pack_normal _ n k hn.1 hn.2]
  have heq : k+1 = Wasm.IEEE64.exponent a+e-1023 := by dsimp [k]; omega
  have hnq : n-2^52 = Wasm.IEEE64.fraction a := by dsimp [n]; omega
  rw [heq, hnq]
  have hiff : 2047 ≤ Wasm.IEEE64.exponent a+e-1023 ↔
      3070 ≤ Wasm.IEEE64.exponent a+e := by omega
  simp only [hiff]

#print axioms mul_power_word
end Project.ProofKit.F64NormalScale
