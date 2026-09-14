import Project.ProofKit.F64Packing

namespace Project.ProofKit.F64Packing
open CodeLib.IEEE64
set_option exponentiation.threshold 4096

theorem significand_bounds (n : Nat) (hn : 2^53 ≤ n) :
    let shift := Nat.log2 n-52
    0 < shift ∧ 2^52 ≤ Wasm.IEEE32.roundShift n shift ∧
      Wasm.IEEE32.roundShift n shift ≤ 2^53 := by
  have hnz : n ≠ 0 := by omega
  have hl : 53 ≤ Nat.log2 n := (Nat.le_log2 hnz).mpr hn
  let shift := Nat.log2 n-52
  have hlow : 2^52*2^shift ≤ n := by
    rw [← pow_add, show 52+shift = Nat.log2 n by dsimp [shift]; omega]
    exact Nat.log2_self_le hnz
  have hhigh : n < 2^53*2^shift := by
    rw [← pow_add, show 53+shift = Nat.log2 n+1 by dsimp [shift]; omega]
    exact Nat.lt_log2_self
  have hql : 2^52 ≤ n/2^shift := (Nat.le_div_iff_mul_le (by positivity)).mpr hlow
  have hqh : n/2^shift < 2^53 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr hhigh
  have hr := CodeLib.IEEE32.roundShift_bounds n shift
  change 0 < shift ∧ _ ∧ _
  dsimp only [shift] at *
  omega

theorem infinity_not_finite (negative : Bool) : ¬Finite (Wasm.IEEE64.infinity negative) := by
  cases negative <;> unfold CodeLib.IEEE64.Finite <;> decide +kernel

theorem pack_finite_spec (negative : Bool) (n : Nat)
    (hf : Finite (Wasm.IEEE64.roundScaledMagnitude negative n)) :
    Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundScaledMagnitude negative n) =
      roundedMagnitude n ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundScaledMagnitude negative n) = negative := by
  by_cases hsmall : n < 2^2097
  · exact (pack_spec negative n hsmall).2
  have hn : 2^53 ≤ n := by omega
  have hsub : ¬n < 4503599627370496 := by omega
  have hexact : ¬n < 9007199254740992 := by omega
  let shift := Nat.log2 n-52
  let rounded := Wasm.IEEE32.roundShift n shift
  obtain ⟨hshift, hlo, hhi⟩ := significand_bounds n hn
  change 0 < shift at hshift
  change 2^52 ≤ rounded at hlo
  change rounded ≤ 2^53 at hhi
  by_cases hc : rounded = 2^53
  · have hcn : Wasm.IEEE32.roundShift n (Nat.log2 n-52) = 9007199254740992 := hc
    have heq : Wasm.IEEE64.roundScaledMagnitude negative n =
        if 2047 ≤ shift+2 then Wasm.IEEE64.infinity negative
        else Wasm.IEEE64.encodeFinite negative (shift+2) 0 := by
      simp [Wasm.IEEE64.roundScaledMagnitude, hsub, hexact, hcn, shift, Nat.add_assoc]
    have he : ¬2047 ≤ shift+2 := by
      intro he
      rw [heq, ite_eq_left he] at hf
      exact infinity_not_finite negative hf
    rw [heq, ite_eq_right he]
    have hm := scaledMagnitude_encodeFinite negative (shift+2) 0 (by omega) (by norm_num)
    have hs := sign_encodeFinite negative (shift+2) 0 (by omega) (by norm_num)
    refine ⟨?_, hs⟩
    rw [hm]
    simp only [show shift+2 ≠ 0 by omega, ite_false, Nat.add_zero,
      show shift+2-1 = shift+1 by omega]
    simp [roundedMagnitude, hexact, hcn, shift]
  · have hcn : ¬Wasm.IEEE32.roundShift n (Nat.log2 n-52) = 9007199254740992 := hc
    have heq : Wasm.IEEE64.roundScaledMagnitude negative n =
        if 2047 ≤ shift+1 then Wasm.IEEE64.infinity negative
        else Wasm.IEEE64.encodeFinite negative (shift+1) (rounded-2^52) := by
      simp [Wasm.IEEE64.roundScaledMagnitude, hsub, hexact, hcn, shift, rounded]
    have he : ¬2047 ≤ shift+1 := by
      intro he
      rw [heq, ite_eq_left he] at hf
      exact infinity_not_finite negative hf
    have hfrac : rounded-2^52 < 2^52 := by omega
    rw [heq, ite_eq_right he]
    have hm := scaledMagnitude_encodeFinite negative (shift+1) (rounded-2^52)
      (by omega) hfrac
    have hs := sign_encodeFinite negative (shift+1) (rounded-2^52) (by omega) hfrac
    refine ⟨?_, hs⟩
    rw [hm]
    simp only [show shift+1 ≠ 0 by omega, ite_false,
      show shift+1-1 = shift by omega, show 2^52+(rounded-2^52) = rounded by omega]
    simp [roundedMagnitude, hexact, hcn, shift, rounded]

theorem pack_scaledValue_finite (negative : Bool) (n : Nat)
    (hf : Finite (Wasm.IEEE64.roundScaledMagnitude negative n)) :
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude negative n) =
      if negative then -(roundedMagnitude n : Int) else roundedMagnitude n := by
  have hs := pack_finite_spec negative n hf
  simp only [Wasm.IEEE64.scaledValue, hs.1, hs.2]

#print axioms significand_bounds
#print axioms pack_finite_spec
#print axioms pack_scaledValue_finite
end Project.ProofKit.F64Packing
