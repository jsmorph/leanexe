import LeanExe.ProofKit.F64DyadicBounds

/-!
The bits of a nonnegative word from its scaled value.  A word with a clear sign bit whose scaled
value is `R · 2 ^ g`, with `2 ^ 52 ≤ R < 2 ^ 53`, has exponent field `g + 1` and fraction
`R - 2 ^ 52`, so its bits are `(g + 1) · 2 ^ 52 + (R - 2 ^ 52)`.
-/

namespace LeanExe.ProofKit.F64BinadeWord

theorem binade_word_toNat (w : UInt64) (R g : Nat)
    (hs : Wasm.IEEE64.sign w = false)
    (hv : Wasm.IEEE64.scaledValue w = (R : Int) * 2 ^ g)
    (hRl : 2 ^ 52 ≤ R) (hRu : R < 2 ^ 53) :
    w.toNat = (g + 1) * 2 ^ 52 + (R - 2 ^ 52) := by
  have hR0 : R ≠ 0 := by omega
  have hmagI : (Wasm.IEEE64.scaledMagnitude w : Int) = (R : Int) * 2 ^ g := by
    simpa only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false] using hv
  have hm : Wasm.IEEE64.scaledMagnitude w = R * 2 ^ g := by exact_mod_cast hmagI
  have hRlog : Nat.log2 R = 52 := (Nat.log2_eq_iff hR0).mpr ⟨hRl, hRu⟩
  have hmlog : Nat.log2 (Wasm.IEEE64.scaledMagnitude w) = 52 + g := by
    rw [hm, F64DyadicBounds.log2_mul_two_pow R g hR0, hRlog]
  have hf : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have h0 : Wasm.IEEE64.exponent w ≠ 0 := by
    intro he
    have hmf : Wasm.IEEE64.scaledMagnitude w = Wasm.IEEE64.fraction w := by
      simp [Wasm.IEEE64.scaledMagnitude, he]
    have hm0 : Wasm.IEEE64.scaledMagnitude w ≠ 0 := by
      rw [hm]
      exact Nat.mul_ne_zero hR0 (by positivity)
    have hflog : Nat.log2 (Wasm.IEEE64.fraction w) < 52 :=
      (Nat.log2_lt (by rwa [← hmf])).mpr hf
    rw [hmf] at hmlog
    omega
  have hsig : 2 ^ 52 + Wasm.IEEE64.fraction w ≠ 0 := by positivity
  have hsiglog : Nat.log2 (2 ^ 52 + Wasm.IEEE64.fraction w) = 52 :=
    (Nat.log2_eq_iff hsig).mpr ⟨by omega, by omega⟩
  have hmlog' : Nat.log2 (Wasm.IEEE64.scaledMagnitude w) =
      52 + (Wasm.IEEE64.exponent w - 1) := by
    simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, h0, ite_false]
    rw [F64DyadicBounds.log2_mul_two_pow _ _ hsig, hsiglog]
  have he : Wasm.IEEE64.exponent w = g + 1 := by omega
  have hmag' : Wasm.IEEE64.scaledMagnitude w =
      (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ g := by
    simp [Wasm.IEEE64.scaledMagnitude, he]
  rw [hmag'] at hm
  have hfrac : Wasm.IEEE64.fraction w = R - 2 ^ 52 := by
    have hsum := (Nat.mul_left_inj (by positivity : (2 : Nat) ^ g ≠ 0)).mp hm
    omega
  have hsn : w.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have he' : w.toNat / 2 ^ 52 % 2 ^ 11 = g + 1 := he
  have hf' : w.toNat % 2 ^ 52 = R - 2 ^ 52 := hfrac
  omega

#print axioms binade_word_toNat

end LeanExe.ProofKit.F64BinadeWord
