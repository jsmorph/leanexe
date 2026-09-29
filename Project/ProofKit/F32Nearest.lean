import Project.ProofKit.F32Convert

namespace Project.ProofKit.F32Nearest

theorem signed_integral (value : UInt32) (n : Nat) :
    (if n == 0 then (if value < 0x80000000 then (0 : UInt32) else 0x80000000)
     else (Float32.Model.ofInt (if value < 0x80000000 then (n : Int) else -(n : Int))).toBits) =
      Wasm.IEEE32.roundScaledMagnitude (Wasm.IEEE32.sign value) (n * 2 ^ 149) := by
  by_cases hs : value < 0x80000000
  · have hsign : Wasm.IEEE32.sign value = false := by
      simp only [Wasm.IEEE32.sign, decide_eq_false_iff_not]
      have h : value.toNat < 2147483648 := hs
      omega
    by_cases hn : n = 0
    · subst n
      simp only [hs, hsign, ↓reduceIte]
      decide
    · have hp : ¬(n : Int) < 0 := by omega
      simp [hs, hn, hsign, F32Convert.ofInt_eq, Wasm.IEEE32.fromInt, hp]
  · have hsign : Wasm.IEEE32.sign value = true := by
      simp only [Wasm.IEEE32.sign, decide_eq_true_eq]
      have h : ¬value.toNat < 2147483648 := hs
      omega
    by_cases hn : n = 0
    · subst n
      simp only [hs, hsign, ↓reduceIte]
      decide
    · have hp : 0 < n := Nat.pos_of_ne_zero hn
      simp [hs, hn, hsign, F32Convert.ofInt_eq, Wasm.IEEE32.fromInt, hp]

theorem zero_encoding (value : UInt32) (hz : Wasm.IEEE32.scaledMagnitude value = 0) :
    value = Wasm.IEEE32.signMask (Wasm.IEEE32.sign value) := by
  have he : Wasm.IEEE32.exponent value = 0 := by
    by_contra he
    have hp : 0 < (2 ^ 23 + Wasm.IEEE32.fraction value) * 2 ^ (Wasm.IEEE32.exponent value - 1) :=
      Nat.mul_pos (by omega) (by positivity)
    simp [Wasm.IEEE32.scaledMagnitude, he] at hz
  have hf : Wasm.IEEE32.fraction value = 0 := by
    simpa [Wasm.IEEE32.scaledMagnitude, he] using hz
  calc
    value = Wasm.IEEE32.encodeFinite (Wasm.IEEE32.sign value)
        (Wasm.IEEE32.exponent value) (Wasm.IEEE32.fraction value) := (F32Packing.encode_fields value).symm
    _ = Wasm.IEEE32.signMask (Wasm.IEEE32.sign value) := by
      rw [he, hf, ← F32Packing.signMask_eq_encode]

theorem nearestBits_finite (value : UInt32) (he : Wasm.IEEE32.exponent value ≠ 255) :
    LeanExe.Float32.nearestBits value =
      Wasm.IEEE32.roundScaledMagnitude (Wasm.IEEE32.sign value)
        (Wasm.IEEE32.roundShift (Wasm.IEEE32.scaledMagnitude value) 149 * 2 ^ 149) := by
  have hs := signed_integral value (Wasm.IEEE32.roundShift (Wasm.IEEE32.scaledMagnitude value) 149)
  have he' : value.toNat / 2 ^ 23 % 256 ≠ 255 := he
  simpa only [LeanExe.Float32.nearestBits, Wasm.IEEE32.roundShift,
    Wasm.IEEE32.scaledMagnitude, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction,
    show 2 ^ 8 = (256 : Nat) by decide, he', beq_eq_false_iff_ne.mpr he', Bool.false_eq_true,
    ite_false] using hs

theorem nearest_eq (value : UInt32) :
    LeanExe.Float32.nearestBits value = Wasm.IEEE32.nearest value := by
  by_cases he : Wasm.IEEE32.exponent value = 255
  · by_cases hf : Wasm.IEEE32.fraction value = 0
    · simp [LeanExe.Float32.nearestBits, Wasm.IEEE32.nearest, Wasm.IEEE32.roundIntegral,
        Wasm.IEEE32.isNaN, Wasm.IEEE32.isInfinite, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction] at he hf ⊢
      simp [he, hf]
    · simp [LeanExe.Float32.nearestBits, Wasm.IEEE32.nearest, Wasm.IEEE32.roundIntegral,
        Wasm.IEEE32.isNaN, Wasm.IEEE32.isInfinite, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction] at he hf ⊢
      simp [he, hf, Wasm.IEEE32.canonicalNaN]
  · rw [nearestBits_finite value he]
    simp only [Wasm.IEEE32.nearest, Wasm.IEEE32.roundIntegral,
      Wasm.IEEE32.isNaN, Wasm.IEEE32.isInfinite, beq_eq_false_iff_ne.mpr he,
      Bool.false_and, Bool.false_eq_true, ite_false]
    by_cases hz : Wasm.IEEE32.scaledMagnitude value = 0
    · rw [hz, zero_encoding value hz]
      cases Wasm.IEEE32.sign value <;> decide
    · simp only [beq_eq_false_iff_ne.mpr hz, Bool.false_eq_true, ite_false,
        Wasm.IEEE32.roundIntegralFinite]

#print axioms nearest_eq

end Project.ProofKit.F32Nearest
