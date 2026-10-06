import LeanExe.ProofKit.F32Convert
import LeanExe.ProofKit.F32Bits

namespace LeanExe.ProofKit.F32Nearest

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

theorem isNaN_encodeFinite (negative : Bool) (e f : Nat) (he : e < 255) (hf : f < 2 ^ 23) :
    Wasm.IEEE32.isNaN (Wasm.IEEE32.encodeFinite negative e f) = false := by
  have hlt : (if negative then 2 ^ 31 else 0) + e * 2 ^ 23 + f < 2 ^ 32 := by
    split <;> omega
  simp only [Wasm.IEEE32.isNaN, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction,
    Wasm.IEEE32.encodeFinite, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] <;> omega

/-- Rounding a scaled magnitude gives a finite value or an infinity, never a NaN. -/
theorem isNaN_roundScaledMagnitude (negative : Bool) (n : Nat) :
    Wasm.IEEE32.isNaN (Wasm.IEEE32.roundScaledMagnitude negative n) = false := by
  unfold Wasm.IEEE32.roundScaledMagnitude
  split
  · exact isNaN_encodeFinite negative 0 n (by omega) (by omega)
  split
  · exact isNaN_encodeFinite negative 1 (n - 2 ^ 23) (by omega) (by omega)
  rename_i h1 h2
  have hn : n ≠ 0 := by omega
  have hlow := Nat.log2_self_le hn
  have hhigh := Nat.lt_log2_self (n := n)
  have hlog : 24 ≤ n.log2 := by
    by_contra h
    have : n.log2 + 1 ≤ 24 := by omega
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) this
    omega
  have hsplit : 2 ^ n.log2 = 2 ^ 23 * 2 ^ (n.log2 - 23) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hsplit' : 2 ^ (n.log2 + 1) = 2 ^ 24 * 2 ^ (n.log2 - 23) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hq1 : 2 ^ 23 ≤ n / 2 ^ (n.log2 - 23) :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by rw [← hsplit]; exact hlow)
  have hq2 : n / 2 ^ (n.log2 - 23) < 2 ^ 24 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [← hsplit']; exact hhigh)
  have hr := CodeLib.IEEE32.roundShift_bounds n (n.log2 - 23)
  dsimp only
  generalize Wasm.IEEE32.roundShift n (n.log2 - 23) = R at hr ⊢
  by_cases hR : R = 2 ^ 24
  · have hR' : (R == 2 ^ 24) = true := by simp [hR]
    simp only [hR', ↓reduceIte]
    by_cases hx : 255 ≤ n.log2 - 23 + 1 + 1
    · simp only [hx, ↓reduceIte]
      exact CodeLib.IEEE32.infinity_not_nan negative
    · simp only [hx, ↓reduceIte]
      exact isNaN_encodeFinite negative _ _ (by omega) (by simp)
  · have hR' : (R == 2 ^ 24) = false := by simpa using hR
    simp only [hR', Bool.false_eq_true, ↓reduceIte]
    by_cases hx : 255 ≤ n.log2 - 23 + 1
    · simp only [hx, ↓reduceIte]
      exact CodeLib.IEEE32.infinity_not_nan negative
    · simp only [hx, ↓reduceIte]
      exact isNaN_encodeFinite negative _ _ (by omega) (by omega)

/-- The only NaN that `nearest` returns is the canonical NaN. -/
theorem nearest_nan (value : UInt32) (h : Wasm.IEEE32.isNaN (Wasm.IEEE32.nearest value) = true) :
    Wasm.IEEE32.nearest value = Wasm.IEEE32.canonicalNaN := by
  unfold Wasm.IEEE32.nearest Wasm.IEEE32.roundIntegral at *
  split
  · rfl
  · rename_i hnan
    split at h
    · contradiction
    split at h
    · exact absurd h hnan
    split at h
    · exact absurd h hnan
    · unfold Wasm.IEEE32.roundIntegralFinite at h
      rw [isNaN_roundScaledMagnitude] at h
      contradiction

theorem toBits_nearest (x : Float32) :
    (LeanExe.Float32.nearest x).toBits = Wasm.IEEE32.nearest x.toBits := by
  unfold LeanExe.Float32.nearest
  rw [F32Bits.toBits_ofBits, nearest_eq]
  split
  · rename_i h; exact (nearest_nan _ h).symm
  · rfl

end LeanExe.ProofKit.F32Nearest

