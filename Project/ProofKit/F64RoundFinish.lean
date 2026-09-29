import Project.ProofKit.F64Normalize

namespace Project.ProofKit.F64RoundFinish
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Packing FloatRounding F64RoundScaled FloatCommon

def finish (s : Sign) (m : Nat) (e : Int) : UnpackedFloat :=
  let final := shiftToTargetExponent Format.binary64 m e .exact
  if h : final.1.mantissa = 0 then .zero s
  else .finite s final.1.mantissa final.2 (Nat.pos_of_ne_zero h)

theorem roundWithAccuracy_finish (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) :
    roundWithAccuracy Format.binary64 s m e acc =
      let first := shiftToTargetExponent Format.binary64 m e acc
      finish s first.1.roundedMantissa first.2 := rfl

theorem finish_no_shift (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (ht : Format.binary64.targetExponent (totalExponent m e) = e) :
    finish s m e = .finite s m e hm := by
  simp only [finish, shift_target m e .exact 0 (by simpa using ht)]
  simp [shift_zero, ExtendedMantissa.ofMantissaAndAccuracy, Nat.ne_of_gt hm]

theorem finish_carry (s : Sign) (e : Int) (he : -1074 ≤ e) :
    finish s (2 ^ 53) e = .finite s (2 ^ 52) (e + 1) (by decide) := by
  have ht : Format.binary64.targetExponent (totalExponent (2 ^ 53) e) = e + (1 : Nat) := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, Nat.log2_two_pow]
    omega
  simp only [finish, shift_target (2 ^ 53) e .exact 1 ht]
  rfl

theorem pack_finish_scaled (s : Sign) (m : Nat) (hm : m ≤ 2 ^ 53) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (finish s m (-1074))) =
      Wasm.IEEE64.roundScaledMagnitude (negative s) m := by
  by_cases hc : m = 2 ^ 53
  · subst m
    rw [finish_carry s (-1074) (by omega)]
    cases s <;> rfl
  · have hl : m.log2 < 53 := by
      by_cases hz : m = 0
      · subst m; decide
      · exact (Nat.log2_lt hz).mpr (by omega)
    have ht : Format.binary64.targetExponent (totalExponent m (-1074)) = (-1074 : Int) + (0 : Nat) := by
      rw [target_scaled]
      omega
    have h := pack_roundWithAccuracy_scaled s m
    rw [roundWithAccuracy_finish, shift_target m (-1074) .exact 0 ht] at h
    exact h

theorem pack_finish_normal (s : Sign) (m : Nat) (k : Nat)
    (hlo : 2 ^ 52 ≤ m) (hhi : m ≤ 2 ^ 53) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (finish s m ((k : Int) - 1074))) =
      if m = 2 ^ 53 then
        if 2047 ≤ k + 2 then Wasm.IEEE64.infinity (negative s)
        else Wasm.IEEE64.encodeFinite (negative s) (k + 2) 0
      else if 2047 ≤ k + 1 then Wasm.IEEE64.infinity (negative s)
        else Wasm.IEEE64.encodeFinite (negative s) (k + 1) (m - 2 ^ 52) := by
  by_cases hc : m = 2 ^ 53
  · subst m
    rw [finish_carry s _ (by omega), pack_finite]
    have he : ((k : Int) - 1074 + 1 + 1075).toNat = k + 2 := by omega
    simp [he, show Nat.log2 4503599627370496 = 52 from rfl]
  · have hm : 0 < m := by omega
    have hl : m.log2 = 52 := (Nat.log2_eq_iff (Nat.ne_of_gt hm)).mpr ⟨hlo, by omega⟩
    have ht : Format.binary64.targetExponent (totalExponent m ((k : Int) - 1074)) = (k : Int) - 1074 := by
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
        Format.minExponent, hl]
      omega
    rw [finish_no_shift s m _ hm ht, pack_finite]
    have he : ((k : Int) - 1074 + 1075).toNat = k + 1 := by omega
    have hf : m % 4503599627370496 = m - 4503599627370496 := by omega
    norm_num only [Nat.reducePow] at hc
    simp [hc, hl, he, hf]

#print axioms pack_finish_scaled
#print axioms pack_finish_normal

theorem finish_eq_round (s : Sign) (m : Nat) (e : Int)
    (hlo : 2 ^ 52 ≤ m) (hhi : m ≤ 2 ^ 53) (he : -1074 ≤ e) :
    finish s m e = UnpackedFloat.round Format.binary64 s m e := by
  have hm : 0 < m := by omega
  by_cases hc : m = 2 ^ 53
  · subst m
    have ht : Format.binary64.targetExponent (totalExponent (2 ^ 53) e) = e + 1 := by
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
        Format.minExponent, Nat.log2_two_pow]
      omega
    have hz : (e - (e + 1)).toNat = 0 := by omega
    simp only [UnpackedFloat.round, ht, decreaseExponent, hz, Nat.shiftLeft_zero,
      Nat.cast_zero, sub_zero, roundWithAccuracy_finish]
    rw [shift_target _ e .exact 1 (by simpa using ht)]
    have hr : (ExtendedMantissa.ofMantissaAndAccuracy (2 ^ 53) .exact >>> 1).roundedMantissa =
        2 ^ 52 := by
      rw [show (2 ^ 53 : Nat) = 2 ^ 52 * 2 ^ 1 by norm_num, FloatShift.shift_exact_mul_pow]
      rfl
    dsimp only
    rw [hr]
    simp only [Nat.cast_one]
    rw [finish_carry s e he, finish_no_shift s (2 ^ 52) (e + 1) (by decide)]
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, Nat.log2_two_pow]
    omega
  · have hl : m.log2 = 52 := (Nat.log2_eq_iff (Nat.ne_of_gt hm)).mpr ⟨hlo, by omega⟩
    have ht : Format.binary64.targetExponent (totalExponent m e) = e := by
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
        Format.minExponent, hl]
      omega
    simp only [UnpackedFloat.round, ht, decreaseExponent, sub_self, Int.toNat_zero,
      Nat.shiftLeft_zero, Nat.cast_zero, sub_zero, roundWithAccuracy_finish]
    rw [shift_target _ e .exact 0 (by simpa using ht)]
    simp [shift_zero, roundedMantissa_eq, ExtendedMantissa.ofMantissaAndAccuracy]

theorem pack_finish_above_min (s : Sign) (m : Nat) (e : Int)
    (hlo : 2 ^ 52 ≤ m) (hhi : m ≤ 2 ^ 53) (he : -1074 ≤ e) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (finish s m e)) =
      Wasm.IEEE64.roundScaledMagnitude (negative s) (m * 2 ^ (e + 1074).toNat) := by
  rw [finish_eq_round s m e hlo hhi he,
    F64Normalize.pack_round_above_min s m e (by omega) he]

#print axioms pack_finish_above_min

end Project.ProofKit.F64RoundFinish
