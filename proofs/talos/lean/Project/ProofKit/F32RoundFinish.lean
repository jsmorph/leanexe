import Project.ProofKit.F32Normalize

namespace Project.ProofKit.F32RoundFinish
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing F32Rounding F32RoundScaled

def finish (s : Sign) (m : Nat) (e : Int) : UnpackedFloat :=
  let final := shiftToTargetExponent Format.binary32 m e .exact
  if h : final.1.mantissa = 0 then .zero s
  else .finite s final.1.mantissa final.2 (Nat.pos_of_ne_zero h)

theorem roundWithAccuracy_finish (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) :
    roundWithAccuracy Format.binary32 s m e acc =
      let first := shiftToTargetExponent Format.binary32 m e acc
      finish s first.1.roundedMantissa first.2 := rfl

theorem finish_no_shift (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (ht : Format.binary32.targetExponent (totalExponent m e) = e) :
    finish s m e = .finite s m e hm := by
  simp only [finish, shift_target m e .exact 0 (by simpa using ht)]
  simp [shift_zero, ExtendedMantissa.ofMantissaAndAccuracy, Nat.ne_of_gt hm]

theorem finish_carry (s : Sign) (e : Int) (he : -149 ≤ e) :
    finish s (2 ^ 24) e = .finite s (2 ^ 23) (e + 1) (by decide) := by
  have ht : Format.binary32.targetExponent (totalExponent (2 ^ 24) e) = e + (1 : Nat) := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent, Nat.log2_two_pow]
    omega
  simp only [finish, shift_target (2 ^ 24) e .exact 1 ht]
  rfl

theorem pack_finish_scaled (s : Sign) (m : Nat) (hm : m ≤ 2 ^ 24) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (finish s m (-149))) =
      Wasm.IEEE32.roundScaledMagnitude (negative s) m := by
  by_cases hc : m = 2 ^ 24
  · subst m
    rw [finish_carry s (-149) (by omega)]
    cases s <;> rfl
  · have hl : m.log2 < 24 := by
      by_cases hz : m = 0
      · subst m; decide
      · exact (Nat.log2_lt hz).mpr (by omega)
    have ht : Format.binary32.targetExponent (totalExponent m (-149)) = (-149 : Int) + (0 : Nat) := by
      rw [target_scaled]
      omega
    have h := pack_roundWithAccuracy_scaled s m
    rw [roundWithAccuracy_finish, shift_target m (-149) .exact 0 ht] at h
    exact h

theorem pack_finish_normal (s : Sign) (m : Nat) (k : Nat)
    (hlo : 2 ^ 23 ≤ m) (hhi : m ≤ 2 ^ 24) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (finish s m ((k : Int) - 149))) =
      if m = 2 ^ 24 then
        if 255 ≤ k + 2 then Wasm.IEEE32.infinity (negative s)
        else Wasm.IEEE32.encodeFinite (negative s) (k + 2) 0
      else if 255 ≤ k + 1 then Wasm.IEEE32.infinity (negative s)
        else Wasm.IEEE32.encodeFinite (negative s) (k + 1) (m - 2 ^ 23) := by
  by_cases hc : m = 2 ^ 24
  · subst m
    rw [finish_carry s _ (by omega), pack_finite]
    have he : ((k : Int) - 149 + 1 + 150).toNat = k + 2 := by omega
    simp [he, show Nat.log2 8388608 = 23 from rfl]
  · have hm : 0 < m := by omega
    have hl : m.log2 = 23 := (Nat.log2_eq_iff (Nat.ne_of_gt hm)).mpr ⟨hlo, by omega⟩
    have ht : Format.binary32.targetExponent (totalExponent m ((k : Int) - 149)) = (k : Int) - 149 := by
      simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
        Format.minExponent, hl]
      omega
    rw [finish_no_shift s m _ hm ht, pack_finite]
    have he : ((k : Int) - 149 + 150).toNat = k + 1 := by omega
    have hf : m % 8388608 = m - 8388608 := by omega
    norm_num only [Nat.reducePow] at hc
    simp [hc, hl, he, hf]

#print axioms pack_finish_scaled
#print axioms pack_finish_normal

end Project.ProofKit.F32RoundFinish
