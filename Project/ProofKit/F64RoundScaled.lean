import Project.ProofKit.F64Packing
import Project.ProofKit.FloatRounding

namespace Project.ProofKit.F64RoundScaled
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Packing FloatRounding FloatCommon

theorem target_scaled (m : Nat) :
    Format.binary64.targetExponent (totalExponent m (-1074)) =
      (m.log2 - 52 : Nat) - (1074 : Int) := by
  simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
    Format.minExponent]
  omega

theorem shift_target (m : Nat) (e : Int) (acc : Accuracy) (k : Nat)
    (ht : Format.binary64.targetExponent (totalExponent m e) = e + k) :
    shiftToTargetExponent Format.binary64 m e acc =
      (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> k, e + k) := by
  simp [shiftToTargetExponent, ht, shiftToExponent]

theorem roundWithAccuracy_eq (s : Sign) (m : Nat) (e : Int) (acc : Accuracy)
    (k r j : Nat)
    (ht : Format.binary64.targetExponent (totalExponent m e) = e + k)
    (hr : (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> k).roundedMantissa = r)
    (ht' : Format.binary64.targetExponent (totalExponent r (e + k)) = e + k + j)
    (hpos : 0 < r / 2 ^ j) :
    roundWithAccuracy Format.binary64 s m e acc =
      .finite s (r / 2 ^ j) (e + k + j) hpos := by
  unfold roundWithAccuracy
  rw [shift_target m e acc k ht]
  dsimp only
  rw [hr, shift_target r (e + k) .exact j ht']
  dsimp only
  rw [shift_mantissa]
  simp [ExtendedMantissa.ofMantissaAndAccuracy, Nat.ne_of_gt hpos]

theorem roundWithAccuracy_small (s : Sign) (m : Nat) (hm : 0 < m) (hb : m < 2 ^ 53) :
    roundWithAccuracy Format.binary64 s m (-1074) .exact = .finite s m (-1074) hm := by
  have hl := (Nat.log2_lt (Nat.ne_of_gt hm)).mpr hb
  have ht : Format.binary64.targetExponent (totalExponent m (-1074)) = (-1074 : Int) + (0 : Nat) := by
    rw [target_scaled]
    omega
  simpa using roundWithAccuracy_eq s m (-1074) .exact 0 m 0 ht rfl (by simpa using ht) (by simpa)

theorem roundWithAccuracy_zero (s : Sign) :
    roundWithAccuracy Format.binary64 s 0 (-1074) .exact = .zero s := by rfl

theorem rounded_parameters (m : Nat) (hm : 2 ^ 53 ≤ m) :
    0 < m.log2 - 52 ∧
    2 ^ 52 ≤ Wasm.IEEE32.roundShift m (m.log2 - 52) ∧
    Wasm.IEEE32.roundShift m (m.log2 - 52) ≤ 2 ^ 53 := by
  have hn : m ≠ 0 := by omega
  have hl := (Nat.le_log2 hn).mpr hm
  let k := m.log2 - 52
  have hlo : 2 ^ 52 * 2 ^ k ≤ m := by
    rw [← pow_add, show 52 + k = m.log2 by omega]
    exact Nat.log2_self_le hn
  have hhi : m < 2 ^ 53 * 2 ^ k := by
    rw [← pow_add, show 53 + k = m.log2 + 1 by omega]
    exact Nat.lt_log2_self
  have hql := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).mpr hlo
  have hqh := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ k)).mpr hhi
  have hr := CodeLib.IEEE32.roundShift_bounds m k
  dsimp only [k] at hr hql hqh
  exact ⟨by omega, by omega, by omega⟩

theorem pack_roundWithAccuracy_scaled (s : Sign) (m : Nat) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
      (roundWithAccuracy Format.binary64 s m (-1074) .exact)) =
      Wasm.IEEE64.roundScaledMagnitude (negative s) m := by
  by_cases hz : m = 0
  · subst m
    rw [roundWithAccuracy_zero, pack_zero]
    cases s <;> rfl
  have hm : 0 < m := Nat.pos_of_ne_zero hz
  by_cases hsmall : m < 2 ^ 53
  · rw [roundWithAccuracy_small s m hm hsmall, pack_finite]
    norm_num only [Nat.reducePow] at hsmall
    by_cases hsub : m < 2 ^ 52
    · have hl := (Nat.log2_lt hz).mpr hsub
      norm_num only [Nat.reducePow] at hsub
      simp [Wasm.IEEE64.roundScaledMagnitude, hsub, Nat.ne_of_lt hl]
      rw [Nat.mod_eq_of_lt (by omega : m < 4503599627370496)]
    · have hl : m.log2 = 52 := (Nat.log2_eq_iff hz).mpr ⟨by omega, by omega⟩
      have hf : m % 4503599627370496 = m - 4503599627370496 := by omega
      norm_num only [Nat.reducePow] at hsub
      simp [Wasm.IEEE64.roundScaledMagnitude, hsub, hsmall, hl, hf]
  · obtain ⟨hk, hlo, hhi⟩ := rounded_parameters m (by omega)
    norm_num only [Nat.reducePow] at hsmall
    let k := m.log2 - 52
    let r := Wasm.IEEE32.roundShift m k
    have hr : (ExtendedMantissa.ofMantissaAndAccuracy m .exact >>> k).roundedMantissa = r := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      dsimp [r, k]
      rw [hj]
      exact round_exact_shift m j
    have ht : Format.binary64.targetExponent (totalExponent m (-1074)) = (-1074 : Int) + k := by
      rw [target_scaled]
      dsimp [k]
      omega
    have hsmall' : ¬m < 2 ^ 52 := by omega
    norm_num only [Nat.reducePow] at hsmall'
    have hround : Wasm.IEEE64.roundScaledMagnitude (negative s) m =
        if r = 2 ^ 53 then
          if 2047 ≤ k + 2 then Wasm.IEEE64.infinity (negative s)
          else Wasm.IEEE64.encodeFinite (negative s) (k + 2) 0
        else if 2047 ≤ k + 1 then Wasm.IEEE64.infinity (negative s)
          else Wasm.IEEE64.encodeFinite (negative s) (k + 1) (r - 2 ^ 52) := by
      simp [Wasm.IEEE64.roundScaledMagnitude, hsmall', hsmall, r, k]
      split <;> simp_all [Nat.add_assoc]
    rw [hround]
    by_cases hc : r = 2 ^ 53
    · have hfinal : Format.binary64.targetExponent (totalExponent (2 ^ 53) ((-1074 : Int) + k)) =
          (-1074 : Int) + k + (1 : Nat) := by
        simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
          Format.minExponent, Nat.log2_two_pow]
        omega
      have hvalue := roundWithAccuracy_eq s m (-1074) .exact k (2 ^ 53) 1 ht
        (hr.trans hc) hfinal (by decide)
      rw [hvalue, pack_finite]
      have he : ((-1074 : Int) + k + 1 + 1075).toNat = k + 2 := by omega
      simp [hc, he, show Nat.log2 4503599627370496 = 52 from rfl]
    · have hrpos : 0 < r := by dsimp [r, k]; omega
      have hrl : r.log2 = 52 := by
        apply (Nat.log2_eq_iff (Nat.ne_of_gt hrpos)).mpr
        dsimp [r, k] at hc ⊢
        constructor <;> omega
      have hfinal : Format.binary64.targetExponent (totalExponent r ((-1074 : Int) + k)) =
          (-1074 : Int) + k + (0 : Nat) := by
        simp only [Format.targetExponent, totalExponent, Format.mantissaBits,
          Format.minExponent, hrl]
        omega
      have hvalue := roundWithAccuracy_eq s m (-1074) .exact k r 0 ht hr hfinal (by simpa)
      rw [hvalue, pack_finite]
      have he : ((-1074 : Int) + k + 1075).toNat = k + 1 := by omega
      have hf : r % 4503599627370496 = r - 4503599627370496 := by dsimp [r, k] at hc ⊢; omega
      norm_num only [Nat.reducePow] at hc
      simp [hc, he, hrl, hf]

theorem pack_round_scaled (s : Sign) (m : Nat) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
      (UnpackedFloat.round Format.binary64 s m (-1074))) =
      Wasm.IEEE64.roundScaledMagnitude (negative s) m := by
  have he : ((-1074 : Int) - Format.binary64.targetExponent (totalExponent m (-1074))).toNat = 0 := by
    rw [target_scaled]
    omega
  simpa [UnpackedFloat.round, decreaseExponent, he] using pack_roundWithAccuracy_scaled s m

#print axioms pack_round_scaled

end Project.ProofKit.F64RoundScaled
