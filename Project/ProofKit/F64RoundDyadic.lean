import Project.ProofKit.F64RoundFinish

namespace Project.ProofKit.F64RoundDyadic
open Float.Model Float.Model.UnpackedFloat F64Encoding FloatRounding F64RoundScaled F64RoundFinish FloatCommon

theorem target_dyadic (m f : Nat) :
    Format.binary64.targetExponent (totalExponent m (-1074 - (f : Int))) =
      (m.log2 - (f + 52) : Nat) - (1074 : Int) := by
  simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
  omega

theorem rounded_upper (m f : Nat) (hm : m ≠ 0) :
    rounded m (f + (m.log2 - (f + 52))) ≤ 2 ^ 53 := by
  let k := f + (m.log2 - (f + 52))
  have hl : m.log2 < k + 53 := by dsimp [k]; omega
  have hp : m < 2 ^ 53 * 2 ^ k := by
    rw [← pow_add, Nat.add_comm]
    exact (Nat.log2_lt hm).mp hl
  have hq := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ k)).mpr hp
  have hr := rounded_bounds m k
  change rounded m k ≤ 2 ^ 53
  omega

theorem rounded_lower (m f : Nat) (hk : 0 < m.log2 - (f + 52)) :
    2 ^ 52 ≤ rounded m (f + (m.log2 - (f + 52))) := by
  let k := f + (m.log2 - (f + 52))
  have hm : m ≠ 0 := by intro h; simp [h] at hk
  have hp : 2 ^ 52 * 2 ^ k ≤ m := by
    rw [← pow_add, show 52 + k = m.log2 by dsimp [k]; omega]
    exact Nat.log2_self_le hm
  have hq := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).mpr hp
  have hr := rounded_bounds m k
  change 2 ^ 52 ≤ rounded m k
  omega

theorem roundWithAccuracy_dyadic (s : Sign) (m f : Nat) :
    roundWithAccuracy Format.binary64 s m (-1074 - (f : Int)) .exact =
      finish s (rounded m (f + (m.log2 - (f + 52))))
        ((m.log2 - (f + 52) : Nat) - (1074 : Int)) := by
  let k := m.log2 - (f + 52)
  have ht : Format.binary64.targetExponent (totalExponent m (-1074 - (f : Int))) =
      (-1074 - (f : Int)) + (f + k : Nat) := by
    rw [target_dyadic]
    dsimp [k]
    omega
  rw [roundWithAccuracy_finish, shift_target m _ .exact (f + k) ht]
  dsimp only
  rw [rounded_eq]
  congr 1
  dsimp [k]
  omega

theorem roundShift_mul_pow (r k : Nat) (hk : 0 < k) : Wasm.IEEE32.roundShift (r * 2 ^ k) k = r := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold Wasm.IEEE32.roundShift
  have hhalf : 0 < 2 ^ (j + 1) / 2 := by rw [pow_succ]; simp
  simp [Nat.mul_div_cancel _ (Nat.two_pow_pos (j + 1)), hhalf]

/-- `roundScaledMagnitude` of an exact `r * 2 ^ k` with `r` in `[2^52, 2^53]`
encodes `r` with exponent field `k + 1`, carrying into the exponent when
`r = 2^53`.  Binary64's dyadic rounder reaches this form, where binary32's
encodes the fields directly. -/
theorem roundScaled_mul_pow (negative : Bool) (r k : Nat) (hk : 0 < k)
    (hlo : 2 ^ 52 ≤ r) (hhi : r ≤ 2 ^ 53) :
    Wasm.IEEE64.roundScaledMagnitude negative (r * 2 ^ k) =
      if r = 2 ^ 53 then
        if 2047 ≤ k + 2 then Wasm.IEEE64.infinity negative
        else Wasm.IEEE64.encodeFinite negative (k + 2) 0
      else if 2047 ≤ k + 1 then Wasm.IEEE64.infinity negative
      else Wasm.IEEE64.encodeFinite negative (k + 1) (r - 2 ^ 52) := by
  have hbig : 2 ^ 53 ≤ r * 2 ^ k :=
    calc 2 ^ 53 = 2 ^ 52 * 2 ^ 1 := by norm_num
      _ ≤ r * 2 ^ k := Nat.mul_le_mul hlo (Nat.pow_le_pow_right (by decide) hk)
  have hlog := FloatShift.log2_mul_pow r k (by omega)
  unfold Wasm.IEEE64.roundScaledMagnitude
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  by_cases hr : r = 2 ^ 53
  · subst hr
    have hshift : Nat.log2 (2 ^ 53 * 2 ^ k) - 52 = k + 1 := by
      rw [hlog, Nat.log2_two_pow]; omega
    have hround : Wasm.IEEE32.roundShift (2 ^ 53 * 2 ^ k) (k + 1) = 2 ^ 52 := by
      rw [show (2 : Nat) ^ 53 * 2 ^ k = 2 ^ 52 * 2 ^ (k + 1) by rw [pow_succ]; ring]
      exact roundShift_mul_pow _ _ (by omega)
    simp only [hshift, hround]
    simp
  · have hl : Nat.log2 r = 52 := by
      rw [Nat.log2_eq_iff (by omega)]
      omega
    have hshift : Nat.log2 (r * 2 ^ k) - 52 = k := by rw [hlog, hl]; omega
    simp only [hshift, roundShift_mul_pow r k hk]
    simp [show r ≠ 9007199254740992 from hr]

theorem pack_roundWithAccuracy_dyadic (s : Sign) (m f : Nat) (hm : m ≠ 0) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
      (roundWithAccuracy Format.binary64 s m (-1074 - (f : Int)) .exact)) =
      Wasm.IEEE64.roundDyadicMagnitude (negative s) m f := by
  rw [roundWithAccuracy_dyadic]
  let k := m.log2 - (f + 52)
  by_cases hk : k = 0
  · have hb := rounded_upper m f hm
    change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
      (finish s (rounded m (f + k)) ((k : Int) - 1074))) = _
    rw [hk]
    simp only [Nat.add_zero, Nat.cast_zero, Int.zero_sub]
    rw [pack_finish_scaled s (rounded m f) (by simpa [k, hk] using hb)]
    simp [Wasm.IEEE64.roundDyadicMagnitude, hm, show m.log2 - (f + 52) = 0 from hk, rounded]
  · have hlo := rounded_lower m f (by dsimp [k] at hk; omega)
    have hhi := rounded_upper m f hm
    rw [pack_finish_normal s _ _ hlo hhi]
    have hshift : f + k ≠ 0 := by omega
    have hr : Wasm.IEEE32.roundShift m (f + k) = rounded m (f + k) := by
      unfold rounded
      rw [ite_eq_right hshift]
    simp only [Wasm.IEEE64.roundDyadicMagnitude, beq_iff_eq, hm, ite_false]
    change _ = Wasm.IEEE64.roundScaledMagnitude (negative s)
      (if k = 0 then _ else Wasm.IEEE32.roundShift m (f + k) * 2 ^ k)
    rw [ite_eq_right hk, hr, roundScaled_mul_pow _ _ _ (Nat.pos_of_ne_zero hk) hlo hhi]

#print axioms pack_roundWithAccuracy_dyadic

theorem pack_round_dyadic (s : Sign) (m f : Nat) (hm : m ≠ 0) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
      (UnpackedFloat.round Format.binary64 s m (-1074 - (f : Int)))) =
      Wasm.IEEE64.roundDyadicMagnitude (negative s) m f := by
  have he : ((-1074 - (f : Int)) -
      Format.binary64.targetExponent (totalExponent m (-1074 - (f : Int)))).toNat = 0 := by
    rw [target_dyadic]
    omega
  simpa [UnpackedFloat.round, decreaseExponent, he] using pack_roundWithAccuracy_dyadic s m f hm

theorem pack_round_above_dyadic (s : Sign) (m f : Nat) (e : Int)
    (hm : m ≠ 0) (he : -1074 - (f : Int) ≤ e) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (UnpackedFloat.round Format.binary64 s m e)) =
      Wasm.IEEE64.roundDyadicMagnitude (negative s) (m * 2 ^ (e + 1074 + f).toNat) f := by
  have he' : e - ((e + 1074 + f).toNat : Int) = -1074 - (f : Int) := by omega
  have h := F64Normalize.round_mul_pow s m (e + 1074 + f).toNat e hm
  rw [he'] at h
  rw [← h, pack_round_dyadic _ _ _ (Nat.mul_ne_zero hm (by positivity))]

#print axioms pack_round_above_dyadic

end Project.ProofKit.F64RoundDyadic
