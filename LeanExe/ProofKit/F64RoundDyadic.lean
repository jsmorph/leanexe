import LeanExe.ProofKit.F64RoundFinish

namespace LeanExe.ProofKit.F64RoundDyadic
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

end LeanExe.ProofKit.F64RoundDyadic
