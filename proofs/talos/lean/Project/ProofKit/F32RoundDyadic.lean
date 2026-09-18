import Project.ProofKit.F32RoundFinish

namespace Project.ProofKit.F32RoundDyadic
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Rounding F32RoundScaled F32RoundFinish

def rounded (m k : Nat) : Nat := if k = 0 then m else Wasm.IEEE32.roundShift m k

theorem rounded_eq (m k : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy m .exact >>> k).roundedMantissa = rounded m k := by
  cases k with
  | zero => rfl
  | succ k => exact round_exact_shift m k

theorem rounded_bounds (m k : Nat) : m / 2 ^ k ≤ rounded m k ∧ rounded m k ≤ m / 2 ^ k + 1 := by
  by_cases hk : k = 0
  · simp [rounded, hk]
  · simpa [rounded, hk] using CodeLib.IEEE32.roundShift_bounds m k

theorem target_dyadic (m f : Nat) :
    Format.binary32.targetExponent (totalExponent m (-149 - (f : Int))) =
      (m.log2 - (f + 23) : Nat) - (149 : Int) := by
  simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
  omega

theorem rounded_upper (m f : Nat) (hm : m ≠ 0) :
    rounded m (f + (m.log2 - (f + 23))) ≤ 2 ^ 24 := by
  let k := f + (m.log2 - (f + 23))
  have hl : m.log2 < k + 24 := by dsimp [k]; omega
  have hp : m < 2 ^ 24 * 2 ^ k := by
    rw [← pow_add, Nat.add_comm]
    exact (Nat.log2_lt hm).mp hl
  have hq := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ k)).mpr hp
  have hr := rounded_bounds m k
  change rounded m k ≤ 2 ^ 24
  omega

theorem rounded_lower (m f : Nat) (hk : 0 < m.log2 - (f + 23)) :
    2 ^ 23 ≤ rounded m (f + (m.log2 - (f + 23))) := by
  let k := f + (m.log2 - (f + 23))
  have hm : m ≠ 0 := by intro h; simp [h] at hk
  have hp : 2 ^ 23 * 2 ^ k ≤ m := by
    rw [← pow_add, show 23 + k = m.log2 by dsimp [k]; omega]
    exact Nat.log2_self_le hm
  have hq := (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).mpr hp
  have hr := rounded_bounds m k
  change 2 ^ 23 ≤ rounded m k
  omega

theorem roundWithAccuracy_dyadic (s : Sign) (m f : Nat) :
    roundWithAccuracy Format.binary32 s m (-149 - (f : Int)) .exact =
      finish s (rounded m (f + (m.log2 - (f + 23))))
        ((m.log2 - (f + 23) : Nat) - (149 : Int)) := by
  let k := m.log2 - (f + 23)
  have ht : Format.binary32.targetExponent (totalExponent m (-149 - (f : Int))) =
      (-149 - (f : Int)) + (f + k : Nat) := by
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
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (roundWithAccuracy Format.binary32 s m (-149 - (f : Int)) .exact)) =
      Wasm.IEEE32.roundDyadicMagnitude (negative s) m f := by
  rw [roundWithAccuracy_dyadic]
  let k := m.log2 - (f + 23)
  by_cases hk : k = 0
  · have hb := rounded_upper m f hm
    change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (finish s (rounded m (f + k)) ((k : Int) - 149))) = _
    rw [hk]
    simp only [Nat.add_zero, Nat.cast_zero, Int.zero_sub]
    rw [pack_finish_scaled s (rounded m f) (by simpa [k, hk] using hb)]
    simp [Wasm.IEEE32.roundDyadicMagnitude, hm, show m.log2 - (f + 23) = 0 from hk, rounded]
  · have hlo := rounded_lower m f (by dsimp [k] at hk; omega)
    have hhi := rounded_upper m f hm
    rw [pack_finish_normal s _ _ hlo hhi]
    have hshift : f + k ≠ 0 := by omega
    simp only [Wasm.IEEE32.roundDyadicMagnitude, beq_iff_eq, hm, ite_false]
    change _ = if k = 0 then _ else _
    simp only [hk, ite_false]
    simp only [rounded, show f + (m.log2 - (f + 23)) ≠ 0 from hshift, ite_false]
    split <;> simp_all [k, Nat.add_assoc]

#print axioms pack_roundWithAccuracy_dyadic

theorem pack_round_dyadic (s : Sign) (m f : Nat) (hm : m ≠ 0) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.round Format.binary32 s m (-149 - (f : Int)))) =
      Wasm.IEEE32.roundDyadicMagnitude (negative s) m f := by
  have he : ((-149 - (f : Int)) -
      Format.binary32.targetExponent (totalExponent m (-149 - (f : Int)))).toNat = 0 := by
    rw [target_dyadic]
    omega
  simpa [UnpackedFloat.round, decreaseExponent, he] using pack_roundWithAccuracy_dyadic s m f hm

theorem pack_round_above_dyadic (s : Sign) (m f : Nat) (e : Int)
    (hm : m ≠ 0) (he : -149 - (f : Int) ≤ e) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (UnpackedFloat.round Format.binary32 s m e)) =
      Wasm.IEEE32.roundDyadicMagnitude (negative s) (m * 2 ^ (e + 149 + f).toNat) f := by
  have he' : e - ((e + 149 + f).toNat : Int) = -149 - (f : Int) := by omega
  have h := F32Normalize.round_mul_pow s m (e + 149 + f).toNat e hm
  rw [he'] at h
  rw [← h, pack_round_dyadic _ _ _ (Nat.mul_ne_zero hm (by positivity))]

#print axioms pack_round_above_dyadic

end Project.ProofKit.F32RoundDyadic
