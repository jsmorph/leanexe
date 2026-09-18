import Project.ProofKit.F32RoundScaled
import Project.ProofKit.F32Shift

namespace Project.ProofKit.F32Normalize
open Float.Model Float.Model.UnpackedFloat F32Rounding F32Shift

def aligned (m : Nat) (e target : Int) : ExtendedMantissa :=
  ExtendedMantissa.ofMantissaAndAccuracy (m * 2 ^ (e - target).toNat) .exact >>>
    (target - e).toNat

theorem first_shift (m : Nat) (e : Int) (hm : m ≠ 0) :
    (let target := Format.binary32.targetExponent (totalExponent m e)
     let p := decreaseExponent m e target
     shiftToTargetExponent Format.binary32 p.1 p.2 .exact) =
      (aligned m e (Format.binary32.targetExponent (totalExponent m e)),
       Format.binary32.targetExponent (totalExponent m e)) := by
  let t := Format.binary32.targetExponent (totalExponent m e)
  change shiftToTargetExponent Format.binary32
    (m <<< (e - t).toNat) (e - (e - t).toNat) .exact = (aligned m e t, t)
  rw [Nat.shiftLeft_eq]
  unfold shiftToTargetExponent
  rw [target_mul_pow m (e - t).toNat e hm]
  change shiftToExponent (m * 2 ^ (e - t).toNat) (e - (e - t).toNat) .exact t = _
  have hk : (t - (e - (e - t).toNat)).toNat = (t - e).toNat := by omega
  have he : e - (e - t).toNat + (t - e).toNat = t := by omega
  simp only [shiftToExponent, hk, he, aligned]

theorem roundWithAccuracy_congr (s : Sign) (m m' : Nat) (e e' : Int)
    (h : shiftToTargetExponent Format.binary32 m e .exact =
      shiftToTargetExponent Format.binary32 m' e' .exact) :
    roundWithAccuracy Format.binary32 s m e .exact =
      roundWithAccuracy Format.binary32 s m' e' .exact := by
  unfold roundWithAccuracy
  rw [h]

theorem round_congr_aligned (s : Sign) (m m' : Nat) (e e' : Int)
    (hm : m ≠ 0) (hm' : m' ≠ 0)
    (ht : Format.binary32.targetExponent (totalExponent m e) =
      Format.binary32.targetExponent (totalExponent m' e'))
    (ha : aligned m e (Format.binary32.targetExponent (totalExponent m e)) =
      aligned m' e' (Format.binary32.targetExponent (totalExponent m' e'))) :
    UnpackedFloat.round Format.binary32 s m e = UnpackedFloat.round Format.binary32 s m' e' := by
  unfold UnpackedFloat.round
  apply roundWithAccuracy_congr
  exact (first_shift m e hm).trans ((Prod.ext ha ht).trans (first_shift m' e' hm').symm)

theorem aligned_mul_pow (m k : Nat) (e t : Int) :
    aligned (m * 2 ^ k) (e - k) t = aligned m e t := by
  by_cases hte : t ≤ e - k
  · have hl : (t - (e - k)).toNat = 0 := by omega
    have hr : (t - e).toNat = 0 := by omega
    have hk : k + (e - k - t).toNat = (e - t).toNat := by omega
    simp only [aligned, hl, hr, shift_zero]
    rw [Nat.mul_assoc, ← pow_add, hk]
  · have hl : (e - k - t).toNat = 0 := by omega
    simp only [aligned, hl, pow_zero, Nat.mul_one]
    by_cases hte' : t ≤ e
    · have hr : (t - e).toNat = 0 := by omega
      have hk : (t - (e - k)).toNat ≤ k := by omega
      have he : k - (t - (e - k)).toNat = (e - t).toNat := by omega
      rw [hr, shift_zero, shift_exact_mul_pow_le m k _ hk, he]
    · have hr : (e - t).toNat = 0 := by omega
      have hk : (t - (e - k)).toNat = k + (t - e).toNat := by omega
      rw [hk, shift_exact_mul_pow_add, hr]
      simp

theorem round_mul_pow (s : Sign) (m k : Nat) (e : Int) (hm : m ≠ 0) :
    UnpackedFloat.round Format.binary32 s (m * 2 ^ k) (e - k) =
      UnpackedFloat.round Format.binary32 s m e := by
  apply round_congr_aligned s _ _ _ _ (Nat.mul_ne_zero hm (by positivity)) hm
    (target_mul_pow m k e hm)
  rw [target_mul_pow m k e hm, aligned_mul_pow]

theorem pack_round_above_min (s : Sign) (m : Nat) (e : Int)
    (hm : m ≠ 0) (he : -149 ≤ e) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.round Format.binary32 s m e)) =
      Wasm.IEEE32.roundScaledMagnitude (F32Encoding.negative s) (m * 2 ^ (e + 149).toNat) := by
  have he' : e - ((e + 149).toNat : Int) = -149 := by omega
  have h := round_mul_pow s m (e + 149).toNat e hm
  rw [he'] at h
  rw [← h, F32RoundScaled.pack_round_scaled]

#print axioms round_mul_pow
#print axioms pack_round_above_min

theorem pack_normalize (z : Int) (e : Int) (s : Sign) (he : -149 ≤ e) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.normalize Format.binary32 z e s)) =
      if z = 0 then Wasm.IEEE32.signMask (F32Encoding.negative s)
      else Wasm.IEEE32.roundScaledMagnitude (decide (z < 0))
        (z.natAbs * 2 ^ (e + 149).toNat) := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => simp [UnpackedFloat.normalize, F32Packing.pack_zero]
    | succ n =>
      simp only [Int.ofNat_eq_natCast]
      have hc : compare ((n + 1 : Nat) : Int) 0 = .gt := Int.compare_eq_gt.mpr (by omega)
      simp only [UnpackedFloat.normalize, hc, Int.toNat_natCast]
      rw [pack_round_above_min _ _ _ (by omega) he]
      have hz : ((n + 1 : Nat) : Int) ≠ 0 := by omega
      have hn : ¬((n + 1 : Nat) : Int) < 0 := by omega
      simp only [hz, hn, ↓reduceIte, decide_false, F32Encoding.negative, Int.natAbs_natCast]
  | negSucc n =>
    have hc : compare (Int.negSucc n) 0 = .lt := Int.compare_eq_lt.mpr (by omega)
    simp only [UnpackedFloat.normalize, hc, Int.neg_negSucc, Int.toNat_natCast]
    rw [pack_round_above_min _ _ _ (by omega) he]
    simp [F32Encoding.negative]

#print axioms pack_normalize

end Project.ProofKit.F32Normalize
