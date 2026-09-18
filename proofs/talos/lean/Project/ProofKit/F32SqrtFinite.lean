import Project.ProofKit.F32SqrtCore
import Project.ProofKit.F32RoundFinish

namespace Project.ProofKit.F32SqrtFinite
open Float.Model Float.Model.UnpackedFloat F32SqrtCore F32SqrtRounding F32RoundFinish

theorem pack_sqrt_finite (m : Nat) (e : Int) (hm : 0 < m)
    (hl : m.log2 ≤ 23) (he : -149 ≤ e) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.sqrt Format.binary32 (.finite .positive m e hm))) =
      Wasm.IEEE32.roundSqrtMagnitude (m * 2 ^ (e + 149).toNat) := by
  let t := coreExponent m e
  let n := m * 2 ^ (e - 2 * t).toNat
  let k := (t + 149).toNat
  have hn : n ≠ 0 := by dsimp [n]; positivity
  have hr : n.sqrt ≠ 0 := fun h => hn (Nat.sqrt_eq_zero.mp h)
  have hlog : n.sqrt.log2 = 23 := root_log m e (by omega) hl he
  have ht : -149 ≤ t := (coreExponent_bounds m e hl he).1
  have htarget : Format.binary32.targetExponent (totalExponent n.sqrt t) = t + (0 : Nat) := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent, hlog]
    omega
  have ⟨hlo, hhi⟩ := (Nat.log2_eq_iff hr).mp hlog
  have hb := rounded_root_bounds n
  rw [UnpackedFloat.sqrt, core_eq m e hl he]
  change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
    (roundWithAccuracy Format.binary32 .positive n.sqrt t (rootAccuracy n))) = _
  rw [roundWithAccuracy_finish, F32RoundScaled.shift_target _ _ _ 0 htarget]
  simp only [F32Rounding.shift_zero, Nat.cast_zero, add_zero]
  rw [rounded_root, pack_finish_above_min _ _ _ (by omega) (by omega) ht]
  have hmag : m * 2 ^ (e + 149).toNat ≠ 0 := by positivity
  have hrad : (m * 2 ^ (e + 149).toNat) * 2 ^ 149 = n * 2 ^ (2 * k) :=
    (radicand_scaled m e hl he).symm
  simp only [Wasm.IEEE32.roundSqrtMagnitude, beq_iff_eq, hmag, ite_false, hrad,
    scaled_root_log n k hn hlog, show 23 + k - 23 = k by omega, roundSqrtIntegral_scaled]
  rfl

#print axioms pack_sqrt_finite

end Project.ProofKit.F32SqrtFinite
