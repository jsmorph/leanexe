import Project.ProofKit.F32RoundBounds
import Project.ProofKit.F32Convert

set_option exponentiation.threshold 512

namespace Project.ProofKit.F32IntegerExact
open CodeLib.IEEE32

theorem roundShift_exact (n shift : Nat) (hShift : 0 < shift) (hDivides : 2 ^ shift ∣ n) :
    Wasm.IEEE32.roundShift n shift = n / 2 ^ shift := by
  have hHalf : 0 < 2 ^ shift / 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
    simp [pow_succ]
  simp [Wasm.IEEE32.roundShift, Nat.mod_eq_zero_of_dvd hDivides, hHalf]

theorem roundedMagnitude_mul_power (n k : Nat) (hN : n < 2 ^ 24) :
    roundedMagnitude (n * 2 ^ k) = n * 2 ^ k := by
  by_cases hSmall : n * 2 ^ k < 2 ^ 24
  · simp only [roundedMagnitude, hSmall, ite_true]
  have hNonzero : n ≠ 0 := by intro h; simp [h] at hSmall
  have hLog : Nat.log2 n < 24 := (Nat.log2_lt hNonzero).mpr hN
  have hLogProduct := F32Shift.log2_mul_pow n k hNonzero
  let shift := Nat.log2 (n * 2 ^ k) - 23
  have hShift : 0 < shift := by
    have hLower := (Nat.le_log2 (Nat.mul_ne_zero hNonzero (by positivity))).mpr
      (Nat.le_of_not_gt hSmall)
    change 0 < Nat.log2 (n * 2 ^ k) - 23
    omega
  have hShiftK : shift ≤ k := by dsimp only [shift]; omega
  have hProduct : n * 2 ^ k = (n * 2 ^ (k - shift)) * 2 ^ shift := by
    rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hShiftK]
  have hDivides : 2 ^ shift ∣ n * 2 ^ k := by
    rw [hProduct]
    exact dvd_mul_left _ _
  have hRound := roundShift_exact (n * 2 ^ k) shift hShift hDivides
  have hRestore : n * 2 ^ k / 2 ^ shift * 2 ^ shift = n * 2 ^ k :=
    Nat.div_mul_cancel hDivides
  simp only [roundedMagnitude, hSmall, ite_false]
  change (if Wasm.IEEE32.roundShift (n * 2 ^ k) shift == 2 ^ 24 then
    2 ^ 23 * 2 ^ (shift + 1) else
    Wasm.IEEE32.roundShift (n * 2 ^ k) shift * 2 ^ shift) = _
  rw [hRound]
  split
  · rename_i hCarry
    have hCarry' : n * 2 ^ k / 2 ^ shift = 2 ^ 24 := by simpa using hCarry
    rw [hCarry'] at hRestore
    calc
      2 ^ 23 * 2 ^ (shift + 1) = 2 ^ 24 * 2 ^ shift := by
        rw [pow_succ]
        ring
      _ = n * 2 ^ k := hRestore
  · exact hRestore

theorem fromInt_exact (value : Int) (hAbs : value.natAbs < 2 ^ 24) :
    CodeLib.IEEE32.Finite (Wasm.IEEE32.fromInt value) ∧
      CodeLib.IEEE32.value (Wasm.IEEE32.fromInt value) = value := by
  have hBound : value.natAbs * 2 ^ 149 < 2 ^ 173 := by
    have h := Nat.mul_lt_mul_of_pos_right hAbs (by positivity : 0 < (2 : Nat) ^ 149)
    simpa only [← pow_add] using h
  have hPack := F32RoundBounds.roundScaledMagnitude_spec (decide (value < 0))
    (value.natAbs * 2 ^ 149) 173 (by decide) hBound
  have hSign := F32RoundBounds.sign_roundScaledMagnitude (decide (value < 0))
    (value.natAbs * 2 ^ 149) 173 (by decide) hBound
  rw [roundedMagnitude_mul_power _ _ hAbs] at hPack
  refine ⟨hPack.1, ?_⟩
  have hScaled : Wasm.IEEE32.scaledValue (Wasm.IEEE32.fromInt value) = value * 2 ^ 149 := by
    simp only [Wasm.IEEE32.fromInt, Wasm.IEEE32.scaledValue, hSign, hPack.2.1,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.natCast_natAbs]
    split <;> rename_i hSignValue
    · rw [abs_of_neg (by simpa using hSignValue)]
      ring
    · rw [abs_of_nonneg (by simpa using hSignValue)]
  rw [CodeLib.IEEE32.value, hScaled]
  push_cast
  field_simp
  norm_num

theorem conversion_exact (word : UInt32)
    (hAbs : (LeanExe.Signed32.decode word).natAbs < 2 ^ 24) :
    CodeLib.IEEE32.Finite (LeanExe.Float32.ofInt32Bits word) ∧
      CodeLib.IEEE32.value (LeanExe.Float32.ofInt32Bits word) = LeanExe.Signed32.decode word := by
  rw [F32Convert.ofInt32Bits_eq]
  change CodeLib.IEEE32.Finite (Wasm.IEEE32.fromInt (Wasm.IEEE32.signedI32Value word)) ∧
    CodeLib.IEEE32.value (Wasm.IEEE32.fromInt (Wasm.IEEE32.signedI32Value word)) = LeanExe.Signed32.decode word
  rw [← QuantizedInt32.decode_talos]
  exact fromInt_exact _ hAbs

#print axioms roundedMagnitude_mul_power
#print axioms fromInt_exact
#print axioms conversion_exact
end Project.ProofKit.F32IntegerExact
