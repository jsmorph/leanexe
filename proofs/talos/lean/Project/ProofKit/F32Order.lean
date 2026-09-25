import CodeLib.IEEE32.Roundoff

namespace Project.ProofKit.F32Order
set_option exponentiation.threshold 512
set_option maxRecDepth 8192

def absBits (bits : UInt32) : UInt32 := bits &&& 0x7FFFFFFF

def finiteBits (bits : UInt32) : Bool :=
  decide (absBits bits < (0x7F800000 : UInt32))

def positiveBits (bits : UInt32) : Bool :=
  decide ((0 : UInt32) < bits) && decide (bits < (0x7F800000 : UInt32))

theorem absBits_toNat (bits : UInt32) :
    (absBits bits).toNat = bits.toNat % 2 ^ 31 := by
  simp only [absBits, UInt32.toNat_and]
  change bits.toNat &&& (2 ^ 31 - 1) = bits.toNat % 2 ^ 31
  exact Nat.and_two_pow_sub_one_eq_mod bits.toNat 31

theorem exponent_abs (bits : UInt32) :
    Wasm.IEEE32.exponent bits = (absBits bits).toNat / 2 ^ 23 := by
  rw [absBits_toNat]
  change bits.toNat / 2 ^ 23 % 2 ^ 8 = _
  rw [← Nat.mod_mul_right_div_self bits.toNat (2 ^ 23) (2 ^ 8)]
  norm_num

theorem fraction_abs (bits : UInt32) :
    Wasm.IEEE32.fraction bits = (absBits bits).toNat % 2 ^ 23 := by
  rw [absBits_toNat]
  exact (Nat.mod_mod_of_dvd bits.toNat (by norm_num : 2 ^ 23 ∣ 2 ^ 31)).symm

theorem finiteBits_iff (bits : UInt32) :
    finiteBits bits = true ↔ CodeLib.IEEE32.Finite bits := by
  have hbound : (absBits bits).toNat < 2 ^ 31 := by
    rw [absBits_toNat]
    exact Nat.mod_lt _ (by positivity)
  simp only [finiteBits, decide_eq_true_eq, UInt32.lt_iff_toNat_lt,
    CodeLib.IEEE32.Finite, Wasm.IEEE32.isFinite, bne_iff_ne, ne_eq,
    exponent_abs]
  change (absBits bits).toNat < 255 * 2 ^ 23 ↔
    (absBits bits).toNat / 2 ^ 23 ≠ 255
  omega

def unsignedScaled (n : Nat) : Nat :=
  if n / 2 ^ 23 = 0 then n % 2 ^ 23
  else (2 ^ 23 + n % 2 ^ 23) * 2 ^ (n / 2 ^ 23 - 1)

theorem scaledMagnitude_abs (bits : UInt32) :
    Wasm.IEEE32.scaledMagnitude bits = unsignedScaled (absBits bits).toNat := by
  simp [Wasm.IEEE32.scaledMagnitude, unsignedScaled, exponent_abs, fraction_abs]

private theorem unsignedScaled_mono {left right : Nat} (hle : left ≤ right) :
    unsignedScaled left ≤ unsignedScaled right := by
  let le := left / 2 ^ 23
  let re := right / 2 ^ 23
  let lf := left % 2 ^ 23
  let rf := right % 2 ^ 23
  have hlf : lf < 2 ^ 23 := Nat.mod_lt _ (by positivity)
  have hrf : rf < 2 ^ 23 := Nat.mod_lt _ (by positivity)
  have hld : left = le * 2 ^ 23 + lf := (Nat.div_add_mod' left (2 ^ 23)).symm
  have hrd : right = re * 2 ^ 23 + rf := (Nat.div_add_mod' right (2 ^ 23)).symm
  change (if le = 0 then lf else (2 ^ 23 + lf) * 2 ^ (le - 1)) ≤
    (if re = 0 then rf else (2 ^ 23 + rf) * 2 ^ (re - 1))
  by_cases heq : le = re
  · have hfrac : lf ≤ rf := by omega
    rw [← heq]
    split
    · exact hfrac
    · exact Nat.mul_le_mul_right _ (Nat.add_le_add_left hfrac _)
  · have hexp : le < re := by omega
    have hrnz : re ≠ 0 := by omega
    rw [ite_eq_right hrnz]
    by_cases hlz : le = 0
    · rw [ite_eq_left hlz]
      have hp : 1 ≤ 2 ^ (re - 1) := Nat.one_le_pow _ _ (by omega)
      calc
        lf ≤ 2 ^ 23 := Nat.le_of_lt hlf
        _ ≤ (2 ^ 23 + rf) * 2 ^ (re - 1) := by nlinarith
    · rw [ite_eq_right hlz]
      have hsig : 2 ^ 23 + lf ≤ 2 ^ 24 := by norm_num at hlf ⊢; omega
      have hpow : 2 ^ le ≤ 2 ^ (re - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      calc
        (2 ^ 23 + lf) * 2 ^ (le - 1) ≤ 2 ^ 24 * 2 ^ (le - 1) :=
          Nat.mul_le_mul_right _ hsig
        _ = 2 ^ 23 * 2 ^ le := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        _ ≤ 2 ^ 23 * 2 ^ (re - 1) := Nat.mul_le_mul_left _ hpow
        _ ≤ (2 ^ 23 + rf) * 2 ^ (re - 1) :=
          Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

theorem abs_value_mono (left right : UInt32)
    (hle : absBits left ≤ absBits right) :
    |CodeLib.IEEE32.value left| ≤ |CodeLib.IEEE32.value right| := by
  have hscaled : Wasm.IEEE32.scaledMagnitude left ≤ Wasm.IEEE32.scaledMagnitude right := by
    rw [scaledMagnitude_abs, scaledMagnitude_abs]
    exact unsignedScaled_mono (UInt32.le_iff_toNat_le.mp hle)
  have habs (x : UInt32) : |(Wasm.IEEE32.scaledValue x : ℝ)| =
      Wasm.IEEE32.scaledMagnitude x := by
    simp [Wasm.IEEE32.scaledValue]
    split <;> simp
  simp only [CodeLib.IEEE32.value, abs_div, habs]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hscaled) (by positivity)

theorem positiveBits_spec (bits : UInt32) (h : positiveBits bits = true) :
    CodeLib.IEEE32.Finite bits ∧ 0 < CodeLib.IEEE32.value bits := by
  have hraw : (0 : UInt32) < bits ∧ bits < 0x7F800000 := by
    simpa [positiveBits] using h
  have hlo : 0 < bits.toNat := UInt32.lt_iff_toNat_lt.mp hraw.1
  have hhi : bits.toNat < 0x7F800000 := UInt32.lt_iff_toNat_lt.mp hraw.2
  have hsmall : bits.toNat < 2 ^ 31 := by norm_num at hhi ⊢; omega
  have habs : (absBits bits).toNat = bits.toNat := by
    rw [absBits_toNat, Nat.mod_eq_of_lt hsmall]
  have hfinite : CodeLib.IEEE32.Finite bits := (finiteBits_iff bits).mp (by
    simpa only [finiteBits, decide_eq_true_eq, UInt32.lt_iff_toNat_lt, habs] using
      (UInt32.lt_iff_toNat_lt.mp hraw.2))
  have hsign : Wasm.IEEE32.sign bits = false := by
    simpa only [Wasm.IEEE32.sign, decide_eq_false_iff_not] using
      (Nat.not_le_of_gt hsmall)
  have hscaled : 0 < Wasm.IEEE32.scaledMagnitude bits := by
    rw [scaledMagnitude_abs, habs]
    unfold unsignedScaled
    split
    · rename_i he
      have hd := Nat.div_add_mod' bits.toNat (2 ^ 23)
      omega
    · positivity
  refine ⟨hfinite, ?_⟩
  simp only [CodeLib.IEEE32.value, Wasm.IEEE32.scaledValue, hsign, Bool.false_eq_true,
    ite_false, Int.cast_natCast]
  positivity

theorem absBits_of_positive (bits : UInt32) (h : positiveBits bits = true) :
    absBits bits = bits := by
  have hraw : (0 : UInt32) < bits ∧ bits < 0x7F800000 := by
    simpa [positiveBits] using h
  apply UInt32.toNat_inj.mp
  rw [absBits_toNat]
  apply Nat.mod_eq_of_lt
  have hhi : bits.toNat < 0x7F800000 := UInt32.lt_iff_toNat_lt.mp hraw.2
  norm_num at hhi ⊢
  omega

#print axioms absBits_of_positive
#print axioms finiteBits_iff
#print axioms abs_value_mono
#print axioms positiveBits_spec
end Project.ProofKit.F32Order
