import CodeLib.IEEE64.Roundoff

/-! Integer guards for finite binary64 words, including zero and subnormals. -/
namespace Project.ProofKit.F64Order
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

def absBits (bits : UInt64) : UInt64 := bits &&& 0x7FFFFFFFFFFFFFFF

def finiteBits (bits : UInt64) : Bool :=
  decide (absBits bits < (0x7FF0000000000000 : UInt64))

def positiveBits (bits : UInt64) : Bool :=
  decide ((0 : UInt64) < bits) && decide (bits < (0x7FF0000000000000 : UInt64))

theorem absBits_toNat (bits : UInt64) :
    (absBits bits).toNat = bits.toNat % 2 ^ 63 := by
  simp only [absBits, UInt64.toNat_and]
  change bits.toNat &&& (2 ^ 63 - 1) = bits.toNat % 2 ^ 63
  exact Nat.and_two_pow_sub_one_eq_mod bits.toNat 63

theorem exponent_abs (bits : UInt64) :
    Wasm.IEEE64.exponent bits = (absBits bits).toNat / 2 ^ 52 := by
  rw [absBits_toNat]
  change bits.toNat / 2 ^ 52 % 2 ^ 11 = _
  rw [← Nat.mod_mul_right_div_self bits.toNat (2 ^ 52) (2 ^ 11)]
  norm_num

theorem fraction_abs (bits : UInt64) :
    Wasm.IEEE64.fraction bits = (absBits bits).toNat % 2 ^ 52 := by
  rw [absBits_toNat]
  exact (Nat.mod_mod_of_dvd bits.toNat (by norm_num : 2 ^ 52 ∣ 2 ^ 63)).symm

theorem finiteBits_iff (bits : UInt64) :
    finiteBits bits = true ↔ CodeLib.IEEE64.Finite bits := by
  have hbound : (absBits bits).toNat < 2 ^ 63 := by
    rw [absBits_toNat]
    exact Nat.mod_lt _ (by positivity)
  simp only [finiteBits, decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
    CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq,
    exponent_abs]
  change (absBits bits).toNat < 2047 * 2 ^ 52 ↔
    (absBits bits).toNat / 2 ^ 52 ≠ 2047
  omega

private def unsignedScaled (n : Nat) : Nat :=
  if n / 2 ^ 52 = 0 then n % 2 ^ 52
  else (2 ^ 52 + n % 2 ^ 52) * 2 ^ (n / 2 ^ 52 - 1)

theorem scaledMagnitude_abs (bits : UInt64) :
    Wasm.IEEE64.scaledMagnitude bits = unsignedScaled (absBits bits).toNat := by
  simp [Wasm.IEEE64.scaledMagnitude, unsignedScaled, exponent_abs, fraction_abs]

private theorem unsignedScaled_mono {left right : Nat} (hle : left ≤ right) :
    unsignedScaled left ≤ unsignedScaled right := by
  let le := left / 2 ^ 52
  let re := right / 2 ^ 52
  let lf := left % 2 ^ 52
  let rf := right % 2 ^ 52
  have hlf : lf < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hrf : rf < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hld : left = le * 2 ^ 52 + lf := (Nat.div_add_mod' left (2 ^ 52)).symm
  have hrd : right = re * 2 ^ 52 + rf := (Nat.div_add_mod' right (2 ^ 52)).symm
  change (if le = 0 then lf else (2 ^ 52 + lf) * 2 ^ (le - 1)) ≤
    (if re = 0 then rf else (2 ^ 52 + rf) * 2 ^ (re - 1))
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
        lf ≤ 2 ^ 52 := Nat.le_of_lt hlf
        _ ≤ (2 ^ 52 + rf) * 2 ^ (re - 1) := by nlinarith
    · rw [ite_eq_right hlz]
      have hsig : 2 ^ 52 + lf ≤ 2 ^ 53 := by norm_num at hlf ⊢; omega
      have hpow : 2 ^ le ≤ 2 ^ (re - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      calc
        (2 ^ 52 + lf) * 2 ^ (le - 1) ≤ 2 ^ 53 * 2 ^ (le - 1) :=
          Nat.mul_le_mul_right _ hsig
        _ = 2 ^ 52 * 2 ^ le := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        _ ≤ 2 ^ 52 * 2 ^ (re - 1) := Nat.mul_le_mul_left _ hpow
        _ ≤ (2 ^ 52 + rf) * 2 ^ (re - 1) :=
          Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- Comparing sign-cleared encodings orders their decoded real magnitudes. -/
theorem abs_value_mono (left right : UInt64)
    (hle : absBits left ≤ absBits right) :
    |CodeLib.IEEE64.value left| ≤ |CodeLib.IEEE64.value right| := by
  have hscaled : Wasm.IEEE64.scaledMagnitude left ≤ Wasm.IEEE64.scaledMagnitude right := by
    rw [scaledMagnitude_abs, scaledMagnitude_abs]
    exact unsignedScaled_mono (UInt64.le_iff_toNat_le.mp hle)
  have habs (x : UInt64) : |(Wasm.IEEE64.scaledValue x : ℝ)| =
      Wasm.IEEE64.scaledMagnitude x := by
    simp [Wasm.IEEE64.scaledValue]
    split <;> simp
  simp only [CodeLib.IEEE64.value, abs_div, habs]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hscaled) (by positivity)

theorem positiveBits_spec (bits : UInt64) (h : positiveBits bits = true) :
    CodeLib.IEEE64.Finite bits ∧ 0 < CodeLib.IEEE64.value bits := by
  have hraw : (0 : UInt64) < bits ∧ bits < 0x7FF0000000000000 := by
    simpa [positiveBits] using h
  have hlo : 0 < bits.toNat := UInt64.lt_iff_toNat_lt.mp hraw.1
  have hhi : bits.toNat < 0x7FF0000000000000 := UInt64.lt_iff_toNat_lt.mp hraw.2
  have hsmall : bits.toNat < 2 ^ 63 := by norm_num at hhi ⊢; omega
  have habs : (absBits bits).toNat = bits.toNat := by
    rw [absBits_toNat, Nat.mod_eq_of_lt hsmall]
  have hfinite : CodeLib.IEEE64.Finite bits := (finiteBits_iff bits).mp (by
    simpa only [finiteBits, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, habs] using
      (UInt64.lt_iff_toNat_lt.mp hraw.2))
  have hsign : Wasm.IEEE64.sign bits = false := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not] using
      (Nat.not_le_of_gt hsmall)
  have hscaled : 0 < Wasm.IEEE64.scaledMagnitude bits := by
    rw [scaledMagnitude_abs, habs]
    unfold unsignedScaled
    split
    · rename_i he
      have hd := Nat.div_add_mod' bits.toNat (2 ^ 52)
      omega
    · positivity
  refine ⟨hfinite, ?_⟩
  simp only [CodeLib.IEEE64.value, Wasm.IEEE64.scaledValue, hsign, Bool.false_eq_true,
    ite_false, Int.cast_natCast]
  positivity

theorem absBits_of_positive (bits : UInt64) (h : positiveBits bits = true) :
    absBits bits = bits := by
  have hraw : (0 : UInt64) < bits ∧ bits < 0x7FF0000000000000 := by
    simpa [positiveBits] using h
  apply UInt64.toNat_inj.mp
  rw [absBits_toNat]
  apply Nat.mod_eq_of_lt
  have hhi : bits.toNat < 0x7FF0000000000000 := UInt64.lt_iff_toNat_lt.mp hraw.2
  norm_num at hhi ⊢
  omega

-- Classification boundaries: both zeros, subnormals, largest finite words,
-- infinities, and NaNs. These are kernel-evaluated guards, not host floats.
example : finiteBits 0 = true ∧ finiteBits 0x8000000000000000 = true := by decide
example : positiveBits 0 = false ∧ positiveBits 0x8000000000000000 = false := by decide
example : positiveBits 1 = true ∧ positiveBits 0x000FFFFFFFFFFFFF = true := by decide
example : positiveBits 0x0010000000000000 = true := by decide
example : finiteBits 0x7FEFFFFFFFFFFFFF = true ∧
    finiteBits 0xFFEFFFFFFFFFFFFF = true := by decide
example : finiteBits 0x7FF0000000000000 = false ∧
    finiteBits 0xFFF0000000000000 = false := by decide
example : finiteBits 0x7FF0000000000001 = false ∧
    finiteBits 0xFFF8000000000000 = false := by decide

#print axioms absBits_of_positive
#print axioms finiteBits_iff
#print axioms abs_value_mono
#print axioms positiveBits_spec
end Project.ProofKit.F64Order
