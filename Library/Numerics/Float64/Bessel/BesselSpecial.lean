import Library.Numerics.Float64.Bessel.Compiled
import Library.Numerics.Float64.Trig.TrigSinCos

/-!
The exceptional results of `Bessel.j0`, `Bessel.j1`, `Bessel.y0`, and `Bessel.y1`, as POSIX gives
them.  `j0` returns `+0` at both infinities and `j1` returns `+0` at `+∞` and `-0` at `-∞`.  `y0` and
`y1` return `+0` at `+∞`, negative infinity at both zeros, and the canonical NaN for an argument with
the sign bit set other than `-0`, negative infinity included.  A NaN argument gives the canonical NaN
for all four functions.  The guards of the code compare the high word `ix` of `|x|`, the word
`u <<< 1`, which is zero exactly at the zeros, and the sign bit `u >>> 63`.
-/

namespace Library.Numerics.Float64.Bessel.BesselSpecial
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem high_toNat (w : UInt64) :
    ((w >>> 32) &&& 0x7fffffff).toNat = w.toNat % 2 ^ 63 / 2 ^ 32 :=
  Library.Numerics.Float64.Trig.TrigSinCos.high_word w

theorem double_zero (w : UInt64) : (w <<< 1 == 0) = decide (w.toNat % 2 ^ 63 = 0) := by
  have h := Library.Numerics.Float64.Trig.TrigWords.shl_toNat w 1
  have hw := w.toNat_lt
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, h]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow, pow_one] at hw ⊢
  omega

theorem sign_bit (w : UInt64) : (w >>> 63 == 1) = decide (2 ^ 63 ≤ w.toNat) := by
  have h := Library.Numerics.Float64.Trig.TrigWords.shr_toNat w 63
  have hw := w.toNat_lt
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, h]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow] at hw ⊢
  omega

/-- The guard `ix ≥ 0x7ff00000` holds exactly for infinities and NaNs. -/
theorem nonfinite_guard (w : UInt64) :
    (w >>> 32 &&& 0x7fffffff ≥ 0x7ff00000) ↔ ¬ Finite w := by
  rw [ge_iff_le, UInt64.le_iff_toNat_le, high_toNat]
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent
  have hw := w.toNat_lt
  simp only [UInt64.reduceToNat, bne_iff_ne, ne_eq, Decidable.not_not, Nat.reducePow] at hw ⊢
  omega

theorem nan_not_finite (w : UInt64) (h : Wasm.IEEE64.isNaN w = true) : ¬ Finite w := by
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite
  simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq] at h
  simp [h.1]

theorem mul_nan (w : UInt64) (h : Wasm.IEEE64.isNaN w = true) :
    Wasm.IEEE64.mul w w = Wasm.IEEE64.canonicalNaN := by
  simp [Wasm.IEEE64.mul, h]

theorem add_nan (w v : UInt64) (h : Wasm.IEEE64.isNaN w = true) :
    Wasm.IEEE64.add w v = Wasm.IEEE64.canonicalNaN := by
  simp [Wasm.IEEE64.add, h]

theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl

theorem div_canonical :
    Wasm.IEEE64.div 0x3FF0000000000000 Wasm.IEEE64.canonicalNaN = Wasm.IEEE64.canonicalNaN := by
  decide +kernel

/-- `j0 (±∞) = +0`. -/
theorem j0_infinity (x : Float)
    (h : x.toBits = 0x7FF0000000000000 ∨ x.toBits = 0xFFF0000000000000) :
    (Bessel.j0 x).toBits = 0 := by
  unfold Bessel.j0 Bessel.j0With
  dsimp only
  rcases h with h | h <;>
  · rw [ite_eq_left (show x.toBits >>> 32 &&& 0x7fffffff ≥ 0x7ff00000 by rw [h]; decide),
      F64Bits.toBits_div, F64Bits.toBits_mul, h, one_bits]
    decide +kernel

/-- `j0` of a NaN is the canonical NaN. -/
theorem j0_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Bessel.j0 x).toBits = Wasm.IEEE64.canonicalNaN := by
  unfold Bessel.j0 Bessel.j0With
  dsimp only
  rw [ite_eq_left ((nonfinite_guard _).mpr (nan_not_finite _ h)), F64Bits.toBits_div,
    F64Bits.toBits_mul, mul_nan _ h, one_bits, div_canonical]

/-- `j1 (+∞) = +0` and `j1 (-∞) = -0`. -/
theorem j1_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Bessel.j1 x).toBits = 0 := by
  unfold Bessel.j1 Bessel.j1With
  dsimp only
  rw [ite_eq_left (show x.toBits >>> 32 &&& 0x7fffffff ≥ 0x7ff00000 by rw [h]; decide),
    F64Bits.toBits_div, h, one_bits]
  decide +kernel

theorem j1_neg_infinity (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (Bessel.j1 x).toBits = 0x8000000000000000 := by
  unfold Bessel.j1 Bessel.j1With
  dsimp only
  rw [ite_eq_left (show x.toBits >>> 32 &&& 0x7fffffff ≥ 0x7ff00000 by rw [h]; decide),
    F64Bits.toBits_div, h, one_bits]
  decide +kernel

/-- `j1` of a NaN is the canonical NaN. -/
theorem j1_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Bessel.j1 x).toBits = Wasm.IEEE64.canonicalNaN := by
  unfold Bessel.j1 Bessel.j1With
  dsimp only
  rw [ite_eq_left ((nonfinite_guard _).mpr (nan_not_finite _ h)), F64Bits.toBits_div, one_bits]
  simp [Wasm.IEEE64.div, h]

/-- The common part of `y0` and `y1` at `+∞`, a NaN, and `-∞`: `1 / (x + x x)`. -/
theorem recip_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (1.0 / (x + x * x)).toBits = 0 := by
  rw [F64Bits.toBits_div, F64Bits.toBits_add, F64Bits.toBits_mul, h, one_bits]
  decide +kernel

theorem recip_neg_infinity (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (1.0 / (x + x * x)).toBits = Wasm.IEEE64.canonicalNaN := by
  rw [F64Bits.toBits_div, F64Bits.toBits_add, F64Bits.toBits_mul, h, one_bits]
  decide +kernel

theorem recip_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (1.0 / (x + x * x)).toBits = Wasm.IEEE64.canonicalNaN := by
  rw [F64Bits.toBits_div, F64Bits.toBits_add, add_nan _ _ h, one_bits, div_canonical]

theorem neg_one_div_zero : (-1.0 / 0.0 : Float).toBits = 0xFFF0000000000000 := by
  rw [F64Bits.toBits_div, F64Bits.toBits_neg, one_bits]
  decide +kernel

theorem zero_div_zero : (0.0 / 0.0 : Float).toBits = Wasm.IEEE64.canonicalNaN := by
  rw [F64Bits.toBits_div]
  decide +kernel

/-- A word with the sign bit set, other than `-0`, is `-∞`, a NaN, or a negative finite number. -/
theorem negative_cases (w : UInt64) (hs : Wasm.IEEE64.sign w = true)
    (hz : w ≠ 0x8000000000000000) :
    w = 0xFFF0000000000000 ∨ Wasm.IEEE64.isNaN w = true ∨
      (Finite w ∧ ¬ w.toNat % 2 ^ 63 = 0) := by
  have hw := w.toNat_lt
  have hz' : w.toNat ≠ 0x8000000000000000 := fun h => hz (UInt64.toNat_inj.mp (by rw [h]; rfl))
  simp only [Wasm.IEEE64.sign, decide_eq_true_eq] at hs
  by_cases hf : Finite w
  · right; right
    refine ⟨hf, ?_⟩
    simp only [Nat.reducePow] at hw hs ⊢
    omega
  · by_cases hn : Wasm.IEEE64.isNaN w = true
    · exact Or.inr (Or.inl hn)
    · left
      unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hf
      simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
        beq_iff_eq, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hf hn
      apply UInt64.toNat_inj.mp
      simp only [Nat.reducePow] at hw hs hf hn ⊢
      have := hn hf
      show w.toNat = 18442240474082181120
      omega

/-- `y0 (+∞) = +0`. -/
theorem y0_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Bessel.y0 x).toBits = 0 := by
  unfold Bessel.y0 Bessel.y0With
  dsimp only
  rw [ite_eq_left (show x.toBits >>> 32 &&& 0x7fffffff ≥ 0x7ff00000 by rw [h]; decide)]
  exact recip_pos_infinity x h

/-- `y0 (±0) = -∞`. -/
theorem y0_zero (x : Float) (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    (Bessel.y0 x).toBits = 0xFFF0000000000000 := by
  unfold Bessel.y0 Bessel.y0With
  dsimp only
  rcases h with h | h <;>
  · rw [ite_eq_right (show ¬ x.toBits >>> 32 &&& 0x7fffffff ≥ 0x7ff00000 by rw [h]; decide),
      ite_eq_left (show (x.toBits <<< 1 == 0) = true by rw [h]; decide)]
    exact neg_one_div_zero

/-- `y0` of a NaN, of `-∞`, and of a negative argument other than `-0` is the canonical NaN. -/
theorem y0_nan (x : Float)
    (h : Wasm.IEEE64.isNaN x.toBits = true ∨
      (Wasm.IEEE64.sign x.toBits = true ∧ x.toBits ≠ 0x8000000000000000)) :
    (Bessel.y0 x).toBits = Wasm.IEEE64.canonicalNaN := by
  unfold Bessel.y0 Bessel.y0With
  dsimp only
  have key : Wasm.IEEE64.isNaN x.toBits = true ∨ x.toBits = 0xFFF0000000000000 ∨
      (Finite x.toBits ∧ ¬ x.toBits.toNat % 2 ^ 63 = 0 ∧ 2 ^ 63 ≤ x.toBits.toNat) := by
    rcases h with h | ⟨hs, hz⟩
    · exact Or.inl h
    · rcases negative_cases _ hs hz with h1 | h1 | ⟨h1, h2⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1
      · simp only [Wasm.IEEE64.sign, decide_eq_true_eq] at hs
        exact Or.inr (Or.inr ⟨h1, h2, hs⟩)
  rcases key with h | h | ⟨hf, hz, hs⟩
  · rw [ite_eq_left ((nonfinite_guard _).mpr (nan_not_finite _ h))]
    exact recip_nan x h
  · rw [ite_eq_left (show x.toBits >>> 32 &&& 0x7fffffff ≥ 0x7ff00000 by rw [h]; decide)]
    exact recip_neg_infinity x h
  · rw [ite_eq_right (fun hc => (nonfinite_guard _).mp hc hf), double_zero, decide_eq_false hz,
      ite_eq_right Bool.false_ne_true, sign_bit, decide_eq_true hs, ite_eq_left rfl]
    exact zero_div_zero

/-- `y1 (+∞) = +0`. -/
theorem y1_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Bessel.y1 x).toBits = 0 := by
  unfold Bessel.y1 Bessel.y1With
  dsimp only
  rw [ite_eq_left (show x.toBits >>> 32 &&& 0x7fffffff ≥ 0x7ff00000 by rw [h]; decide)]
  exact recip_pos_infinity x h

/-- `y1 (±0) = -∞`. -/
theorem y1_zero (x : Float) (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    (Bessel.y1 x).toBits = 0xFFF0000000000000 := by
  unfold Bessel.y1 Bessel.y1With
  dsimp only
  rcases h with h | h <;>
  · rw [ite_eq_right (show ¬ x.toBits >>> 32 &&& 0x7fffffff ≥ 0x7ff00000 by rw [h]; decide),
      ite_eq_left (show (x.toBits <<< 1 == 0) = true by rw [h]; decide)]
    exact neg_one_div_zero

/-- `y1` of a NaN, of `-∞`, and of a negative argument other than `-0` is the canonical NaN. -/
theorem y1_nan (x : Float)
    (h : Wasm.IEEE64.isNaN x.toBits = true ∨
      (Wasm.IEEE64.sign x.toBits = true ∧ x.toBits ≠ 0x8000000000000000)) :
    (Bessel.y1 x).toBits = Wasm.IEEE64.canonicalNaN := by
  unfold Bessel.y1 Bessel.y1With
  dsimp only
  have key : Wasm.IEEE64.isNaN x.toBits = true ∨ x.toBits = 0xFFF0000000000000 ∨
      (Finite x.toBits ∧ ¬ x.toBits.toNat % 2 ^ 63 = 0 ∧ 2 ^ 63 ≤ x.toBits.toNat) := by
    rcases h with h | ⟨hs, hz⟩
    · exact Or.inl h
    · rcases negative_cases _ hs hz with h1 | h1 | ⟨h1, h2⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1
      · simp only [Wasm.IEEE64.sign, decide_eq_true_eq] at hs
        exact Or.inr (Or.inr ⟨h1, h2, hs⟩)
  rcases key with h | h | ⟨hf, hz, hs⟩
  · rw [ite_eq_left ((nonfinite_guard _).mpr (nan_not_finite _ h))]
    exact recip_nan x h
  · rw [ite_eq_left (show x.toBits >>> 32 &&& 0x7fffffff ≥ 0x7ff00000 by rw [h]; decide)]
    exact recip_neg_infinity x h
  · rw [ite_eq_right (fun hc => (nonfinite_guard _).mp hc hf), double_zero, decide_eq_false hz,
      ite_eq_right Bool.false_ne_true, sign_bit, decide_eq_true hs, ite_eq_left rfl]
    exact zero_div_zero

#print axioms double_zero
#print axioms sign_bit
#print axioms nonfinite_guard
#print axioms negative_cases
#print axioms j0_infinity
#print axioms j0_nan
#print axioms j1_pos_infinity
#print axioms j1_neg_infinity
#print axioms j1_nan
#print axioms y0_pos_infinity
#print axioms y0_zero
#print axioms y0_nan
#print axioms y1_pos_infinity
#print axioms y1_zero
#print axioms y1_nan

end Library.Numerics.Float64.Bessel.BesselSpecial
