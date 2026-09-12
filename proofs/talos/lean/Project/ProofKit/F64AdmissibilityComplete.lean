import Project.ProofKit.F64Admissibility
import Project.ProofKit.F64OrderComplete

namespace Project.ProofKit.F64Admissibility
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64Normalize

set_option exponentiation.threshold 4096 in
theorem residual_accepts_of_margin (rho mx my energy : UInt64)
    (hr : Finite rho) (hx : Finite mx) (hy : Finite my) (he : Finite energy)
    (br : |value rho| ≤ 1 / 2) (bx : |value mx| ≤ 1 / 2)
    (byy : |value my| ≤ 1 / 2) (be : |value energy| ≤ 1 / 2)
    (hMargin : 13 * arithmeticEpsilon <
      value rho * value energy - ((value mx)^2 + (value my)^2) / 2) :
    positiveBits (F64InternalEnergy.residual rho mx my energy) = true ∧
      (0x3CE0000000000000 : UInt64) < F64InternalEnergy.residual rho mx my energy := by
  obtain ⟨hf, hError⟩ := F64InternalEnergy.residual_error rho mx my energy
    hr hx hy he br bx byy be
  have hLower : 8 * arithmeticEpsilon < value (F64InternalEnergy.residual rho mx my energy) := by
    have hErrorLower := (abs_le.mp hError).1
    linarith
  have hPositive := positiveBits_of_finite_value_pos _ hf
    (lt_trans (by norm_num [arithmeticEpsilon]) hLower)
  refine ⟨hPositive, (positive_word_lt_iff _ _ (by decide) hPositive).mpr ?_⟩
  have hThreshold : value 0x3CE0000000000000 = 8 * arithmeticEpsilon := by
    change ((2^1025 : Nat) : ℝ) / (2 : ℝ)^1074 = 8 * (1 / (2 : ℝ)^52)
    norm_num
  rwa [hThreshold]

theorem checked_of_normalized_margin (rho mx my energy : UInt64)
    (hr : positiveBits rho = true) (hx : finiteBits mx = true)
    (hy : finiteBits my = true) (he : positiveBits energy = true)
    (nr : normalizable rho (topExponent rho mx my energy) = true)
    (nx : normalizable mx (topExponent rho mx my energy) = true)
    (ny : normalizable my (topExponent rho mx my energy) = true)
    (ne : normalizable energy (topExponent rho mx my energy) = true)
    (hMargin : let top := topExponent rho mx my energy
      13 * arithmeticEpsilon <
        value (normalizedMagnitude rho top) * value (normalizedMagnitude energy top) -
        ((value (normalizedMagnitude mx top))^2 +
          (value (normalizedMagnitude my top))^2) / 2) :
    checked rho mx my energy = true := by
  let top := topExponent rho mx my energy
  have hr' := (positiveBits_spec rho hr).1
  have hx' := (finiteBits_iff mx).mp hx
  have hy' := (finiteBits_iff my).mp hy
  have he' := (positiveBits_spec energy he).1
  have ht_eq : top.toNat = max (max (Wasm.IEEE64.exponent rho) (Wasm.IEEE64.exponent mx))
      (max (Wasm.IEEE64.exponent my) (Wasm.IEEE64.exponent energy)) := by
    simp only [top, topExponent, maxWord_toNat, exponentBits_toNat]
  have ht : top.toNat ≤ 2046 := by
    rw [ht_eq]
    exact max_le (max_le (finite_exponent_bound rho hr') (finite_exponent_bound mx hx'))
      (max_le (finite_exponent_bound my hy') (finite_exponent_bound energy he'))
  have sr := normalizedMagnitude_spec rho top ht
    (by rw [ht_eq]; exact (le_max_left _ _).trans (le_max_left _ _))
    (normalizable_spec rho top hr' nr)
  have sx := normalizedMagnitude_spec mx top ht
    (by rw [ht_eq]; exact (le_max_right _ _).trans (le_max_left _ _))
    (normalizable_spec mx top hx' nx)
  have sy := normalizedMagnitude_spec my top ht
    (by rw [ht_eq]; exact (le_max_left _ _).trans (le_max_right _ _))
    (normalizable_spec my top hy' ny)
  have se := normalizedMagnitude_spec energy top ht
    (by rw [ht_eq]; exact (le_max_right _ _).trans (le_max_right _ _))
    (normalizable_spec energy top he' ne)
  have hAccept := residual_accepts_of_margin _ _ _ _ sr.1 sx.1 sy.1 se.1
    sr.2.1 sx.2.1 sy.2.1 se.2.1 hMargin
  simpa only [checked, hr, hx, hy, he, Bool.and_self, ite_true, nr, nx, ny, ne,
    Bool.and_eq_true_iff, decide_eq_true_eq] using hAccept

#print axioms residual_accepts_of_margin
#print axioms checked_of_normalized_margin
end Project.ProofKit.F64Admissibility
