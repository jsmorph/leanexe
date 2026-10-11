import Verified.Examples.AtanTheorem
import LeanExe.ProofKit.F64WithinZero

/-!
The exceptional inputs of `Atan.atan` as words: `±0` give `±0`, `±∞` give `±(atanhi3 + atanlo3)`,
which is the nearest-even reference of `±π/2` (`WithinSteps 0`), and NaN gives the canonical NaN.
-/

namespace Verified.Examples.AtanTheoremSpecial
open CodeLib.IEEE64 LeanExe.ProofKit AtanTheoremBranches AtanTheorem

set_option exponentiation.threshold 4096

theorem atan_huge_eq (x : Float) (h1 : ixOf x ≥ 0x44100000) :
    Atan.atan x =
      if ixOf x > 0x7ff00000 || (ixOf x == 0x7ff00000 && x.toBits &&& 0xFFFFFFFF != 0) then x + x
      else if x.toBits >>> 32 >>> 31 == 1 then
        -Float.ofBits 0x3FF921FB54442D18 - Float.ofBits 0x3C91A62633145C07
      else Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x3C91A62633145C07 := by
  unfold ixOf at *
  simp only [Atan.atan, h1, ite_true]

theorem half_pi_ref : F64SignedRounding.WithinSteps 0 (Real.pi / 2) 0x3FF921FB54442D18 := by
  have h := big_close
  refine F64WithinZero.within_zero_of_close _ _ (by unfold CodeLib.IEEE64.Finite; decide) 1023
    (by norm_num) (by decide) (by decide) (lt_of_le_of_lt h (by norm_num)) ?_
  rw [abs_of_pos (by positivity)]
  have := Real.pi_lt_four
  linarith [(by norm_num : (2 : ℝ) < 2 ^ 1023)]

theorem atan_pos_inf (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Atan.atan x).toBits = 0x3FF921FB54442D18 ∧
      F64SignedRounding.WithinSteps 0 (Real.pi / 2) (Atan.atan x).toBits := by
  have he : (Atan.atan x).toBits = 0x3FF921FB54442D18 := by
    rw [atan_huge_eq x (by simp only [ixOf, h]; decide), if_neg (by simp only [ixOf, h]; decide),
      if_neg (by rw [h]; decide), big_bits]
  exact ⟨he, by rw [he]; exact half_pi_ref⟩

theorem atan_neg_inf (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (Atan.atan x).toBits = 0xBFF921FB54442D18 ∧
      F64SignedRounding.WithinSteps 0 (-(Real.pi / 2)) (Atan.atan x).toBits := by
  have he : (Atan.atan x).toBits = 0xBFF921FB54442D18 := by
    rw [atan_huge_eq x (by simp only [ixOf, h]; decide), if_neg (by simp only [ixOf, h]; decide),
      if_pos (by rw [h]; decide), big_neg_bits]
    decide
  refine ⟨he, ?_⟩
  rw [he, show (0xBFF921FB54442D18 : UInt64) = Wasm.IEEE64.negate 0x3FF921FB54442D18 by decide]
  exact (F64SignedRounding.within_negate 0 (Real.pi / 2) _).mpr half_pi_ref

theorem atan_zero (x : Float) (h : x.toBits = 0) : (Atan.atan x).toBits = 0 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  rw [AtanTheoremBranches.atan_tiny_eq x (by simp only [ixOf, h]; decide)
    (huge_gt x hx (by rw [h, F64Magnitude.value_zero, abs_zero]; norm_num)), h]

theorem atan_neg_zero (x : Float) (h : x.toBits = 0x8000000000000000) :
    (Atan.atan x).toBits = 0x8000000000000000 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value (0x8000000000000000 : UInt64) = 0 := by
    rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x8000000000000000 = 0 by
      decide +kernel]
    norm_num
  rw [AtanTheoremBranches.atan_tiny_eq x (by simp only [ixOf, h]; decide)
    (huge_gt x hx (by rw [h, hv, abs_zero]; norm_num)), h]

theorem atan_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Atan.atan x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hN := x.toBits.toNat_lt
  have hb : x.toBits.toNat % 2 ^ 63 / 2 ^ 52 = 2047 ∧ x.toBits.toNat % 2 ^ 52 ≠ 0 := by
    simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at h
    omega
  have hix := F64UpperWord.high_toNat x.toBits
  have hlow : (x.toBits &&& 0xFFFFFFFF).toNat = x.toBits.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have h1 : ixOf x ≥ 0x44100000 := by
    rw [ge_iff_le, UInt64.le_iff_toNat_le]
    unfold ixOf
    rw [hix]
    simp
    omega
  have h2 : (ixOf x > 0x7ff00000 || (ixOf x == 0x7ff00000 && x.toBits &&& 0xFFFFFFFF != 0)) =
      true := by
    unfold ixOf
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, hix, hlow,
      UInt64.reduceToNat]
    omega
  rw [atan_huge_eq x h1, if_pos h2, F64Bits.toBits_add]
  simp only [Wasm.IEEE64.add, h, Bool.true_or, ite_true]

#print axioms atan_pos_inf
#print axioms atan_neg_inf
#print axioms atan_zero
#print axioms atan_neg_zero
#print axioms atan_nan

end Verified.Examples.AtanTheoremSpecial
