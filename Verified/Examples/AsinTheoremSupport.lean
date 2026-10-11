import Verified.Examples.Asin
import Verified.Examples.AsinKernelPoly
import Verified.Examples.Log1pTheoremReduce
import LeanExe.ProofKit.F64ExactProduct

/-!
Word facts for `Asin.asin` and `Asin.acos`.  Clearing the low 32 bits of a positive normal word
`s` gives a word `w` with the same exponent field, `s - w < 2 ^ -20 s`, and a significand of at
most 21 bits, so `w * w` is exact.  `poly_bound` reads a bound on a polynomial over an interval
from `PolyBound.check`, which the kernel decides.
-/

namespace Verified.Examples.AsinTheoremSupport
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound

set_option exponentiation.threshold 4096

theorem and_high32 (T : Nat) (hT : T < 2 ^ 64) :
    T &&& 0xFFFFFFFF00000000 = T / 2 ^ 32 * 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hm : (0xFFFFFFFF00000000 : Nat) = (2 ^ 32 - 1) * 2 ^ 32 := by norm_num
  rw [Nat.testBit_and, hm, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hj : 32 ≤ j
  · have he : j - 32 + 32 = j := by omega
    rw [he]
    by_cases hj2 : j < 64
    · simp [hj, show j - 32 < 32 by omega]
    · have h1 : T.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h1]
  · simp [hj]

/-- The word of `s` with its low 32 bits cleared. -/
theorem trunc_facts (s : UInt64) (hs : 0 < value s) (hsf : Finite s)
    (he : 506 ≤ Wasm.IEEE64.exponent s) :
    Finite (s &&& 0xFFFFFFFF00000000) ∧
      value (s &&& 0xFFFFFFFF00000000) ≤ value s ∧
      value s - value (s &&& 0xFFFFFFFF00000000) ≤ value s / 2 ^ 20 ∧
      ∃ q : ℕ, q < 2 ^ 21 ∧ Wasm.IEEE64.scaledMagnitude (s &&& 0xFFFFFFFF00000000) =
        q * 2 ^ (Wasm.IEEE64.exponent s - 1 + 32) := by
  have hw63 := Log1pTheoremReduce.pos_word s hs
  have hst := s.toNat_lt
  have ht : (s &&& 0xFFFFFFFF00000000).toNat = s.toNat / 2 ^ 32 * 2 ^ 32 := by
    rw [UInt64.toNat_and, show (0xFFFFFFFF00000000 : UInt64).toNat = 0xFFFFFFFF00000000 from rfl,
      and_high32 _ hst]
  have hexp : Wasm.IEEE64.exponent s = s.toNat / 2 ^ 52 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  set e := s.toNat / 2 ^ 52 with he'
  set F := s.toNat % 2 ^ 52 with hF
  have he2 : e < 2047 := by
    have h := hsf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hexp, bne_iff_ne, ne_eq] at h
    omega
  rw [hexp] at he ⊢
  have hsv := Log1pTheoremReduce.value_fields s e F (by omega) he2 (by omega) (by omega)
  have htw := Log1pTheoremReduce.value_fields (s &&& 0xFFFFFFFF00000000) e (F / 2 ^ 32 * 2 ^ 32)
    (by omega) he2 (by omega) (by rw [ht]; omega)
  refine ⟨htw.1, ?_, ?_, ?_⟩
  · rw [hsv.2, htw.2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : (((F / 2 ^ 32 * 2 ^ 32 : ℕ)) : ℝ) ≤ F := by exact_mod_cast Nat.div_mul_le_self F _
    push_cast at this ⊢
    linarith
  · rw [hsv.2, htw.2]
    have h1 : ((F : ℕ) : ℝ) - ((F / 2 ^ 32 * 2 ^ 32 : ℕ) : ℝ) < 2 ^ 32 := by
      have : F - F / 2 ^ 32 * 2 ^ 32 < 2 ^ 32 := by omega
      have h2 : F / 2 ^ 32 * 2 ^ 32 ≤ F := Nat.div_mul_le_self F _
      have h3 : ((F - F / 2 ^ 32 * 2 ^ 32 : ℕ) : ℝ) < 2 ^ 32 := by exact_mod_cast this
      push_cast [h2] at h3
      exact h3
    have hp : (0 : ℝ) < 2 ^ (e - 1) := by positivity
    rw [div_sub_div_same, ← sub_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast at h1 ⊢
    nlinarith [(Nat.cast_nonneg F : (0 : ℝ) ≤ F)]
  · refine ⟨2 ^ 20 + F / 2 ^ 32, by omega, ?_⟩
    simp only [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, ht]
    have h1 : s.toNat / 2 ^ 32 * 2 ^ 32 / 2 ^ 52 % 2 ^ 11 = e := by omega
    have h2 : s.toNat / 2 ^ 32 * 2 ^ 32 % 2 ^ 52 = F / 2 ^ 32 * 2 ^ 32 := by omega
    have h3 : (e == 0) = false := by simp; omega
    rw [h1, h2, h3]
    simp only [Bool.false_eq_true, ite_false]
    rw [pow_add]
    ring

/-- A bound on a polynomial over an interval, checked by the kernel. -/
theorem poly_bound (cs : List ℚ) (lo hi M : ℚ) (d : ℕ) (h : check cs lo hi M d = true)
    (t : ℝ) (h1 : (lo : ℝ) ≤ t) (h2 : t ≤ (hi : ℝ)) : |eval cs t| ≤ (M : ℝ) :=
  check_sound cs lo hi M d h t h1 h2

theorem one_sapprox : FSApprox (1.0 : Float) 1 1 1 0 := by
  unfold FSApprox
  rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
  have hv : value 0x3FF0000000000000 = 1 := by
    rw [← ratOfWord_cast, show ratOfWord 0x3FF0000000000000 = 1 by decide +kernel]
    norm_num
  exact ⟨one_pos, le_rfl, by norm_num, by unfold CodeLib.IEEE64.Finite; decide +kernel,
    by rw [hv]; norm_num⟩

/-- A word below one in magnitude has exponent field at most 1022. -/
theorem exponent_lt_one (w : UInt64) (h : |value w| < 1) : Wasm.IEEE64.exponent w ≤ 1022 := by
  by_contra hc
  have := F64Magnitude.magnitude_ge w 1023 0 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [zpow_zero] at this
  linarith

#print axioms and_high32
#print axioms trunc_facts

end Verified.Examples.AsinTheoremSupport
