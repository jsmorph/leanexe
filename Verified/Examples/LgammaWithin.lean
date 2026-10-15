import Verified.Examples.LgammaEnds
import Verified.Examples.LgammaAccPath
import Verified.Examples.LgammaBounds
import Verified.Examples.LgammaFacts
import Verified.Examples.LgammaSign
import Verified.Examples.FmaSpecTheorem

/-!
**`lgamma` within one step up to `2^800`**: `(Lgamma.lgammaR x).1` lies within one step of the
nearest-even rounding of `ln |Γ x|` at every finite `x` with `|x| ≤ 2^800` other than 0 and the
negative integers (`lgamma_within_800`), with no hypothesis.  At 1 and 2 the code returns 0
(`LgammaSpecial.lgamma_unit_steps`).  At the 14 ends of the accurate path's windows the fast path's
rounding test passes (`LgammaEnds.fast_ends`).  At every other input the fast result is within one
step when the code takes it (`LgammaFastWalk.fast_within`), and the accurate path is within one
step (`LgammaAccPath.accurate_within`) with the bounds of `LgammaBounds.lgamma_bounds`.
`LgammaFacts.allFacts` proves the approximation facts and `FmaSpecTheorem.fma_nearest` the
specification of the fused multiply-add.
-/

namespace Verified.Examples.LgammaWithin
open CodeLib.IEEE64 LeanExe.ProofKit Lgamma LgammaSpecial
open Verified.Examples.Tgamma (floorF)

set_option exponentiation.threshold 4096

/-- **`lgamma` within one step** at every finite `x` with `|x| ≤ 2^800` other than 0 and the
negative integers. -/
theorem lgamma_within_800 (x : Float) (hf : Finite x.toBits)
    (hp : ∀ n : ℤ, value x.toBits = n → 0 < n) (h800 : |value x.toBits| ≤ 2 ^ 800) :
    F64SignedRounding.WithinSteps 1 (Real.log (Real.Gamma (value x.toBits)))
      (lgammaR x).1.toBits := by
  obtain ⟨hSm, hPF, hSF, hL, hS, hAP, hAF, hLA, hSA, hRF, hRM, hDb, hCF⟩ := LgammaFacts.allFacts
  have hF := FmaSpecTheorem.fma_nearest
  set v := value x.toBits with hv
  -- the magnitude test
  have hlim : x.toBits.toNat % 2 ^ 63 < 0x7F5754D9278B51A6 := by
    have habs : value (Wasm.IEEE64.abs x.toBits) ≤ value (0x71F0000000000000 : UInt64) := by
      rw [F64UpperWord.value_abs, LgammaFastWalk.w800]
      exact h800
    rw [F64PositiveOrder.value_le_iff (by rw [F64UpperWord.abs_toNat]; omega) (by decide),
      F64UpperWord.abs_toNat] at habs
    simp only [UInt64.reduceToNat] at habs
    omega
  have h1 : ¬ x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C := fun h => by
    have := (big_test _).mp h; omega
  have hv0 : v ≠ 0 := fun h => by
    have := hp 0 (by rw [h]; simp)
    omega
  have hlarge : |v| < 2 ^ 52 ∨ 0 < v := by
    by_cases hl : 2 ^ 52 ≤ |v|
    · obtain ⟨N, hN⟩ := TgammaFloor.int_of_large x.toBits hf hl
      have := hp N hN
      right; rw [hv, hN]; exact_mod_cast this
    · left; exact lt_of_not_ge hl
  have h2 : ¬ (floorF x == x && x ≤ 0.0) = true := by
    rw [Bool.and_eq_true, decide_eq_true_iff, float_le_iff _ _ hf zero_finite,
      TgammaSpecial.zero_bits, F64Magnitude.value_zero]
    rintro ⟨hb, hle⟩
    rcases hlarge with hl | hl
    · obtain ⟨hff, hfv⟩ := TgammaFloor.floorF_spec x hf hl
      rw [F64UpperWord.float_beq_iff _ _ hff hf, hfv] at hb
      have hk := hp _ hb.symm
      have : ((⌊value x.toBits⌋ : ℤ) : ℝ) ≤ 0 := by rw [hb]; exact hle
      have : ⌊value x.toBits⌋ ≤ 0 := by exact_mod_cast this
      omega
    · exact absurd hle (not_le.mpr hl)
  by_cases hu : v = 1 ∨ v = 2
  · have h := lgamma_unit_steps Tgamma.logdTable logAccurateTable sinpiTable asymTable
      accurateTable dbTable mainTable x hf hu
    rw [log_abs_gamma] at h
    exact ⟨h.1, h.2.trans (by norm_num)⟩
  push Not at hu
  obtain ⟨hv1, hv2⟩ := hu
  have h3 : ¬ (floorF x == x && (x == 1.0 || x == 2.0)) = true := by
    rw [Bool.and_eq_true, Bool.or_eq_true, F64UpperWord.float_beq_iff _ _ hf one_finite,
      F64UpperWord.float_beq_iff _ _ hf two_finite, one_value, two_value]
    rintro ⟨-, h | h⟩
    · exact hv1 h
    · exact hv2 h
  have hint : v < 0 → ∀ n : ℤ, v ≠ n := by
    intro hneg n hn
    have := hp n hn
    have : (0 : ℝ) < n := by exact_mod_cast this
    linarith
  by_cases hk : ∃ k : ℕ, k < 7 ∧ |v| = (2 * k + 1) / 4
  · exact LgammaEnds.fast_ends hF hL hS hPF hAP x hf hk h1 h2 h3
  push Not at hk
  have hb := LgammaBounds.lgamma_bounds hRM hCF x.toBits hf hint hv0 hv1 hv2 h800
  exact LgammaFastWalk.fast_within hF hL hS hPF hSF hSm x hf hv0 hv1 hv2 hint h800 h1 h2 h3
    (LgammaAccPath.accurate_within hF hS hSA hLA hAP hAF hCF hRF hRM hDb x hf hint hv0 hv1 hv2
      h800 hk hb.1 hb.2)

#print axioms lgamma_within_800

end Verified.Examples.LgammaWithin
