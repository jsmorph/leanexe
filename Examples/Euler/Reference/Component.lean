import Examples.Euler.RealState
import LeanExe.ProofKit.F64ArithmeticBounds
import LeanExe.ProofKit.RealRusanovError

/-! One Rusanov flux component of the first-order solver against its exact formula.  For a positive
speed at most `32 M²`, side fluxes at most `15 M⁵`, and states at most `M` in magnitude,
`component` accepts, and its value is within `256 ε M⁵` of
`(fluxL + fluxR) / 2 - alpha · (stateR - stateL) / 2` on the inputs' values, where `ε = 2⁻⁵²`. -/

namespace Examples.Euler.Reference

open Examples.Euler LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite arithmeticEpsilon)
open LeanExe.ProofKit.F64ArithmeticBounds
open LeanExe.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem component_error (alpha fluxL fluxR stateL stateR : Float)
    (ha : positive alpha = true) (hfl : Finite fluxL.toBits) (hfr : Finite fluxR.toBits)
    (hsl : Finite stateL.toBits) (hsr : Finite stateR.toBits)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (ba : real alpha ≤ 32 * M^2) (bfl : |real fluxL| ≤ 15 * M^5)
    (bfr : |real fluxR| ≤ 15 * M^5) (bsl : |real stateL| ≤ M) (bsr : |real stateR| ≤ M) :
    let c := component alpha fluxL fluxR stateL stateR
    c.status = 0 ∧ Finite c.value.toBits ∧ |real c.value| ≤ 66 * M^5 ∧
      |real c.value - ((real fluxL + real fluxR) / 2 -
        real alpha * (real stateR - real stateL) / 2)| ≤ 256 * arithmeticEpsilon * M^5 := by
  simp only [real] at ba bfl bfr bsl bsr ⊢
  rw [positive_eq] at ha
  let sum := Wasm.IEEE64.add fluxL.toBits fluxR.toBits
  let mean := Wasm.IEEE64.mul 0x3FE0000000000000 sum
  let jump := Wasm.IEEE64.sub stateR.toBits stateL.toBits
  let viscosity := Wasm.IEEE64.mul alpha.toBits jump
  let halfViscosity := Wasm.IEEE64.mul 0x3FE0000000000000 viscosity
  let result := Wasm.IEEE64.sub mean halfViscosity
  have hp := positiveBits_spec alpha.toBits ha
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM3 : 1 ≤ M^3 := one_le_pow₀ hM
  have hM5 : 1 ≤ M^5 := one_le_pow₀ hM
  have hM13 : M ≤ M^3 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) hMpos.le
    nlinarith only [h]
  have hM35 : M^3 ≤ M^5 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) (pow_nonneg hMpos.le 3)
    nlinarith only [h]
  have hmax : 128 * M^5 < (2 : ℝ)^1022 := by
    calc
      _ ≤ 128 * ((2 : ℝ)^100)^5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 5) (by norm_num)
      _ < (2 : ℝ)^1022 := by norm_num
  have hmaxAdd : 128 * M^5 < (2 : ℝ)^1023 := hmax.trans (by norm_num)
  have heps1 := mul_le_mul_of_nonneg_right epsilon_small.le hMpos.le
  have heps3 := mul_le_mul_of_nonneg_right epsilon_small.le (pow_nonneg hMpos.le 3)
  have heps5 := mul_le_mul_of_nonneg_right epsilon_small.le (pow_nonneg hMpos.le 5)
  have hhalf : Finite 0x3FE0000000000000 := by unfold CodeLib.IEEE64.Finite; decide
  have vhalf : value 0x3FE0000000000000 = 1 / 2 := by
    change ((2^1073 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 2
    norm_num
  have bsum : |value fluxL.toBits + value fluxR.toBits| ≤ 30 * M^5 := by
    have h := abs_add_le (value fluxL.toBits) (value fluxR.toBits)
    linarith only [h, bfl, bfr]
  obtain ⟨hsum, esum⟩ := add_error fluxL.toBits fluxR.toBits hfl hfr (30 * M^5)
    (by linarith only [hM5]) (by linarith only [hmaxAdd, hM5]) bsum
  have bsumRounded : |value sum| ≤ 31 * M^5 := by
    have h := magnitude_of_error _ _ _ _ esum bsum
    change |value sum| ≤ 30 * M^5 + arithmeticEpsilon * (30 * M^5) at h
    nlinarith only [h, heps5, hM5]
  have bmean : |value 0x3FE0000000000000 * value sum| ≤ (31 / 2) * M^5 := by
    rw [abs_mul, vhalf]
    norm_num
    linarith only [bsumRounded]
  obtain ⟨hmean, emean⟩ := mul_error _ sum hhalf hsum (16 * M^5)
    (by linarith only [hM5]) (by linarith only [hmax, hM5])
    (by linarith only [bmean, hM5])
  have bmeanRounded : |value mean| ≤ 16 * M^5 := by
    have h := magnitude_of_error _ _ _ _ emean bmean
    change |value mean| ≤ (31 / 2) * M^5 + arithmeticEpsilon * (16 * M^5) at h
    nlinarith only [h, heps5, hM5]
  have bjump : |value stateR.toBits - value stateL.toBits| ≤ 2 * M := by
    have h := abs_sub (value stateR.toBits) (value stateL.toBits)
    linarith only [h, bsr, bsl]
  obtain ⟨hjump, ejump⟩ := sub_error stateR.toBits stateL.toBits hsr hsl (2 * M)
    (by linarith only [hM]) (by linarith only [hmaxAdd, hM13, hM35, hM]) bjump
  have bjumpRounded : |value jump| ≤ 3 * M := by
    have h := magnitude_of_error _ _ _ _ ejump bjump
    change |value jump| ≤ 2 * M + arithmeticEpsilon * (2 * M) at h
    nlinarith only [h, heps1, hM]
  have bvisc : |value alpha.toBits * value jump| ≤ 96 * M^3 := by
    rw [abs_mul, abs_of_pos hp.2]
    calc
      _ ≤ (32 * M^2) * (3 * M) := mul_le_mul ba bjumpRounded (abs_nonneg _) (by positivity)
      _ = 96 * M^3 := by ring
  obtain ⟨hvisc, evisc⟩ := mul_error alpha.toBits jump hp.1 hjump (96 * M^3)
    (by linarith only [hM3]) (by linarith only [hmax, hM35, hM3]) bvisc
  have bviscRounded : |value viscosity| ≤ 97 * M^3 := by
    have h := magnitude_of_error _ _ _ _ evisc bvisc
    change |value viscosity| ≤ 96 * M^3 + arithmeticEpsilon * (96 * M^3) at h
    nlinarith only [h, heps3, hM3]
  have bhalf : |value 0x3FE0000000000000 * value viscosity| ≤ (97 / 2) * M^3 := by
    rw [abs_mul, vhalf]
    norm_num
    linarith only [bviscRounded]
  obtain ⟨hhalfVisc, ehalf⟩ := mul_error _ viscosity hhalf hvisc (49 * M^3)
    (by linarith only [hM3]) (by linarith only [hmax, hM35, hM3])
    (by linarith only [bhalf, hM3])
  have bhalfRounded : |value halfViscosity| ≤ 49 * M^3 := by
    have h := magnitude_of_error _ _ _ _ ehalf bhalf
    change |value halfViscosity| ≤ (97 / 2) * M^3 + arithmeticEpsilon * (49 * M^3) at h
    nlinarith only [h, heps3, hM3]
  have bresult : |value mean - value halfViscosity| ≤ 65 * M^5 := by
    have h := abs_sub (value mean) (value halfViscosity)
    linarith only [h, bmeanRounded, bhalfRounded, hM35]
  obtain ⟨hresult, eresult⟩ := sub_error mean halfViscosity hmean hhalfVisc (65 * M^5)
    (by linarith only [hM5]) (by linarith only [hmaxAdd, hM5]) bresult
  have bresultRounded : |value result| ≤ 66 * M^5 := by
    have h := magnitude_of_error _ _ _ _ eresult bresult
    change |value result| ≤ 65 * M^5 + arithmeticEpsilon * (65 * M^5) at h
    nlinarith only [h, heps5, hM5]
  have hBits : ∀ x : Float, finite x = finiteBits x.toBits := fun _ => rfl
  have hc : component alpha fluxL fluxR stateL stateR =
      ⟨0, 0.5 * (fluxL + fluxR) - 0.5 * (alpha * (stateR - stateL))⟩ := by
    unfold component
    dsimp only
    split
    · rfl
    · rename_i hNot
      exfalso
      apply hNot
      simp (config := { zetaDelta := true }) only [hBits, positive_eq, F64Bits.toBits_mul,
        F64Bits.toBits_add, F64Bits.toBits_sub, half_toBits, ha, (finiteBits_iff _).mpr hfl,
        (finiteBits_iff _).mpr hfr, (finiteBits_iff _).mpr hsl, (finiteBits_iff _).mpr hsr,
        (finiteBits_iff _).mpr hsum, (finiteBits_iff _).mpr hmean, (finiteBits_iff _).mpr hjump,
        (finiteBits_iff _).mpr hvisc, (finiteBits_iff _).mpr hhalfVisc,
        (finiteBits_iff _).mpr hresult, Bool.and_self]
  rw [hc]
  simp (config := { zetaDelta := true }) only [F64Bits.toBits_mul, F64Bits.toBits_add,
    F64Bits.toBits_sub, half_toBits]
  refine ⟨trivial, hresult, bresultRounded, ?_⟩
  rw [vhalf] at emean ehalf
  have eall := RealRusanovError.component _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp.2.le
    esum (by simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using emean) ejump evisc
    (by simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using ehalf) eresult
  have haError := mul_le_mul_of_nonneg_right ba (mul_nonneg epsilon_pos.le hMpos.le)
  have h35 := mul_le_mul_of_nonneg_left hM35 epsilon_pos.le
  have he5 := mul_pos epsilon_pos (pow_pos hMpos 5)
  exact eall.trans (by nlinarith only [haError, h35, he5])

end Examples.Euler.Reference
