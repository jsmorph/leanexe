import Project.EulerRiemann.NumericsTransport
import Project.ProofKit.RealHalfSumError

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds

set_option exponentiation.threshold 4096

theorem internal_error (rho mx my energy : UInt64)
    (hr : Finite rho) (hx : Finite mx) (hy : Finite my) (he : Finite energy)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : 1 / M ≤ value rho) (bx : |value mx| ≤ M)
    (byy : |value my| ≤ M) (be : |value energy| ≤ M) :
    let u := Wasm.IEEE64.div mx rho
    let v := Wasm.IEEE64.div my rho
    let tx := Wasm.IEEE64.mul mx u
    let ty := Wasm.IEEE64.mul my v
    let sum := Wasm.IEEE64.add tx ty
    let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 sum
    let internal := Wasm.IEEE64.sub energy kinetic
    Finite u ∧ Finite v ∧ Finite tx ∧ Finite ty ∧ Finite sum ∧ Finite kinetic ∧ Finite internal ∧
    |value internal - (value energy - ((value mx)^2 + (value my)^2) / (2 * value rho))| ≤
      12 * arithmeticEpsilon * M^3 ∧
    |value internal| ≤ 5 * M^3 := by
  obtain ⟨hu, htx, _, _, etx, btx⟩ := transport_error rho mx hr hx M hM hMmax br bx
  obtain ⟨hv, hty, _, _, ety, bty⟩ := transport_error rho my hr hy M hM hMmax br byy
  let tx := Wasm.IEEE64.mul mx (Wasm.IEEE64.div mx rho)
  let ty := Wasm.IEEE64.mul my (Wasm.IEEE64.div my rho)
  let sum := Wasm.IEEE64.add tx ty
  let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 sum
  let internal := Wasm.IEEE64.sub energy kinetic
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM3 : 1 ≤ M^3 := one_le_pow₀ hM
  have hMle3 : M ≤ M^3 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) hMpos.le
    nlinarith only [h]
  have heps := mul_le_mul_of_nonneg_right epsilon_small.le (by positivity : 0 ≤ M^3)
  have hmax : 16 * M^3 < (2 : ℝ)^1022 := by
    calc
      16 * M^3 ≤ 16 * ((2 : ℝ)^100)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 3) (by norm_num)
      _ < (2 : ℝ)^1022 := by norm_num
  have hmaxAdd : 16 * M^3 < (2 : ℝ)^1023 := hmax.trans (by norm_num)
  have bsum : |value tx + value ty| ≤ 4 * M^3 := by
    have ht := abs_add_le (value tx) (value ty)
    change |value tx| ≤ 2 * M^3 at btx
    change |value ty| ≤ 2 * M^3 at bty
    linarith only [ht, btx, bty]
  obtain ⟨hsum, esum⟩ := add_error tx ty htx hty (4 * M^3)
    (by linarith only [hM3]) (by linarith only [hmaxAdd, hM3]) bsum
  have bsumRounded : |value sum| ≤ 5 * M^3 := by
    have h := magnitude_of_error _ _ _ _ esum bsum
    change |value sum| ≤ 4 * M^3 + arithmeticEpsilon * (4 * M^3) at h
    nlinarith only [h, heps, hM3]
  have hhalf : Finite 0x3FE0000000000000 := by unfold CodeLib.IEEE64.Finite; decide
  have vhalf : value 0x3FE0000000000000 = 1 / 2 := by
    change ((2^1073 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 2
    norm_num
  have bhalf : |value 0x3FE0000000000000 * value sum| ≤ 3 * M^3 := by
    rw [abs_mul, vhalf]
    norm_num
    linarith only [bsumRounded, hM3]
  obtain ⟨hkin, ekin⟩ := mul_error 0x3FE0000000000000 sum hhalf hsum (3 * M^3)
    (by linarith only [hM3]) (by linarith only [hmax, hM3]) bhalf
  have bkin : |value kinetic| ≤ 3 * M^3 := by
    have h := magnitude_of_error _ _ _ _ ekin (by
      rw [vhalf, abs_mul]
      norm_num
      linarith only [bsumRounded] : |value 0x3FE0000000000000 * value sum| ≤ (5 / 2) * M^3)
    change |value kinetic| ≤ (5 / 2) * M^3 + arithmeticEpsilon * (3 * M^3) at h
    nlinarith only [h, heps, hM3]
  have bsub : |value energy - value kinetic| ≤ 4 * M^3 := by
    have ht := abs_add_le (value energy) (-value kinetic)
    rw [abs_neg, ← sub_eq_add_neg] at ht
    linarith only [ht, be, bkin, hMle3]
  obtain ⟨hint, eint⟩ := sub_error energy kinetic he hkin (4 * M^3)
    (by linarith only [hM3]) (by linarith only [hmaxAdd, hM3]) bsub
  have bint : |value internal| ≤ 5 * M^3 := by
    have h := magnitude_of_error _ _ _ _ eint bsub
    change |value internal| ≤ 4 * M^3 + arithmeticEpsilon * (4 * M^3) at h
    nlinarith only [h, heps, hM3]
  refine ⟨hu, hv, htx, hty, hsum, hkin, hint, ?_, bint⟩
  change |value tx - (value mx)^2 / value rho| ≤ 3 * arithmeticEpsilon * M^3 at etx
  change |value ty - (value my)^2 / value rho| ≤ 3 * arithmeticEpsilon * M^3 at ety
  change |value sum - (value tx + value ty)| ≤ arithmeticEpsilon * (4 * M^3) at esum
  change |value kinetic - value 0x3FE0000000000000 * value sum| ≤
    arithmeticEpsilon * (3 * M^3) at ekin
  rw [vhalf] at ekin
  change |value internal - (value energy - value kinetic)| ≤ arithmeticEpsilon * (4 * M^3) at eint
  have ecombined : ((value mx)^2 + (value my)^2) / (2 * value rho) =
      ((value mx)^2 / value rho + (value my)^2 / value rho) / 2 := by ring
  rw [ecombined]
  have ep := Project.ProofKit.RealHalfSumError.subtract_half_sum _ _ _ _ _ _ _ _ _ _ _ _ _
    etx ety esum (by simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using ekin) eint
  exact ep.trans_eq (by ring)

#print axioms internal_error
end Project.EulerRiemann.Numerics
