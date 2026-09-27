import Project.ExpArm.ShiftRounding
import Project.ExpArm.LogBounds
import Project.ProofKit.F64MulBounds

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

def reductionWord (x : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.mul 0x40671547652B82FE x) 0x4338000000000000

def reductionInteger (x : UInt64) : Int := shiftInteger (reductionWord x)

theorem inverse_log_bounds :
    184 < value 0x40671547652B82FE ∧ value 0x40671547652B82FE < 185 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem log_quotient_bounds : 0 ≤ Real.log 2/128 ∧ Real.log 2/128 ≤ 7/1280 := by
  have hl : 0 ≤ Real.log 2/128 := div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  refine ⟨hl, ?_⟩
  have hu := (abs_le.mp inverse_log_error).2
  have hc := inverse_log_bounds.1
  nlinarith

theorem inverse_product (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 1024) :
    Finite (Wasm.IEEE64.mul 0x40671547652B82FE x) ∧
    |value (Wasm.IEEE64.mul 0x40671547652B82FE x) - value 0x40671547652B82FE * value x| ≤
      1/(2 : ℝ)^35 ∧
    |value (Wasm.IEEE64.mul 0x40671547652B82FE x)| ≤ 190000 := by
  have hi : |value 0x40671547652B82FE| ≤ 185 := by
    rw [abs_of_pos (by linarith [inverse_log_bounds.1])]
    exact inverse_log_bounds.2.le
  have hp : |value 0x40671547652B82FE * value x| ≤ 185 * 1024 := by
    rw [abs_mul]
    exact mul_le_mul hi hx (abs_nonneg _) (by norm_num)
  have hm := F64MulBounds.mul_real_mixed 0x40671547652B82FE x (by rfl) hf
    (hp.trans_lt (by norm_num))
  have he : |value (Wasm.IEEE64.mul 0x40671547652B82FE x) -
      value 0x40671547652B82FE * value x| ≤ 1/(2 : ℝ)^35 := by
    refine hm.2.trans ?_
    calc
      _ ≤ unitRoundoff64 * (185*1024) + multiplicationUnderflowEpsilon := by
        gcongr
        norm_num [unitRoundoff64]
      _ ≤ _ := by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
  refine ⟨hm.1, he, ?_⟩
  have ht := abs_add_le
    (value (Wasm.IEEE64.mul 0x40671547652B82FE x) - value 0x40671547652B82FE * value x)
    (value 0x40671547652B82FE * value x)
  rw [sub_add_cancel] at ht
  linarith

theorem integer_selection (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 1024) :
    0x4330000000000000 ≤ reductionWord x ∧ reductionWord x < 0x4340000000000000 ∧
    Finite (Wasm.IEEE64.sub (reductionWord x) 0x4338000000000000) ∧
    value (Wasm.IEEE64.sub (reductionWord x) 0x4338000000000000) = (reductionInteger x : ℝ) ∧
    |(reductionInteger x : ℝ) - value 0x40671547652B82FE * value x| ≤ 1/2 + 1/(2 : ℝ)^35 := by
  have hp := inverse_product x hf hx
  have hs := shift_rounding _ hp.1 hp.2.2
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  have ht := abs_add_le
    ((reductionInteger x : ℝ) - value (Wasm.IEEE64.mul 0x40671547652B82FE x))
    (value (Wasm.IEEE64.mul 0x40671547652B82FE x) - value 0x40671547652B82FE * value x)
  rw [sub_add_sub_cancel] at ht
  exact ht.trans (add_le_add hs.2.2.2.2 hp.2.1)

theorem reductionInteger_abs (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 1024) :
    |(reductionInteger x : ℝ)| ≤ 185 * |value x| + 1 := by
  have he := (integer_selection x hf hx).2.2.2.2
  have hp : |value 0x40671547652B82FE * value x| ≤ 185 * |value x| := by
    rw [abs_mul, abs_of_pos (by linarith [inverse_log_bounds.1])]
    exact mul_le_mul_of_nonneg_right inverse_log_bounds.2.le (abs_nonneg _)
  have ht := abs_add_le
    ((reductionInteger x : ℝ) - value 0x40671547652B82FE * value x)
    (value 0x40671547652B82FE * value x)
  rw [sub_add_cancel] at ht
  linarith

theorem ideal_reduction_bound (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 1024) :
    |value x - (reductionInteger x : ℝ) * (Real.log 2/128)| ≤ 11/4000 := by
  let l := Real.log 2/128
  let i := value 0x40671547652B82FE
  let k := (reductionInteger x : ℝ)
  have h1 : |value x * (1-i*l)| ≤ 1024/(2 : ℝ)^55 := by
    rw [abs_mul, abs_sub_comm]
    calc
      _ ≤ 1024 * (1/(2 : ℝ)^55) :=
        mul_le_mul hx inverse_log_error (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have h2 : |(i*value x-k)*l| ≤ (1/2 + 1/(2 : ℝ)^35) * (7/1280) := by
    rw [abs_mul, abs_sub_comm, abs_of_nonneg log_quotient_bounds.1]
    exact mul_le_mul (integer_selection x hf hx).2.2.2.2 log_quotient_bounds.2
      log_quotient_bounds.1 (by positivity)
  have he : value x-k*l = value x*(1-i*l) + (i*value x-k)*l := by ring
  change |value x-k*l| ≤ _
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans (by norm_num))

#print axioms integer_selection
#print axioms ideal_reduction_bound
end Project.ExpArm
