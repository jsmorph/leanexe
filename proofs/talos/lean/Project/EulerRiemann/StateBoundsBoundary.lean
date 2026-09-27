import Project.EulerRiemann.NumericsFluxBounds

namespace Project.EulerRiemann.StateBoundsBoundary
open CodeLib.IEEE64
open Numerics

def density : UInt64 := 0x3FC0000000000000
def energy : UInt64 := 0x3FF0000000000000
def momentum (i : Fin 3) : UInt64 := ![0xBFC0000000000000, 0, 0x3FC0000000000000] i
def trial := cellCheckedBits 0x3FB0000000000000
  density (momentum 0) 0 energy
  density (momentum 1) 0 energy
  density (momentum 2) 0 energy

set_option exponentiation.threshold 4096 in
theorem input_bounds (i : Fin 3) : StateBounds 8 density (momentum i) 0 energy := by
  have hd : value density = 1 / 8 := by
    change ((2^1071 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 8
    norm_num
  have he : value energy = 1 := by
    change ((2^1074 : Nat) : ℝ) / (2 : ℝ)^1074 = 1
    norm_num
  have hz : value 0 = 0 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
  have hm : value (momentum i) = ![-(1 / 8 : ℝ), 0, 1 / 8] i := by
    fin_cases i
    · have hs : Wasm.IEEE64.scaledValue (momentum 0) = -(2^1071 : Int) := by decide +kernel
      change value (momentum 0) = -(1 / 8)
      rw [value, hs]
      norm_num
    · exact hz
    · exact hd
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_,
    by unfold CodeLib.IEEE64.Finite; decide +kernel,
    by unfold CodeLib.IEEE64.Finite; decide +kernel,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> unfold CodeLib.IEEE64.Finite <;> decide +kernel
  · norm_num [hd]
  · norm_num [hd]
  · rw [hm]; fin_cases i <;> norm_num
  · rw [hz]; norm_num
  · rw [he]; norm_num
  · rw [hd, he, hz, hm]; fin_cases i <;> norm_num [arithmeticEpsilon]
  · fin_cases i <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem accepted_update : trial.status = 0 ∧ trial.density = 0x3FBE000000000000 := by
  decide +kernel

set_option exponentiation.threshold 4096 in
theorem output_outside_bounds :
    ¬ StateBounds 8 trial.density trial.momentum trial.transverse trial.energy := by
  intro h
  have hd := h.densityLower
  rw [accepted_update.2] at hd
  have hv : value 0x3FBE000000000000 = 15 / 128 := by
    change ((15 * 2^1067 : Nat) : ℝ) / (2 : ℝ)^1074 = 15 / 128
    norm_num
  rw [hv] at hd
  norm_num at hd

#print axioms input_bounds
#print axioms accepted_update
#print axioms output_outside_bounds
end Project.EulerRiemann.StateBoundsBoundary
