import Project.EulerRiemann.NumericsFluxBounds
import Project.EulerRiemann.NumericsPressureReference
import Project.EulerRiemann.NumericsSoundReference
import Project.EulerRiemann.NumericsSpeedReference
import Project.EulerRiemann.NumericsSideValues
import Project.EulerRiemann.RealSoundMargin

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds
open Project.ProofKit.F64Order

theorem side_speed_lower (rho mx my energy : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (h : StateBounds M rho mx my energy) :
    let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
    let c := Real.sqrt ((14 / 25) * (I / value rho))
    |value mx / value rho| + c / 2 ≤ value (sideCheckedBits rho mx my energy).speed := by
  let u := Wasm.IEEE64.div mx rho
  let tx := Wasm.IEEE64.mul mx u
  let ty := Wasm.IEEE64.mul my (Wasm.IEEE64.div my rho)
  let internal := Wasm.IEEE64.sub energy (Wasm.IEEE64.mul 0x3FE0000000000000 (Wasm.IEEE64.add tx ty))
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let sound := Wasm.IEEE64.sqrt (Wasm.IEEE64.mul 0x3FF6666666666666 (Wasm.IEEE64.div pressure rho))
  let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
  let c := Real.sqrt ((14 / 25) * (I / value rho))
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hrPos : 0 < value rho := lt_of_lt_of_le (by positivity) h.densityLower
  have hI : 0 < I := by
    have heM := mul_pos epsilon_pos (pow_pos hMpos 3)
    have hm := h.internalMargin
    change 24 * arithmeticEpsilon * M^3 ≤ I at hm
    linarith only [hm, heM]
  have hIM : I ≤ M := by
    have hk : 0 ≤ ((value mx)^2 + (value my)^2) / (2 * value rho) := by positivity
    have hE := (le_abs_self (value energy)).trans h.energyBound
    dsimp only [I]
    linarith only [hk, hE]
  have budget : arithmeticEpsilon * M^2 ≤ c / 16 :=
    RealSoundMargin.error_budget (value rho) I M arithmeticEpsilon hrPos hMpos epsilon_pos
      h.densityUpper hIM h.internalMargin
  obtain ⟨hu, _, _, _, _, _, hi, ei, bi⟩ := internal_error rho mx my energy
    h.finiteDensity h.finiteMomentum h.finiteTransverse h.finiteEnergy M hM hMmax
    h.densityLower h.momentumBound h.transverseBound h.energyBound
  obtain ⟨_, _, eu, bu, _, _⟩ := transport_error rho mx h.finiteDensity h.finiteMomentum
    M hM hMmax h.densityLower h.momentumBound
  obtain ⟨hpPos, bpLo, bpHi, _, hpLo, hpHi⟩ :=
    pressure_reference_error internal hi I M hM hMmax bi ei h.internalMargin
  have hp := (positiveBits_spec pressure hpPos).1
  obtain ⟨_, _, hs, bs, _⟩ := sound_error pressure rho hp h.finiteDensity M hM hMmax
    h.densityLower h.densityUpper bpLo bpHi
  have bsLo := sound_reference_lower pressure rho hp h.finiteDensity I M hI hM hMmax
    h.densityLower h.densityUpper bpLo bpHi hpLo
  have bsHi := sound_reference_upper pressure rho hp h.finiteDensity I M hI hM hMmax
    h.densityLower h.densityUpper bpLo bpHi hpHi
  have hspeed := speed_reference_lower u sound hu hs (value mx / value rho) c M
    (Real.sqrt_nonneg _) hM hMmax bu bs eu budget bsLo bsHi
  have hstatus := (side_accepted_of_bounds rho mx my energy h.finiteDensity h.finiteMomentum
    h.finiteTransverse h.finiteEnergy M hM hMmax h.densityLower h.densityUpper
    h.momentumBound h.transverseBound h.energyBound h.internalMargin h.guard).1
  dsimp only
  rw [side_values_of_accepted rho mx my energy hstatus]
  exact hspeed

#print axioms side_speed_lower
end Project.EulerRiemann.Numerics
