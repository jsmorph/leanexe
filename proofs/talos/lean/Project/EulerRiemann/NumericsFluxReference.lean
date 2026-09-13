import Project.EulerRiemann.NumericsFluxBounds
import Project.EulerRiemann.NumericsPressureReference
import Project.EulerRiemann.NumericsSideValues
import Project.ProofKit.RealProductError

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds
open Project.ProofKit.F64Order

theorem side_flux_reference_error (rho mx my energy : UInt64)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (h : StateBounds M rho mx my energy) :
    let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
    let side := sideCheckedBits rho mx my energy
    value side.massFlux = value mx ∧
    |value side.momentumFlux - ((value mx)^2 / value rho + (2 / 5) * I)| ≤ 20 * arithmeticEpsilon * M^3 ∧
    |value side.transverseFlux - value mx * value my / value rho| ≤ 3 * arithmeticEpsilon * M^3 ∧
    |value side.energyFlux - (value energy + (2 / 5) * I) * (value mx / value rho)| ≤
      48 * arithmeticEpsilon * M^5 := by
  let u := Wasm.IEEE64.div mx rho
  let tx := Wasm.IEEE64.mul mx u
  let ty := Wasm.IEEE64.mul my (Wasm.IEEE64.div my rho)
  let internal := Wasm.IEEE64.sub energy (Wasm.IEEE64.mul 0x3FE0000000000000 (Wasm.IEEE64.add tx ty))
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let momentumFlux := Wasm.IEEE64.add tx pressure
  let transverseFlux := Wasm.IEEE64.mul my u
  let enthalpy := Wasm.IEEE64.add energy pressure
  let energyFlux := Wasm.IEEE64.mul u enthalpy
  let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
  let H := value energy + (2 / 5) * I
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
  have bH : |H| ≤ 2 * M := by
    have ht := abs_add_le (value energy) ((2 / 5) * I)
    rw [abs_of_pos (by positivity : (0 : ℝ) < (2 / 5) * I)] at ht
    change |H| ≤ |value energy| + (2 / 5) * I at ht
    linarith only [ht, h.energyBound, hIM, hMpos]
  have hM35 : M^3 ≤ M^5 := by
    have hb := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) (pow_nonneg hMpos.le 3)
    nlinarith only [hb]
  have he35 := mul_le_mul_of_nonneg_left hM35 epsilon_pos.le
  obtain ⟨hu, _, htx, _, _, _, hi, ei, bi⟩ := internal_error rho mx my energy
    h.finiteDensity h.finiteMomentum h.finiteTransverse h.finiteEnergy M hM hMmax
    h.densityLower h.momentumBound h.transverseBound h.energyBound
  obtain ⟨_, _, eu, bu, etx, btx⟩ := transport_error rho mx h.finiteDensity h.finiteMomentum
    M hM hMmax h.densityLower h.momentumBound
  obtain ⟨hpPos, _, bpHi, ep, _⟩ := pressure_reference_error internal hi I M hM hMmax bi ei h.internalMargin
  have hp := positiveBits_spec pressure hpPos
  have bp : |value pressure| ≤ 5 * M^3 := by rwa [abs_of_pos hp.2]
  obtain ⟨_, _, _, _, _, _, _, _, em, et, eh, ee⟩ :=
    side_flux_terms u tx my energy pressure hu htx h.finiteTransverse h.finiteEnergy hp.1
      M hM hMmax bu btx h.transverseBound h.energyBound bp
  change |value momentumFlux - (value tx + value pressure)| ≤ 7 * arithmeticEpsilon * M^3 at em
  change |value tx - (value mx)^2 / value rho| ≤ 3 * arithmeticEpsilon * M^3 at etx
  change |value pressure - (2 / 5) * I| ≤ 10 * arithmeticEpsilon * M^3 at ep
  have emTotal : |value momentumFlux - ((value mx)^2 / value rho + (2 / 5) * I)| ≤
      20 * arithmeticEpsilon * M^3 := by
    obtain ⟨eml, emr⟩ := abs_le.mp em
    obtain ⟨etl, etr⟩ := abs_le.mp etx
    obtain ⟨epl, epr⟩ := abs_le.mp ep
    apply abs_le.mpr
    constructor <;> linarith only [eml, emr, etl, etr, epl, epr]
  have etProduct : |value my * value u - value mx * value my / value rho| ≤ arithmeticEpsilon * M^3 := by
    rw [show value my * value u - value mx * value my / value rho =
      value my * (value u - value mx / value rho) by ring, abs_mul]
    calc
      _ ≤ M * (arithmeticEpsilon * M^2) := mul_le_mul h.transverseBound eu (abs_nonneg _) hMpos.le
      _ = arithmeticEpsilon * M^3 := by ring
  have etTotal : |value transverseFlux - value mx * value my / value rho| ≤
      3 * arithmeticEpsilon * M^3 := by
    change |value transverseFlux - value my * value u| ≤ 2 * arithmeticEpsilon * M^3 at et
    obtain ⟨etl, etr⟩ := abs_le.mp et
    obtain ⟨epl, epr⟩ := abs_le.mp etProduct
    apply abs_le.mpr
    constructor <;> linarith only [etl, etr, epl, epr]
  have eH : |value enthalpy - H| ≤ 16 * arithmeticEpsilon * M^3 := by
    change |value enthalpy - (value energy + value pressure)| ≤ 6 * arithmeticEpsilon * M^3 at eh
    obtain ⟨ehl, ehr⟩ := abs_le.mp eh
    obtain ⟨epl, epr⟩ := abs_le.mp ep
    dsimp only [H]
    apply abs_le.mpr
    constructor <;> linarith only [ehl, ehr, epl, epr]
  have eProduct := Project.ProofKit.RealProductError.product_error (value u) (value enthalpy)
    (value mx / value rho) H (arithmeticEpsilon * M^2) (16 * arithmeticEpsilon * M^3)
    (2 * M^2) (2 * M) eu eH bu bH
  have eeTotal : |value energyFlux - H * (value mx / value rho)| ≤ 48 * arithmeticEpsilon * M^5 := by
    change |value energyFlux - value u * value enthalpy| ≤ 14 * arithmeticEpsilon * M^5 at ee
    rw [mul_comm (value mx / value rho) H] at eProduct
    obtain ⟨eel, eer⟩ := abs_le.mp ee
    obtain ⟨epl, epr⟩ := abs_le.mp eProduct
    apply abs_le.mpr
    constructor <;> nlinarith only [eel, eer, epl, epr, he35]
  have hstatus := (side_accepted_of_bounds rho mx my energy h.finiteDensity h.finiteMomentum
    h.finiteTransverse h.finiteEnergy M hM hMmax h.densityLower h.densityUpper
    h.momentumBound h.transverseBound h.energyBound h.internalMargin h.guard).1
  dsimp only
  rw [side_values_of_accepted rho mx my energy hstatus]
  exact ⟨rfl, emTotal, etTotal, eeTotal⟩

#print axioms side_flux_reference_error
end Project.EulerRiemann.Numerics
