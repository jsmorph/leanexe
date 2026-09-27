import Project.EulerRiemann.Numerics
import Project.EulerRiemann.NumericsInternalGuard
import Project.EulerRiemann.NumericsPressure
import Project.EulerRiemann.NumericsSound
import Project.EulerRiemann.NumericsSpeed
import Project.EulerRiemann.NumericsFluxTerms

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64ArithmeticBounds
open Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem side_accepted_of_bounds (rho mx my energy : UInt64)
    (hr : Finite rho) (hx : Finite mx) (hy : Finite my) (he : Finite energy)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : 1 / M ≤ value rho) (brMax : value rho ≤ M)
    (bx : |value mx| ≤ M) (byy : |value my| ≤ M) (be : |value energy| ≤ M)
    (hmargin : 24 * arithmeticEpsilon * M^3 ≤
      value energy - ((value mx)^2 + (value my)^2) / (2 * value rho))
    (hguard : stateGuard rho mx my energy = true) :
    let side := sideCheckedBits rho mx my energy
    side.status = 0 ∧ positiveBits side.speed = true ∧ value side.speed ≤ 32 * M^2 ∧
    Finite side.massFlux ∧ Finite side.momentumFlux ∧ Finite side.transverseFlux ∧ Finite side.energyFlux ∧
    |value side.massFlux| ≤ M ∧ |value side.momentumFlux| ≤ 8 * M^3 ∧
    |value side.transverseFlux| ≤ 3 * M^3 ∧ |value side.energyFlux| ≤ 15 * M^5 := by
  let u := Wasm.IEEE64.div mx rho
  let v := Wasm.IEEE64.div my rho
  let tx := Wasm.IEEE64.mul mx u
  let ty := Wasm.IEEE64.mul my v
  let sum := Wasm.IEEE64.add tx ty
  let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 sum
  let internal := Wasm.IEEE64.sub energy kinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let ratio := Wasm.IEEE64.div pressure rho
  let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 ratio
  let sound := Wasm.IEEE64.sqrt radicand
  let speed := Wasm.IEEE64.add (Project.Euler2DConservative.Model.absBits u) sound
  let momentumFlux := Wasm.IEEE64.add tx pressure
  let transverseFlux := Wasm.IEEE64.mul my u
  let enthalpy := Wasm.IEEE64.add energy pressure
  let energyFlux := Wasm.IEEE64.mul u enthalpy
  obtain ⟨hu, hv, htx, hty, hsum, hkin, hi, ei, bi⟩ :=
    internal_error rho mx my energy hr hx hy he M hM hMmax br bx byy be
  obtain ⟨_, _, _, bu, _, btx⟩ := transport_error rho mx hr hx M hM hMmax br bx
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM3 : 1 ≤ M^3 := one_le_pow₀ hM
  have heM : 0 < arithmeticEpsilon * M^3 := mul_pos epsilon_pos (pow_pos hMpos 3)
  have hmarginStrict : 12 * arithmeticEpsilon * M^3 <
      value energy - ((value mx)^2 + (value my)^2) / (2 * value rho) := by
    linarith only [hmargin, heM]
  have hiMin : arithmeticEpsilon ≤ value internal := by
    have hl := (abs_le.mp ei).1
    have hb := mul_le_mul_of_nonneg_left hM3 epsilon_pos.le
    change -(12 * arithmeticEpsilon * M^3) ≤ value internal -
      (value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)) at hl
    nlinarith only [hl, hmargin, hb, heM]
  have biUpper : value internal ≤ 5 * M^3 := (le_abs_self _).trans bi
  have hiMax : value internal < (2 : ℝ)^1022 := by
    calc
      _ ≤ 5 * M^3 := biUpper
      _ ≤ 5 * ((2 : ℝ)^100)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 3) (by norm_num)
      _ < (2 : ℝ)^1022 := by norm_num
  obtain ⟨hpPos, hpLo, hpHi, _⟩ := pressure_error internal hi hiMin hiMax
  have hp := positiveBits_spec pressure hpPos
  have bpLo : arithmeticEpsilon / 8 ≤ value pressure := by linarith only [hiMin, hpLo]
  have bpHi : value pressure ≤ 5 * M^3 := hpHi.trans biUpper
  have bpAbs : |value pressure| ≤ 5 * M^3 := by rwa [abs_of_pos hp.2]
  obtain ⟨hqPos, hradPos, hsPos, bs, _⟩ := sound_error pressure rho hp.1 hr M hM hMmax br brMax bpLo bpHi
  obtain ⟨hspeedPos, _, bspeed, _⟩ := speed_error u sound hu hsPos M hM hMmax bu bs
  obtain ⟨hfm, hft, hfh, hfe, bfm, bft, _, bfe, _⟩ :=
    side_flux_terms u tx my energy pressure hu htx hy he hp.1 M hM hMmax bu btx byy be bpAbs
  have hg1 : (Project.Euler2DConservative.Model.finiteBits u &&
      Project.Euler2DConservative.Model.finiteBits tx &&
      Project.Euler2DConservative.Model.finiteBits v &&
      Project.Euler2DConservative.Model.finiteBits ty &&
      Project.Euler2DConservative.Model.finiteBits sum &&
      Project.Euler2DConservative.Model.finiteBits kinetic &&
      Project.Euler2DConservative.Model.positiveBits internal) = true :=
    internal_guard rho mx my energy hr hx hy he M hM hMmax br bx byy be hmarginStrict
  have hg2 : (Project.Euler2DConservative.Model.positiveBits pressure &&
      Project.Euler2DConservative.Model.positiveBits ratio &&
      Project.Euler2DConservative.Model.positiveBits radicand) = true := by
    change (positiveBits pressure && positiveBits ratio && positiveBits radicand) = true
    simp only [Bool.and_eq_true_iff]
    exact ⟨⟨hpPos, hqPos⟩, hradPos⟩
  have hg3 : (Project.Euler2DConservative.Model.positiveBits sound &&
      Project.Euler2DConservative.Model.positiveBits speed &&
      Project.Euler2DConservative.Model.finiteBits momentumFlux &&
      Project.Euler2DConservative.Model.finiteBits transverseFlux &&
      Project.Euler2DConservative.Model.finiteBits enthalpy &&
      Project.Euler2DConservative.Model.finiteBits energyFlux) = true := by
    change (positiveBits sound && positiveBits speed && finiteBits momentumFlux &&
      finiteBits transverseFlux && finiteBits enthalpy && finiteBits energyFlux) = true
    simp only [Bool.and_eq_true_iff, finiteBits_iff]
    exact ⟨⟨⟨⟨⟨hsPos, hspeedPos⟩, hfm⟩, hft⟩, hfh⟩, hfe⟩
  have hside : sideCheckedBits rho mx my energy =
      ⟨0, u, pressure, speed, mx, momentumFlux, transverseFlux, energyFlux⟩ := by
    unfold sideCheckedBits
    rw [ite_eq_left hguard, ite_eq_left hg1, ite_eq_left hg2, ite_eq_left hg3]
  dsimp only
  rw [hside]
  exact ⟨rfl, hspeedPos, bspeed, hx, hfm, hft, hfe, bx, bfm, bft, bfe⟩

#print axioms side_accepted_of_bounds
end Project.EulerRiemann.Numerics
