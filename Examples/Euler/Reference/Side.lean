import Examples.Euler.Reference.InternalGuard
import Examples.Euler.Reference.PressureReference
import Examples.Euler.Reference.Sound
import Examples.Euler.Reference.Speed
import Examples.Euler.Reference.FluxTerms
import Examples.Euler.RealState
import LeanExe.ProofKit.RealProductError
import Examples.Euler.Equations.Flux

/-! The first-order solver's `side` against the exact physical flux.  For a state whose density
lies in `[1/M, M]`, whose other components are at most `M` in magnitude, whose internal energy
exceeds `24 ε M³`, and which passes the solver's state check, `side` accepts the state.  Its mass
flux is the momentum, and its momentum, transverse, and energy fluxes are within `20 ε M³`,
`3 ε M³`, and `48 ε M⁵` of the exact x-direction fluxes, where `ε = 2⁻⁵²` is
`arithmeticEpsilon`. -/

namespace Examples.Euler.Reference

open Examples.Euler LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite arithmeticEpsilon)
open LeanExe.ProofKit.F64ArithmeticBounds
open LeanExe.ProofKit.F64Order

set_option exponentiation.threshold 4096

/-- WebAssembly's `abs` clears the sign bit. -/
theorem abs_eq_absBits (x : UInt64) : Wasm.IEEE64.abs x = F64Order.absBits x := by
  apply UInt64.toNat_inj.mp
  rw [F64Order.absBits_toNat]
  have hx := x.toNat_lt
  simp only [Wasm.IEEE64.abs, Wasm.IEEE64.encodeFinite, Wasm.IEEE64.exponent,
    Wasm.IEEE64.fraction, Bool.false_eq_true, ite_false, Nat.zero_add, UInt64.toNat_ofNat']
  omega

theorem finite_of_bits {x : Float} (h : Finite x.toBits) : finite x = true :=
  (F64Order.finiteBits_iff x.toBits).mpr h

/-- A state in the range `M` with a margin of internal energy, accepted by the state check. -/
structure StateBounds (M : ℝ) (rho mx my energy : Float) : Prop where
  finiteDensity : Finite rho.toBits
  finiteMomentum : Finite mx.toBits
  finiteTransverse : Finite my.toBits
  finiteEnergy : Finite energy.toBits
  densityLower : 1 / M ≤ real rho
  densityUpper : real rho ≤ M
  momentumBound : |real mx| ≤ M
  transverseBound : |real my| ≤ M
  energyBound : |real energy| ≤ M
  internalMargin : 24 * arithmeticEpsilon * M^3 ≤
    real energy - ((real mx)^2 + (real my)^2) / (2 * real rho)
  guard : stateGuard rho mx my energy = true

/-- The values that `side` returns when it accepts. -/
theorem side_values_of_accepted (rho mx my energy : Float)
    (h : (side rho mx my energy).status = 0) :
    side rho mx my energy =
      ⟨0, mx / rho, 0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho))),
        (mx / rho).abs + (1.4 * (0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho))) /
          rho)).sqrt, mx,
        mx * (mx / rho) + 0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho))),
        my * (mx / rho),
        mx / rho * (energy + 0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho))))⟩ := by
  unfold side at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hg
  · rfl
  · exact absurd h (by decide)

/-- Under the state bounds, `side` accepts, with a positive speed at most `32 M²` and fluxes
bounded by powers of `M`. -/
theorem side_accepted_of_bounds (rho mx my energy : Float) (M : ℝ) (hM : 1 ≤ M)
    (hMmax : M ≤ (2 : ℝ)^100) (h : StateBounds M rho mx my energy) :
    let s := side rho mx my energy
    s.status = 0 ∧ positive s.speed = true ∧ real s.speed ≤ 32 * M^2 ∧
      Finite s.massFlux.toBits ∧ Finite s.momentumFlux.toBits ∧ Finite s.transverseFlux.toBits ∧
      Finite s.energyFlux.toBits ∧ |real s.massFlux| ≤ M ∧ |real s.momentumFlux| ≤ 8 * M^3 ∧
      |real s.transverseFlux| ≤ 3 * M^3 ∧ |real s.energyFlux| ≤ 15 * M^5 := by
  have hr := h.finiteDensity
  have hx := h.finiteMomentum
  have hy := h.finiteTransverse
  have he := h.finiteEnergy
  have br := h.densityLower
  have brMax := h.densityUpper
  have bx := h.momentumBound
  have byy := h.transverseBound
  have be := h.energyBound
  have hmargin := h.internalMargin
  simp only [real] at br brMax bx byy be hmargin
  let u := Wasm.IEEE64.div mx.toBits rho.toBits
  let v := Wasm.IEEE64.div my.toBits rho.toBits
  let tx := Wasm.IEEE64.mul mx.toBits u
  let ty := Wasm.IEEE64.mul my.toBits v
  let sum := Wasm.IEEE64.add tx ty
  let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 sum
  let internal := Wasm.IEEE64.sub energy.toBits kinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let ratio := Wasm.IEEE64.div pressure rho.toBits
  let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 ratio
  let sound := Wasm.IEEE64.sqrt radicand
  let speed := Wasm.IEEE64.add (F64Order.absBits u) sound
  let momentumFlux := Wasm.IEEE64.add tx pressure
  let transverseFlux := Wasm.IEEE64.mul my.toBits u
  let enthalpy := Wasm.IEEE64.add energy.toBits pressure
  let energyFlux := Wasm.IEEE64.mul u enthalpy
  obtain ⟨hu, hv, htx, hty, hsum, hkin, hi, ei, bi⟩ :=
    internal_error rho.toBits mx.toBits my.toBits energy.toBits hr hx hy he M hM hMmax br bx byy be
  obtain ⟨_, _, _, bu, _, btx⟩ := transport_error rho.toBits mx.toBits hr hx M hM hMmax br bx
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM3 : 1 ≤ M^3 := one_le_pow₀ hM
  have heM : 0 < arithmeticEpsilon * M^3 := mul_pos epsilon_pos (pow_pos hMpos 3)
  have hmarginStrict : 12 * arithmeticEpsilon * M^3 <
      value energy.toBits - ((value mx.toBits)^2 + (value my.toBits)^2) /
        (2 * value rho.toBits) := by
    linarith only [hmargin, heM]
  have hiMin : arithmeticEpsilon ≤ value internal := by
    have hl := (abs_le.mp ei).1
    have hb := mul_le_mul_of_nonneg_left hM3 epsilon_pos.le
    change -(12 * arithmeticEpsilon * M^3) ≤ value internal -
      (value energy.toBits - ((value mx.toBits)^2 + (value my.toBits)^2) /
        (2 * value rho.toBits)) at hl
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
  obtain ⟨hqPos, hradPos, hsPos, bs, _⟩ :=
    sound_error pressure rho.toBits hp.1 hr M hM hMmax br brMax bpLo bpHi
  obtain ⟨hspeedPos, _, bspeed, _⟩ := speed_error u sound hu hsPos M hM hMmax bu bs
  obtain ⟨hfm, hft, hfh, hfe, bfm, bft, _, bfe, _⟩ :=
    side_flux_terms u tx my.toBits energy.toBits pressure hu htx hy he hp.1 M hM hMmax bu btx byy
      be bpAbs
  have hg1 := internal_guard rho.toBits mx.toBits my.toBits energy.toBits hr hx hy he M hM hMmax
    br bx byy be hmarginStrict
  simp only [Bool.and_eq_true] at hg1
  obtain ⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩ := hg1
  have hBits : ∀ x : Float, finite x = finiteBits x.toBits := fun _ => rfl
  have hfmB : finiteBits momentumFlux = true := (finiteBits_iff _).mpr hfm
  have hftB : finiteBits transverseFlux = true := (finiteBits_iff _).mpr hft
  have hfhB : finiteBits enthalpy = true := (finiteBits_iff _).mpr hfh
  have hfeB : finiteBits energyFlux = true := (finiteBits_iff _).mpr hfe
  have hside : side rho mx my energy =
      ⟨0, mx / rho, 0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho))),
        (mx / rho).abs + (1.4 * (0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho))) /
          rho)).sqrt, mx,
        mx * (mx / rho) + 0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho))),
        my * (mx / rho),
        mx / rho * (energy + 0.4 * (energy - 0.5 * (mx * (mx / rho) + my * (my / rho))))⟩ := by
    unfold side
    dsimp only
    split
    · rfl
    · rename_i hNot
      exfalso
      apply hNot
      simp (config := { zetaDelta := true }) only [h.guard, hBits, positive_eq,
        F64Bits.toBits_div, F64Bits.toBits_mul, F64Bits.toBits_add, F64Bits.toBits_sub,
        F64Bits.toBits_sqrt, F64Bits.toBits_abs, half_toBits, twoFifths_toBits, sevenFifths_toBits,
        abs_eq_absBits, g1, g2, g3, g4, g5, g6, g7, hpPos, hqPos, hradPos, hsPos, hspeedPos, hfmB,
        hftB, hfhB, hfeB, Bool.and_self]
  rw [hside]
  refine ⟨rfl, ?_⟩
  simp (config := { zetaDelta := true }) only [real, positive_eq, F64Bits.toBits_div,
    F64Bits.toBits_mul, F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_sqrt,
    F64Bits.toBits_abs, half_toBits, twoFifths_toBits, sevenFifths_toBits, abs_eq_absBits]
  exact ⟨hspeedPos, bspeed, hx, hfm, hft, hfe, bx, bfm, bft, bfe⟩

/-- The side fluxes against the exact fluxes of the state's values. -/
theorem side_flux_reference_error (rho mx my energy : Float) (M : ℝ) (hM : 1 ≤ M)
    (hMmax : M ≤ (2 : ℝ)^100) (h : StateBounds M rho mx my energy) :
    let I := real energy - ((real mx)^2 + (real my)^2) / (2 * real rho)
    let s := side rho mx my energy
    real s.massFlux = real mx ∧
      |real s.momentumFlux - ((real mx)^2 / real rho + (2 / 5) * I)| ≤ 20 * arithmeticEpsilon * M^3 ∧
      |real s.transverseFlux - real mx * real my / real rho| ≤ 3 * arithmeticEpsilon * M^3 ∧
      |real s.energyFlux - (real energy + (2 / 5) * I) * (real mx / real rho)| ≤
        48 * arithmeticEpsilon * M^5 := by
  have hr := h.finiteDensity
  have hx := h.finiteMomentum
  have hy := h.finiteTransverse
  have he := h.finiteEnergy
  have br := h.densityLower
  have bx := h.momentumBound
  have byy := h.transverseBound
  have be := h.energyBound
  have hmargin := h.internalMargin
  simp only [real] at br bx byy be hmargin ⊢
  let u := Wasm.IEEE64.div mx.toBits rho.toBits
  let tx := Wasm.IEEE64.mul mx.toBits u
  let internal := Wasm.IEEE64.sub energy.toBits (Wasm.IEEE64.mul 0x3FE0000000000000
    (Wasm.IEEE64.add tx (Wasm.IEEE64.mul my.toBits (Wasm.IEEE64.div my.toBits rho.toBits))))
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let momentumFlux := Wasm.IEEE64.add tx pressure
  let transverseFlux := Wasm.IEEE64.mul my.toBits u
  let enthalpy := Wasm.IEEE64.add energy.toBits pressure
  let energyFlux := Wasm.IEEE64.mul u enthalpy
  let I := value energy.toBits - ((value mx.toBits)^2 + (value my.toBits)^2) /
    (2 * value rho.toBits)
  let H := value energy.toBits + (2 / 5) * I
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hrPos : 0 < value rho.toBits := lt_of_lt_of_le (by positivity) br
  have hIM : I ≤ M := by
    have hk : 0 ≤ ((value mx.toBits)^2 + (value my.toBits)^2) / (2 * value rho.toBits) := by
      positivity
    have hE := (le_abs_self (value energy.toBits)).trans be
    dsimp only [I]
    linarith only [hk, hE]
  have hI : 0 < I := by
    have heM := mul_pos epsilon_pos (pow_pos hMpos 3)
    change 24 * arithmeticEpsilon * M^3 ≤ I at hmargin
    linarith only [hmargin, heM]
  have bH : |H| ≤ 2 * M := by
    have ht := abs_add_le (value energy.toBits) ((2 / 5) * I)
    rw [abs_of_pos (by positivity : (0 : ℝ) < (2 / 5) * I)] at ht
    change |H| ≤ |value energy.toBits| + (2 / 5) * I at ht
    linarith only [ht, be, hIM, hMpos]
  have hM35 : M^3 ≤ M^5 := by
    have hb := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^2) (pow_nonneg hMpos.le 3)
    nlinarith only [hb]
  have he35 := mul_le_mul_of_nonneg_left hM35 epsilon_pos.le
  obtain ⟨hu, _, htx, _, _, _, hi, ei, bi⟩ :=
    internal_error rho.toBits mx.toBits my.toBits energy.toBits hr hx hy he M hM hMmax br bx byy be
  obtain ⟨_, _, eu, bu, etx, btx⟩ := transport_error rho.toBits mx.toBits hr hx M hM hMmax br bx
  obtain ⟨hpPos, _, bpHi, ep, _⟩ := pressure_reference_error internal hi I M hM hMmax bi ei hmargin
  have hp := positiveBits_spec pressure hpPos
  have bp : |value pressure| ≤ 5 * M^3 := by rwa [abs_of_pos hp.2]
  obtain ⟨_, _, _, _, _, _, _, _, em, et, eh, ee⟩ :=
    side_flux_terms u tx my.toBits energy.toBits pressure hu htx hy he hp.1 M hM hMmax bu btx byy
      be bp
  change |value momentumFlux - (value tx + value pressure)| ≤ 7 * arithmeticEpsilon * M^3 at em
  change |value tx - (value mx.toBits)^2 / value rho.toBits| ≤ 3 * arithmeticEpsilon * M^3 at etx
  change |value pressure - (2 / 5) * I| ≤ 10 * arithmeticEpsilon * M^3 at ep
  have emTotal : |value momentumFlux - ((value mx.toBits)^2 / value rho.toBits + (2 / 5) * I)| ≤
      20 * arithmeticEpsilon * M^3 := by
    obtain ⟨eml, emr⟩ := abs_le.mp em
    obtain ⟨etl, etr⟩ := abs_le.mp etx
    obtain ⟨epl, epr⟩ := abs_le.mp ep
    apply abs_le.mpr
    constructor <;> linarith only [eml, emr, etl, etr, epl, epr]
  have etProduct : |value my.toBits * value u - value mx.toBits * value my.toBits /
      value rho.toBits| ≤ arithmeticEpsilon * M^3 := by
    rw [show value my.toBits * value u - value mx.toBits * value my.toBits / value rho.toBits =
      value my.toBits * (value u - value mx.toBits / value rho.toBits) by ring, abs_mul]
    calc
      _ ≤ M * (arithmeticEpsilon * M^2) := mul_le_mul byy eu (abs_nonneg _) hMpos.le
      _ = arithmeticEpsilon * M^3 := by ring
  have etTotal : |value transverseFlux - value mx.toBits * value my.toBits / value rho.toBits| ≤
      3 * arithmeticEpsilon * M^3 := by
    change |value transverseFlux - value my.toBits * value u| ≤ 2 * arithmeticEpsilon * M^3 at et
    obtain ⟨etl, etr⟩ := abs_le.mp et
    obtain ⟨epl, epr⟩ := abs_le.mp etProduct
    apply abs_le.mpr
    constructor <;> linarith only [etl, etr, epl, epr]
  have eH : |value enthalpy - H| ≤ 16 * arithmeticEpsilon * M^3 := by
    change |value enthalpy - (value energy.toBits + value pressure)| ≤
      6 * arithmeticEpsilon * M^3 at eh
    obtain ⟨ehl, ehr⟩ := abs_le.mp eh
    obtain ⟨epl, epr⟩ := abs_le.mp ep
    dsimp only [H]
    apply abs_le.mpr
    constructor <;> linarith only [ehl, ehr, epl, epr]
  have eProduct := RealProductError.product_error (value u) (value enthalpy)
    (value mx.toBits / value rho.toBits) H (arithmeticEpsilon * M^2) (16 * arithmeticEpsilon * M^3)
    (2 * M^2) (2 * M) eu eH bu bH
  have eeTotal : |value energyFlux - H * (value mx.toBits / value rho.toBits)| ≤
      48 * arithmeticEpsilon * M^5 := by
    change |value energyFlux - value u * value enthalpy| ≤ 14 * arithmeticEpsilon * M^5 at ee
    rw [mul_comm (value mx.toBits / value rho.toBits) H] at eProduct
    obtain ⟨eel, eer⟩ := abs_le.mp ee
    obtain ⟨epl, epr⟩ := abs_le.mp eProduct
    apply abs_le.mpr
    constructor <;> nlinarith only [eel, eer, epl, epr, he35]
  have hstatus := (side_accepted_of_bounds rho mx my energy M hM hMmax h).1
  rw [side_values_of_accepted rho mx my energy hstatus]
  simp (config := { zetaDelta := true }) only [F64Bits.toBits_div, F64Bits.toBits_mul,
    F64Bits.toBits_add, F64Bits.toBits_sub, half_toBits, twoFifths_toBits]
  exact ⟨trivial, emTotal, etTotal, eeTotal⟩

/-- The four fluxes that `side` returns, as reals. -/
noncomputable def sideFluxes (s : Side) : Equations.Vec4 :=
  ![real s.massFlux, real s.momentumFlux, real s.transverseFlux, real s.energyFlux]

/-- The error bound of each side flux. -/
noncomputable def sideFluxBound (M : ℝ) : Equations.Vec4 :=
  ![0, 20 * arithmeticEpsilon * M^3, 3 * arithmeticEpsilon * M^3, 48 * arithmeticEpsilon * M^5]

/-- Under the state bounds, each flux that `side` returns is within its bound of the exact
x-direction flux `Equations.xFlux` of the state's values. -/
theorem side_xFlux_error (rho mx my energy : Float) (M : ℝ) (hM : 1 ≤ M)
    (hMmax : M ≤ (2 : ℝ)^100) (h : StateBounds M rho mx my energy) (i : Fin 4) :
    |sideFluxes (side rho mx my energy) i - Equations.xFlux (vec ⟨rho, mx, my, energy⟩) i| ≤
      sideFluxBound M i := by
  obtain ⟨hm, hp, ht, he⟩ := side_flux_reference_error rho mx my energy M hM hMmax h
  have hx1 : Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 1 = (real mx)^2 / real rho +
      (2 / 5) * (real energy - ((real mx)^2 + (real my)^2) / (2 * real rho)) := by
    simp [Equations.xFlux, vec, Equations.velocity, Equations.pressure, Equations.internalEnergy]
    field_simp
  have hx2 : Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 2 = real mx * real my / real rho := by
    simp [Equations.xFlux, vec, Equations.velocity]
    field_simp
  have hx3 : Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 3 = (real energy + (2 / 5) *
      (real energy - ((real mx)^2 + (real my)^2) / (2 * real rho))) * (real mx / real rho) := by
    simp [Equations.xFlux, vec, Equations.velocity, Equations.pressure, Equations.internalEnergy]
  fin_cases i
  · show |real (side rho mx my energy).massFlux - Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 0| ≤ 0
    simp [Equations.xFlux, vec, hm]
  · show |real (side rho mx my energy).momentumFlux -
        Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 1| ≤ 20 * arithmeticEpsilon * M^3
    rw [hx1]; exact hp
  · show |real (side rho mx my energy).transverseFlux -
        Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 2| ≤ 3 * arithmeticEpsilon * M^3
    rw [hx2]; exact ht
  · show |real (side rho mx my energy).energyFlux -
        Equations.xFlux (vec ⟨rho, mx, my, energy⟩) 3| ≤ 48 * arithmeticEpsilon * M^5
    rw [hx3]; exact he

end Examples.Euler.Reference
