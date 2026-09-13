import Project.Euler2DCellStep.Model
import Project.ProofKit.F64AdmissibilityTiny

namespace Project.EulerRiemann.Numerics
open Project.Euler2DConservative.Model
  (CheckedSideBits rejectedSide absBits finiteBits positiveBits narrowStateGuard)
open Project.Euler2DDynamicFlux.Model
  (CheckedFlux rejectedFlux componentCheckedBits)
open Project.Euler2DCellStep.Model
  (CheckedCell rejectedCell updateCheckedBits)

def stateGuard (rho momentum transverse energy : UInt64) : Bool :=
  narrowStateGuard rho momentum transverse energy ||
    Project.ProofKit.F64AdmissibilityTiny.checked rho momentum transverse energy

def sideCheckedBits (rho momentum transverse energy : UInt64) : CheckedSideBits :=
  if stateGuard rho momentum transverse energy then
    let velocity := Wasm.IEEE64.div momentum rho
    let transport := Wasm.IEEE64.mul momentum velocity
    let transverseVelocity := Wasm.IEEE64.div transverse rho
    let transverseTransport := Wasm.IEEE64.mul transverse transverseVelocity
    let kineticSum := Wasm.IEEE64.add transport transverseTransport
    let halfKinetic := Wasm.IEEE64.mul 0x3FE0000000000000 kineticSum
    let internal := Wasm.IEEE64.sub energy halfKinetic
    if finiteBits velocity && finiteBits transport && finiteBits transverseVelocity &&
        finiteBits transverseTransport && finiteBits kineticSum && finiteBits halfKinetic &&
        positiveBits internal then
      let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
      let pressureOverDensity := Wasm.IEEE64.div pressure rho
      let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 pressureOverDensity
      if positiveBits pressure && positiveBits pressureOverDensity &&
          positiveBits radicand then
        let soundSpeed := Wasm.IEEE64.sqrt radicand
        let speed := Wasm.IEEE64.add (absBits velocity) soundSpeed
        let momentumFlux := Wasm.IEEE64.add transport pressure
        let transverseFlux := Wasm.IEEE64.mul transverse velocity
        let enthalpy := Wasm.IEEE64.add energy pressure
        let energyFlux := Wasm.IEEE64.mul velocity enthalpy
        if positiveBits soundSpeed && positiveBits speed && finiteBits momentumFlux &&
            finiteBits transverseFlux && finiteBits enthalpy && finiteBits energyFlux then
          ⟨0, velocity, pressure, speed, momentum, momentumFlux, transverseFlux, energyFlux⟩
        else rejectedSide
      else rejectedSide
    else rejectedSide
  else rejectedSide

def fluxCheckedBits (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64) : CheckedFlux :=
  let left := sideCheckedBits rhoL momentumL transverseL energyL
  if left.status == 0 then
    let right := sideCheckedBits rhoR momentumR transverseR energyR
    if right.status == 0 then
      let alpha := if left.speed ≤ right.speed then right.speed else left.speed
      let mass := componentCheckedBits alpha left.massFlux right.massFlux rhoL rhoR
      let momentum := componentCheckedBits alpha left.momentumFlux right.momentumFlux momentumL momentumR
      let transverse := componentCheckedBits alpha left.transverseFlux right.transverseFlux transverseL transverseR
      let energy := componentCheckedBits alpha left.energyFlux right.energyFlux energyL energyR
      if mass.status == 0 && momentum.status == 0 && transverse.status == 0 && energy.status == 0 then
        ⟨0, mass.value, momentum.value, transverse.value, energy.value, alpha⟩
      else rejectedFlux
    else rejectedFlux
  else rejectedFlux

def cellCheckedBits (ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR momentumR transverseR energyR : UInt64) : CheckedCell :=
  if positiveBits ratio then
    let left := fluxCheckedBits rhoL momentumL transverseL energyL rho momentum transverse energy
    if left.status == 0 then
      let right := fluxCheckedBits rho momentum transverse energy rhoR momentumR transverseR energyR
      if right.status == 0 then
        let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
        let courant := Wasm.IEEE64.mul ratio alpha
        if positiveBits courant && decide (courant ≤ 0x3FE0000000000000) then
          let nextDensity := updateCheckedBits ratio rho left.mass right.mass
          let nextMomentum := updateCheckedBits ratio momentum left.momentum right.momentum
          let nextTransverse := updateCheckedBits ratio transverse left.transverse right.transverse
          let nextEnergy := updateCheckedBits ratio energy left.energy right.energy
          if nextDensity.status == 0 && nextMomentum.status == 0 && nextTransverse.status == 0 && nextEnergy.status == 0 then
            let nextSide := sideCheckedBits nextDensity.value nextMomentum.value nextTransverse.value nextEnergy.value
            if nextSide.status == 0 then
              ⟨0, nextDensity.value, nextMomentum.value, nextTransverse.value, nextEnergy.value, nextSide.pressure, alpha, courant⟩
            else rejectedCell
          else rejectedCell
        else rejectedCell
      else rejectedCell
    else rejectedCell
  else rejectedCell

end Project.EulerRiemann.Numerics
