import Project.EulerRiemann.OutwardSpeed

namespace Project.EulerRiemann.OutwardNumerics
open Project.Euler2DConservative.Model (CheckedSideBits rejectedSide finiteBits positiveBits)

def sideCheckedBits (rho momentum transverse energy : UInt64) : CheckedSideBits :=
  let speed := OutwardSpeed.speedUpper rho momentum transverse energy
  if speed.status == 0 then
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
      let momentumFlux := Wasm.IEEE64.add transport pressure
      let transverseFlux := Wasm.IEEE64.mul transverse velocity
      let enthalpy := Wasm.IEEE64.add energy pressure
      let energyFlux := Wasm.IEEE64.mul velocity enthalpy
      if positiveBits pressure && finiteBits momentumFlux && finiteBits transverseFlux &&
          finiteBits enthalpy && finiteBits energyFlux then
        ⟨0, velocity, pressure, speed.value, momentum, momentumFlux, transverseFlux, energyFlux⟩
      else rejectedSide
    else rejectedSide
  else rejectedSide

end Project.EulerRiemann.OutwardNumerics
