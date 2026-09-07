import Project.ProofKit.F64Order

namespace Project.EulerConservative.Model

/-- Every public numeric value is a raw binary64 word. -/
structure CheckedSideBits where
  status : UInt64
  velocity : UInt64
  pressure : UInt64
  speed : UInt64
  massFlux : UInt64
  momentumFlux : UInt64
  energyFlux : UInt64
  deriving DecidableEq, Inhabited, Repr

def absBits (bits : UInt64) : UInt64 := bits &&& 0x7FFFFFFFFFFFFFFF

def finiteBits (bits : UInt64) : Bool :=
  decide (absBits bits < (0x7FF0000000000000 : UInt64))

def positiveBits (bits : UInt64) : Bool :=
  decide ((0 : UInt64) < bits) && decide (bits < (0x7FF0000000000000 : UInt64))

/-- A conservative sufficient domain for positive exact internal energy.
Energy must be positive before unsigned ordering is used. -/
def stateGuard (rho momentum energy : UInt64) : Bool :=
  positiveBits rho && finiteBits momentum && positiveBits energy &&
    decide (absBits momentum ≤ rho) && decide (rho ≤ energy)

def rejectedSide : CheckedSideBits := ⟨1, 0, 0, 0, 0, 0, 0⟩

/-- Pure Talos model of one conservative state's thermodynamics and physical flux.
The executable constants are the binary64 encodings nearest to 2/5 and 7/5.
Every input and rounded intermediate is checked before acceptance. -/
def sideCheckedBits (rho momentum energy : UInt64) : CheckedSideBits :=
  if stateGuard rho momentum energy then
    let velocity := Wasm.IEEE64.div momentum rho
    let transport := Wasm.IEEE64.mul momentum velocity
    let halfKinetic := Wasm.IEEE64.mul 0x3FE0000000000000 transport
    let internal := Wasm.IEEE64.sub energy halfKinetic
    if finiteBits velocity && finiteBits transport && finiteBits halfKinetic &&
        positiveBits internal then
      let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
      let pressureOverDensity := Wasm.IEEE64.div pressure rho
      let radicand := Wasm.IEEE64.mul 0x3FF6666666666666 pressureOverDensity
      if positiveBits pressure && positiveBits pressureOverDensity &&
          positiveBits radicand then
        let soundSpeed := Wasm.IEEE64.sqrt radicand
        let speed := Wasm.IEEE64.add (absBits velocity) soundSpeed
        let momentumFlux := Wasm.IEEE64.add transport pressure
        let enthalpy := Wasm.IEEE64.add energy pressure
        let energyFlux := Wasm.IEEE64.mul velocity enthalpy
        if positiveBits soundSpeed && positiveBits speed && finiteBits momentumFlux &&
            finiteBits enthalpy && finiteBits energyFlux then
          ⟨0, velocity, pressure, speed, momentum, momentumFlux, energyFlux⟩
        else rejectedSide
      else rejectedSide
    else rejectedSide
  else rejectedSide

end Project.EulerConservative.Model
