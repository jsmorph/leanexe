import LeanExe.Float64

namespace LeanExe.Examples.Euler2DConservative

/-- Every public numeric value is a raw binary64 word. -/
structure CheckedSideBits where
  status : UInt64
  velocity : UInt64
  pressure : UInt64
  speed : UInt64
  massFlux : UInt64
  momentumFlux : UInt64
  transverseFlux : UInt64
  energyFlux : UInt64
  deriving Inhabited

def absBits (bits : UInt64) : UInt64 := bits &&& 0x7FFFFFFFFFFFFFFF

def finiteBits (bits : UInt64) : Bool :=
  decide (absBits bits < (0x7FF0000000000000 : UInt64))

def positiveBits (bits : UInt64) : Bool :=
  decide ((0 : UInt64) < bits) && decide (bits < (0x7FF0000000000000 : UInt64))

/-- A conservative sufficient domain for positive exact internal energy.
Both momentum magnitudes are at most rho; E>rho leaves a strict internal-energy margin. -/
def narrowStateGuard (rho momentum transverse energy : UInt64) : Bool :=
  positiveBits rho && finiteBits momentum && finiteBits transverse && positiveBits energy &&
    decide (absBits momentum ≤ rho) && decide (absBits transverse ≤ rho) && decide (rho < energy)

def exponentBits (bits : UInt64) : UInt64 := absBits bits / 0x0010000000000000

def maxWord (a b : UInt64) : UInt64 := if a < b then b else a

def topExponent (rho mx my energy : UInt64) : UInt64 :=
  maxWord (maxWord (exponentBits rho) (exponentBits mx))
    (maxWord (exponentBits my) (exponentBits energy))

def normalizable (bits top : UInt64) : Bool :=
  absBits bits == 0 ||
    (decide ((0 : UInt64) < exponentBits bits) && decide (top < exponentBits bits + 1021))

def normalizedMagnitude (bits top : UInt64) : UInt64 :=
  if absBits bits == 0 then 0
  else (exponentBits bits + 1021 - top) * 0x0010000000000000 +
    absBits bits % 0x0010000000000000

def energyResidual (rho mx my energy : UInt64) : UInt64 :=
  let product := LeanExe.Float64.mulBits rho energy
  let xx := LeanExe.Float64.mulBits mx mx
  let yy := LeanExe.Float64.mulBits my my
  let sum := LeanExe.Float64.addBits xx yy
  let kinetic := LeanExe.Float64.mulBits 0x3FE0000000000000 sum
  LeanExe.Float64.subBits product kinetic

def energyGuard (rho mx my energy : UInt64) : Bool :=
  if positiveBits rho && finiteBits mx && finiteBits my && positiveBits energy then
    let top := topExponent rho mx my energy
    if normalizable rho top && normalizable mx top && normalizable my top && normalizable energy top then
      let result := energyResidual
        (normalizedMagnitude rho top) (normalizedMagnitude mx top)
        (normalizedMagnitude my top) (normalizedMagnitude energy top)
      positiveBits result && decide ((0x3CE0000000000000 : UInt64) < result)
    else false
  else false

def stateGuard (rho momentum transverse energy : UInt64) : Bool :=
  narrowStateGuard rho momentum transverse energy || energyGuard rho momentum transverse energy

def rejectedSide : CheckedSideBits := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- Compute one conservative state's thermodynamics and physical flux.
The executable constants are the binary64 encodings nearest to 2/5 and 7/5.
Every input and rounded intermediate is checked before acceptance. -/
def sideCheckedBits (rho momentum transverse energy : UInt64) : CheckedSideBits :=
  if stateGuard rho momentum transverse energy then
    let velocity := LeanExe.Float64.divBits momentum rho
    let transport := LeanExe.Float64.mulBits momentum velocity
    let transverseVelocity := LeanExe.Float64.divBits transverse rho
    let transverseTransport := LeanExe.Float64.mulBits transverse transverseVelocity
    let kineticSum := LeanExe.Float64.addBits transport transverseTransport
    let halfKinetic := LeanExe.Float64.mulBits 0x3FE0000000000000 kineticSum
    let internal := LeanExe.Float64.subBits energy halfKinetic
    if finiteBits velocity && finiteBits transport && finiteBits transverseVelocity &&
        finiteBits transverseTransport && finiteBits kineticSum && finiteBits halfKinetic &&
        positiveBits internal then
      let pressure := LeanExe.Float64.mulBits 0x3FD999999999999A internal
      let pressureOverDensity := LeanExe.Float64.divBits pressure rho
      let radicand := LeanExe.Float64.mulBits 0x3FF6666666666666 pressureOverDensity
      if positiveBits pressure && positiveBits pressureOverDensity &&
          positiveBits radicand then
        let soundSpeed := LeanExe.Float64.sqrtBits radicand
        let speed := LeanExe.Float64.addBits (absBits velocity) soundSpeed
        let momentumFlux := LeanExe.Float64.addBits transport pressure
        let transverseFlux := LeanExe.Float64.mulBits transverse velocity
        let enthalpy := LeanExe.Float64.addBits energy pressure
        let energyFlux := LeanExe.Float64.mulBits velocity enthalpy
        if positiveBits soundSpeed && positiveBits speed && finiteBits momentumFlux &&
            finiteBits transverseFlux && finiteBits enthalpy && finiteBits energyFlux then
          ⟨0, velocity, pressure, speed, momentum, momentumFlux, transverseFlux, energyFlux⟩
        else rejectedSide
      else rejectedSide
    else rejectedSide
  else rejectedSide

end LeanExe.Examples.Euler2DConservative
