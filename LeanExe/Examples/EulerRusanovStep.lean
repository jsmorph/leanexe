import LeanExe.Examples.EulerRusanov

namespace LeanExe.Examples.EulerRusanovStep

/-- Seven-word public result for the fixed two-cell Sod quarter-step.

Status zero means that all three guarded interface-flux calls succeeded and
the remaining fields contain the updated conservative binary64 words.  Status
one means that an interface call rejected; every payload is then positive
zero. -/
structure CheckedSodQuarterStepBits where
  status : UInt64
  leftDensity : UInt64
  leftMomentum : UInt64
  leftEnergy : UInt64
  rightDensity : UInt64
  rightMomentum : UInt64
  rightEnergy : UInt64
  deriving Inhabited

/-- One component of `U - (1/4) * (fluxRight - fluxLeft)`.

Every subtraction is binary64 addition after exact sign-bit toggling.  The
association here is part of the public numerical specification. -/
def quarterUpdateComponentBits
    (state fluxLeft fluxRight : UInt64) : UInt64 :=
  let signMask : UInt64 := 0x8000000000000000
  let quarter : UInt64 := 0x3FD0000000000000
  let fluxDifference :=
    LeanExe.Float64.addBits fluxRight (fluxLeft ^^^ signMask)
  let scaledDifference :=
    LeanExe.Float64.mulBits quarter fluxDifference
  LeanExe.Float64.addBits state (scaledDifference ^^^ signMask)

/-- Fixed first-order transmissive two-cell Sod step.

The primitive states are `(1, 0, 1)` and
`(1/8, 0, binary64(1/10))`.  The initial conservative binary64 states are
`(1, 0, 5/2)` and `(1/8, 0, 1/4)`.  The latter energy is the rounded binary64
conservative value; it must not be identified with exact-real
`(5/2) * binary64(1/10)` without the separate numerical bridge. -/
def sodQuarterStepCheckedBits : CheckedSodQuarterStepBits :=
  let zero : UInt64 := 0x0000000000000000
  let one : UInt64 := 0x3FF0000000000000
  let eighth : UInt64 := 0x3FC0000000000000
  let tenth : UInt64 := 0x3FB999999999999A
  let quarter : UInt64 := 0x3FD0000000000000
  let fiveHalves : UInt64 := 0x4004000000000000

  let leftLeft :=
    LeanExe.Examples.EulerRusanov.rusanovFluxCheckedBits
      one zero one one zero one
  let leftRight :=
    LeanExe.Examples.EulerRusanov.rusanovFluxCheckedBits
      one zero one eighth zero tenth
  let rightRight :=
    LeanExe.Examples.EulerRusanov.rusanovFluxCheckedBits
      eighth zero tenth eighth zero tenth

  if leftLeft.status == zero &&
      leftRight.status == zero &&
      rightRight.status == zero then
    let leftDensity :=
      quarterUpdateComponentBits
        one leftLeft.mass leftRight.mass
    let leftMomentum :=
      quarterUpdateComponentBits
        zero leftLeft.momentum leftRight.momentum
    let leftEnergy :=
      quarterUpdateComponentBits
        fiveHalves leftLeft.energy leftRight.energy
    let rightDensity :=
      quarterUpdateComponentBits
        eighth leftRight.mass rightRight.mass
    let rightMomentum :=
      quarterUpdateComponentBits
        zero leftRight.momentum rightRight.momentum
    let rightEnergy :=
      quarterUpdateComponentBits
        quarter leftRight.energy rightRight.energy
    { status := zero
      leftDensity
      leftMomentum
      leftEnergy
      rightDensity
      rightMomentum
      rightEnergy }
  else
    { status := 1
      leftDensity := zero
      leftMomentum := zero
      leftEnergy := zero
      rightDensity := zero
      rightMomentum := zero
      rightEnergy := zero }

end LeanExe.Examples.EulerRusanovStep
