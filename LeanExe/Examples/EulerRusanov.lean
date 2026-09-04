import LeanExe.Float64

namespace LeanExe.Examples.EulerRusanov

/-- Four-word public result for the guarded Euler numerical flux.  Status zero
means that the remaining fields contain computed binary64 words; status one
means that an input failed the raw-bit domain check and every payload is zero. -/
structure CheckedFluxBits where
  status : UInt64
  mass : UInt64
  momentum : UInt64
  energy : UInt64
  deriving Inhabited

/-- Guarded one-dimensional ideal-gas Rusanov flux over primitive states.

The inputs are raw binary64 words for `(rhoL, uL, pL, rhoR, uR, pR)`.  The
integer-only guard admits

* `1/8 <= rho <= 1`,
* `1/16 <= p <= rho`, and
* `|u| <= 1/2`.

The accepted path uses `gamma = 7/5` and the fixed certified signal bound
`alpha = 7/4`.  Its dyadic evaluation order avoids large floating-point
constants: pressure multiples are sums of `p` and `p/2`, while `alpha/2` is
evaluated as `1/2 + 1/4 + 1/8` times each conservative-state jump.  This is
the same exact-real Rusanov formula while keeping the rounded intermediates in
the ranges covered by the proof library. -/
def rusanovFluxCheckedBits
    (rhoL uL pL rhoR uR pR : UInt64) : CheckedFluxBits :=
  if decide ((0x3FC0000000000000 : UInt64) ≤ rhoL) &&
      decide (rhoL ≤ (0x3FF0000000000000 : UInt64)) &&
      decide ((0x3FB0000000000000 : UInt64) ≤ pL) &&
      decide (pL ≤ rhoL) &&
      decide ((uL &&& (0x7FFFFFFFFFFFFFFF : UInt64)) ≤
        (0x3FE0000000000000 : UInt64)) &&
      decide ((0x3FC0000000000000 : UInt64) ≤ rhoR) &&
      decide (rhoR ≤ (0x3FF0000000000000 : UInt64)) &&
      decide ((0x3FB0000000000000 : UInt64) ≤ pR) &&
      decide (pR ≤ rhoR) &&
      decide ((uR &&& (0x7FFFFFFFFFFFFFFF : UInt64)) ≤
        (0x3FE0000000000000 : UInt64)) then
    let half : UInt64 := 0x3FE0000000000000
    let quarter : UInt64 := 0x3FD0000000000000
    let eighth : UInt64 := 0x3FC0000000000000
    let signMask : UInt64 := 0x8000000000000000

    let massL := LeanExe.Float64.mulBits rhoL uL
    let velocitySquaredMassL := LeanExe.Float64.mulBits massL uL
    let halfKineticL := LeanExe.Float64.mulBits half velocitySquaredMassL
    let halfPressureL := LeanExe.Float64.mulBits half pL
    let twoPressureL := LeanExe.Float64.addBits pL pL
    let energyPressureL := LeanExe.Float64.addBits twoPressureL halfPressureL
    let energyL := LeanExe.Float64.addBits energyPressureL halfKineticL
    let enthalpyPressureL := LeanExe.Float64.addBits energyPressureL pL
    let enthalpyL := LeanExe.Float64.addBits enthalpyPressureL halfKineticL
    let momentumFluxL := LeanExe.Float64.addBits velocitySquaredMassL pL
    let energyFluxL := LeanExe.Float64.mulBits enthalpyL uL

    let massR := LeanExe.Float64.mulBits rhoR uR
    let velocitySquaredMassR := LeanExe.Float64.mulBits massR uR
    let halfKineticR := LeanExe.Float64.mulBits half velocitySquaredMassR
    let halfPressureR := LeanExe.Float64.mulBits half pR
    let twoPressureR := LeanExe.Float64.addBits pR pR
    let energyPressureR := LeanExe.Float64.addBits twoPressureR halfPressureR
    let energyR := LeanExe.Float64.addBits energyPressureR halfKineticR
    let enthalpyPressureR := LeanExe.Float64.addBits energyPressureR pR
    let enthalpyR := LeanExe.Float64.addBits enthalpyPressureR halfKineticR
    let momentumFluxR := LeanExe.Float64.addBits velocitySquaredMassR pR
    let energyFluxR := LeanExe.Float64.mulBits enthalpyR uR

    let massJump := LeanExe.Float64.addBits rhoL (rhoR ^^^ signMask)
    let massMean := LeanExe.Float64.mulBits half
      (LeanExe.Float64.addBits massL massR)
    let massDissipation := LeanExe.Float64.addBits
      (LeanExe.Float64.addBits
        (LeanExe.Float64.mulBits half massJump)
        (LeanExe.Float64.mulBits quarter massJump))
      (LeanExe.Float64.mulBits eighth massJump)
    let massFlux := LeanExe.Float64.addBits massMean massDissipation

    let momentumJump := LeanExe.Float64.addBits massL (massR ^^^ signMask)
    let momentumMean := LeanExe.Float64.mulBits half
      (LeanExe.Float64.addBits momentumFluxL momentumFluxR)
    let momentumDissipation := LeanExe.Float64.addBits
      (LeanExe.Float64.addBits
        (LeanExe.Float64.mulBits half momentumJump)
        (LeanExe.Float64.mulBits quarter momentumJump))
      (LeanExe.Float64.mulBits eighth momentumJump)
    let momentumFlux := LeanExe.Float64.addBits momentumMean momentumDissipation

    let energyJump := LeanExe.Float64.addBits energyL (energyR ^^^ signMask)
    let energyMean := LeanExe.Float64.mulBits half
      (LeanExe.Float64.addBits energyFluxL energyFluxR)
    let energyDissipation := LeanExe.Float64.addBits
      (LeanExe.Float64.addBits
        (LeanExe.Float64.mulBits half energyJump)
        (LeanExe.Float64.mulBits quarter energyJump))
      (LeanExe.Float64.mulBits eighth energyJump)
    let energyFlux := LeanExe.Float64.addBits energyMean energyDissipation

    { status := 0, mass := massFlux, momentum := momentumFlux,
      energy := energyFlux }
  else
    { status := 1, mass := 0, momentum := 0, energy := 0 }

end LeanExe.Examples.EulerRusanov
