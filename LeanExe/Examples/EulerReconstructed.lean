import LeanExe.Examples.Euler

/-!
The reconstructed solver for the two-dimensional Euler equations, on the same four-quadrant
problem as the first-order solver.  Each directional update reads five cells, reconstructs three
of them with componentwise minmod slopes and a common scale factor, and evaluates Rusanov fluxes
at the center cell's faces.  A reconstruction whose faces fail the state checks halves the
factor, at most `trials` times, and then uses the cell average.  Signal speeds and the Courant
number are bounded by outward rounding: each operation's binary64 result is moved one step
toward the bound.

The arithmetic follows main's word-level model operation for operation, as the first-order
solver does, and shares its initial cells, conservative update, flux components, acceptance
test, timestep proposal, and output.  Each checked function computes every value and tests the
conjunction of main's checks once, at the end; the float operations are total, so the returned
values and statuses are main's.
-/

namespace LeanExe.Examples.Euler

/-! Outward rounding. -/

/-- A checked value: status 0 with a value, or status 1. -/
structure Checked where
  status : UInt64
  value : Float
  deriving Inhabited

abbrev rejectedChecked : Checked := ⟨1, 0⟩

/-- The next binary64 word above `bits` in value. -/
abbrev nextUpBits (bits : UInt64) : UInt64 :=
  if bits == 0x8000000000000000 then 1 else if bits < 0x8000000000000000 then bits + 1
  else bits - 1

/-- The next binary64 word below `bits` in value. -/
abbrev nextDownBits (bits : UInt64) : UInt64 :=
  if bits == 0 then 0x8000000000000001 else if bits < 0x8000000000000000 then bits - 1
  else bits + 1

/-- A rounded result moved one step up or down, when the result and the step are finite. -/
def endpoint (up : Bool) (rounded : Float) : Checked :=
  let bits := if up then nextUpBits rounded.toBits else nextDownBits rounded.toBits
  if finite rounded && absBits bits < 0x7FF0000000000000 then ⟨0, Float.ofBits bits⟩
  else rejectedChecked

def outAdd (up : Bool) (a b : Float) : Checked :=
  let e := endpoint up (a + b)
  if finite a && finite b && e.status == 0 then e else rejectedChecked

def outSub (up : Bool) (a b : Float) : Checked :=
  let e := endpoint up (a - b)
  if finite a && finite b && e.status == 0 then e else rejectedChecked

def outMul (up : Bool) (a b : Float) : Checked :=
  let e := endpoint up (a * b)
  if finite a && finite b && e.status == 0 then e else rejectedChecked

def outDiv (up : Bool) (a b : Float) : Checked :=
  let e := endpoint up (a / b)
  if finite a && finite b && 0 < absBits b.toBits && e.status == 0 then e else rejectedChecked

def outSqrt (up : Bool) (a : Float) : Checked :=
  let e := endpoint up a.sqrt
  if finite a && a.toBits ≤ 0x8000000000000000 && e.status == 0 then e else rejectedChecked

/-! Outward speed bounds. -/

/-- A lower bound on the kinetic energy `(mx² + my²) / (2ρ)`. -/
def kineticLower (rho mx my : Float) : Checked :=
  let xx := outMul false mx mx
  let yy := outMul false my my
  let sum := outAdd false xx.value yy.value
  let half := outMul false 0.5 sum.value
  let kinetic := outDiv false half.value rho
  if xx.status == 0 && yy.status == 0 && sum.status == 0 && half.status == 0 &&
      kinetic.status == 0 then kinetic
  else rejectedChecked

/-- An upper bound on the pressure. -/
def pressureUpper (rho mx my energy : Float) : Checked :=
  let kinetic := kineticLower rho mx my
  let internal := outSub true energy kinetic.value
  let pressure := outMul true 0.4 internal.value
  if kinetic.status == 0 && internal.status == 0 && pressure.status == 0 then pressure
  else rejectedChecked

/-- An upper bound on the sound speed. -/
def soundUpper (rho mx my energy : Float) : Checked :=
  let pressure := pressureUpper rho mx my energy
  let ratio := outDiv true pressure.value rho
  let radicand := outMul true 1.4000000000000001 ratio.value
  let sound := outSqrt true radicand.value
  if pressure.status == 0 && ratio.status == 0 && radicand.status == 0 && sound.status == 0 then
    sound
  else rejectedChecked

/-- An upper bound on the signal speed `|u| + c` in the direction of `mx`. -/
def speedUpper (rho mx my energy : Float) : Checked :=
  let velocity := outDiv true (Float.ofBits (absBits mx.toBits)) rho
  let sound := soundUpper rho mx my energy
  let speed := outAdd true velocity.value sound.value
  if stateGuard rho mx my energy && velocity.status == 0 && sound.status == 0 &&
      speed.status == 0 then speed
  else rejectedChecked

/-! Fluxes and the update of a cell from its faces. -/

/-- `side` with the outward speed bound as the signal speed. -/
def outwardSide (rho momentum transverse energy : Float) : Side :=
  let speed := speedUpper rho momentum transverse energy
  let velocity := momentum / rho
  let transport := momentum * velocity
  let transverseVelocity := transverse / rho
  let transverseTransport := transverse * transverseVelocity
  let kineticSum := transport + transverseTransport
  let halfKinetic := 0.5 * kineticSum
  let internal := energy - halfKinetic
  let pressure := 0.4 * internal
  let momentumFlux := transport + pressure
  let transverseFlux := transverse * velocity
  let enthalpy := energy + pressure
  let energyFlux := velocity * enthalpy
  if speed.status == 0 &&
      (finite velocity && finite transport && finite transverseVelocity &&
        finite transverseTransport && finite kineticSum && finite halfKinetic &&
        positive internal) &&
      (positive pressure && finite momentumFlux && finite transverseFlux && finite enthalpy &&
        finite energyFlux) then
    ⟨0, velocity, pressure, speed.value, momentum, momentumFlux, transverseFlux, energyFlux⟩
  else rejectedSide

/-- The Rusanov flux between two states with outward speed bounds. -/
def outwardFlux (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : Float) :
    Flux :=
  let left := outwardSide rhoL momentumL transverseL energyL
  let right := outwardSide rhoR momentumR transverseR energyR
  let alpha := if left.speed.toBits ≤ right.speed.toBits then right.speed else left.speed
  let mass := component alpha left.massFlux right.massFlux rhoL rhoR
  let momentum := component alpha left.momentumFlux right.momentumFlux momentumL momentumR
  let transverse := component alpha left.transverseFlux right.transverseFlux transverseL transverseR
  let energy := component alpha left.energyFlux right.energyFlux energyL energyR
  if left.status == 0 && right.status == 0 && mass.status == 0 && momentum.status == 0 &&
      transverse.status == 0 && energy.status == 0 then
    ⟨0, mass.value, momentum.value, transverse.value, energy.value, alpha⟩
  else rejectedFlux

/-- The center state advanced by the fluxes at its faces: the left face between `leftOuter` and
`leftInner`, the right face between `rightInner` and `rightOuter`.  The Courant number is
bounded outward. -/
def faceStep (ratio rho momentum transverse energy
    leftOuterRho leftOuterMomentum leftOuterTransverse leftOuterEnergy
    leftInnerRho leftInnerMomentum leftInnerTransverse leftInnerEnergy
    rightInnerRho rightInnerMomentum rightInnerTransverse rightInnerEnergy
    rightOuterRho rightOuterMomentum rightOuterTransverse rightOuterEnergy : Float) : Updated :=
  let left := outwardFlux leftOuterRho leftOuterMomentum leftOuterTransverse leftOuterEnergy
    leftInnerRho leftInnerMomentum leftInnerTransverse leftInnerEnergy
  let right := outwardFlux rightInnerRho rightInnerMomentum rightInnerTransverse rightInnerEnergy
    rightOuterRho rightOuterMomentum rightOuterTransverse rightOuterEnergy
  let alpha := if left.alpha.toBits ≤ right.alpha.toBits then right.alpha else left.alpha
  let courant := outMul true ratio alpha
  let nextDensity := update ratio rho left.mass right.mass
  let nextMomentum := update ratio momentum left.momentum right.momentum
  let nextTransverse := update ratio transverse left.transverse right.transverse
  let nextEnergy := update ratio energy left.energy right.energy
  let nextSide := outwardSide nextDensity.value nextMomentum.value nextTransverse.value
    nextEnergy.value
  if positive ratio && left.status == 0 && right.status == 0 && positive alpha &&
      (courant.status == 0 && courant.value.toBits ≤ 0x3FE0000000000000) &&
      (nextDensity.status == 0 && nextMomentum.status == 0 && nextTransverse.status == 0 &&
        nextEnergy.status == 0) && nextSide.status == 0 then
    ⟨0, nextDensity.value, nextMomentum.value, nextTransverse.value, nextEnergy.value,
      nextSide.pressure, alpha, courant.value⟩
  else rejectedCell

/-! Reconstruction. -/

/-- Reconstructed face states of a cell, with the scale factor of its slopes. -/
structure Faces where
  status : UInt64
  left : Conserved
  right : Conserved
  factor : Float
  deriving Inhabited

abbrev zeroState : Conserved := ⟨0, 0, 0, 0⟩

abbrev rejectedFaces : Faces := ⟨1, zeroState, zeroState, 0⟩

abbrev finiteState (q : Conserved) : Bool :=
  finite q.density && finite q.mx && finite q.my && finite q.energy

abbrev admissibleState (q : Conserved) : Bool := stateGuard q.density q.mx q.my q.energy

/-- The smaller of two words of the same sign in magnitude, or 0. -/
abbrev minmod (a b : Float) : Float :=
  if (a.toBits < 0x8000000000000000) == (b.toBits < 0x8000000000000000) then
    if absBits a.toBits ≤ absBits b.toBits then a else b
  else 0

/-- A minmod slope, with status 0 when both differences are finite. -/
structure Slope where
  status : UInt64
  state : Conserved
  deriving Inhabited

def slope (left center right : Conserved) : Slope :=
  let backward : Conserved := ⟨center.density - left.density, center.mx - left.mx,
    center.my - left.my, center.energy - left.energy⟩
  let forward : Conserved := ⟨right.density - center.density, right.mx - center.mx,
    right.my - center.my, right.energy - center.energy⟩
  if finiteState backward && finiteState forward then
    ⟨0, ⟨minmod backward.density forward.density, minmod backward.mx forward.mx,
      minmod backward.my forward.my, minmod backward.energy forward.energy⟩⟩
  else ⟨1, zeroState⟩

/-- The faces `center ∓ factor · delta`, with status 0 when they pass the state checks. -/
def candidate (center delta : Conserved) (factor : Float) : Faces :=
  let offset : Conserved := ⟨factor * delta.density, factor * delta.mx, factor * delta.my,
    factor * delta.energy⟩
  let left : Conserved := ⟨center.density - offset.density, center.mx - offset.mx,
    center.my - offset.my, center.energy - offset.energy⟩
  let right : Conserved := ⟨center.density + offset.density, center.mx + offset.mx,
    center.my + offset.my, center.energy + offset.energy⟩
  if finite factor && finiteState offset && admissibleState left && admissibleState right then
    ⟨0, left, right, factor⟩
  else rejectedFaces

/-- One try of the limiter: status 0 with `factor` when its faces pass, or status 1 with half
the factor. -/
def tryFactor (center delta : Conserved) (factor : Float) : UInt64 × Float :=
  if (candidate center delta factor).status == 0 then (0, factor) else (1, 0.5 * factor)

/-- The first factor from 1/2, halving, whose faces pass, within `trials` tries. -/
def limitFactor (trials : UInt64) (center delta : Conserved) : UInt64 × Float :=
  LeanExe.repeatWhile trials ((1 : UInt64), (0.5 : Float)) (fun (status, _) => status != 0)
    (fun (_, factor) => tryFactor center delta factor)

/-- The faces at the first passing factor, or the cell average when no try passes. -/
def limit (trials : UInt64) (center delta : Conserved) : Faces :=
  match limitFactor trials center delta with
  | (status, factor) =>
    if status == 0 then candidate center delta factor else ⟨0, center, center, 0⟩

/-- The reconstructed faces of `center` between its neighbors. -/
def reconstruct (trials : UInt64) (left center right : Conserved) : Faces :=
  let delta := slope left center right
  let faces := limit trials center delta.state
  if admissibleState left && admissibleState center && admissibleState right &&
      delta.status == 0 then faces
  else rejectedFaces

/-- The update of the center of five states from its reconstructed faces. -/
def reconstructedStep (trials : UInt64) (ratio : Float)
    (farLeft left center right farRight : Conserved) : Updated :=
  let leftFaces := reconstruct trials farLeft left center
  let centerFaces := reconstruct trials left center right
  let rightFaces := reconstruct trials center right farRight
  let out := faceStep ratio center.density center.mx center.my center.energy
    leftFaces.right.density leftFaces.right.mx leftFaces.right.my leftFaces.right.energy
    centerFaces.left.density centerFaces.left.mx centerFaces.left.my centerFaces.left.energy
    centerFaces.right.density centerFaces.right.mx centerFaces.right.my centerFaces.right.energy
    rightFaces.left.density rightFaces.left.mx rightFaces.left.my rightFaces.left.energy
  if leftFaces.status == 0 && centerFaces.status == 0 && rightFaces.status == 0 then out
  else rejectedCell

/-! Sweeps. -/

/-- The state as seen along an axis: a y sweep exchanges the momenta. -/
abbrev oriented (axisY : Bool) (q : Conserved) : Conserved :=
  ⟨q.density, if axisY then q.my else q.mx, if axisY then q.mx else q.my, q.energy⟩

/-- One sweep along an axis with reconstruction: each cell advanced by its two faces, from five
cells clamped at the boundary. -/
def reconstructedSweep (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid : Array Cell) : Array Cell :=
  LeanExe.build grid.size.toUInt64 fun index =>
    let cx := index % n
    let cy := index / n
    let coordinate := if axisY then cy else cx
    let stride := if axisY then n else 1
    let lower := if coordinate == 0 then index else index - stride
    let lowerCoordinate := if coordinate == 0 then coordinate else coordinate - 1
    let farLower := if lowerCoordinate == 0 then lower else lower - stride
    let upper := if coordinate + 1 < n then index + stride else index
    let upperCoordinate := if coordinate + 1 < n then coordinate + 1 else coordinate
    let farUpper := if upperCoordinate + 1 < n then upper + stride else upper
    let a := grid[farLower.toNat]!.state
    let b := grid[lower.toNat]!.state
    let c := grid[index.toNat]!.state
    let d := grid[upper.toNat]!.state
    let e := grid[farUpper.toNat]!.state
    let out := reconstructedStep trials ratio (oriented axisY a) (oriented axisY b)
      (oriented axisY c) (oriented axisY d) (oriented axisY e)
    ⟨⟨out.density, if axisY then out.transverse else out.momentum,
      if axisY then out.momentum else out.transverse, out.energy⟩, out.pressure, out.status⟩

/-- The y sweep of an accepted x sweep, or the rejected x sweep. -/
def reconstructedFinish (n trials : UInt64) (ratio : Float) (middle : Array Cell) :
    Array Cell :=
  if accepted middle then reconstructedSweep n true trials ratio middle else middle

def reconstructedStepGrid (n trials : UInt64) (ratio : Float) (grid : Array Cell) : Array Cell :=
  reconstructedFinish n trials ratio (reconstructedSweep n false trials ratio grid)

/-! Timesteps. -/

abbrev mergeChecked (a b : Checked) : Checked :=
  if a.status == 0 && b.status == 0 then
    ⟨0, if a.value.toBits ≤ b.value.toBits then b.value else a.value⟩
  else rejectedChecked

/-- The larger of the speed bounds of a state in both directions. -/
def cellUpper (rho mx my energy : Float) : Checked :=
  let x := speedUpper rho mx my energy
  let y := speedUpper rho my mx energy
  mergeChecked x y

/-- The largest speed bound over the grid, or status 1 when a cell fails. -/
def gridUpper (grid : Array Cell) : Checked :=
  match LeanExe.loop grid.size.toUInt64 ((0 : UInt64), (0 : Float)) fun i acc =>
      let q := grid[i.toNat]!.state
      let c := cellUpper q.density q.mx q.my q.energy
      (if acc.1 == 0 && c.status == 0 then 0 else 1,
        if acc.1 == 0 && c.status == 0 then
          (if acc.2.toBits ≤ c.value.toBits then c.value else acc.2)
        else 0) with
  | (status, value) => ⟨status, value⟩

/-- The ratio `dt / h`, bounded above, with status 0 when the Courant number, bounded above, is
at most 1/2. -/
def gridRatio (n : UInt64) (dt alpha : Float) : Checked :=
  let spacing := outDiv false 1 n.toFloat
  let ratio := outDiv true dt spacing.value
  let courant := outMul true ratio.value alpha
  if 2 ≤ n && n ≤ 800 && spacing.status == 0 && positive dt && positive spacing.value &&
      positive alpha && ratio.status == 0 && courant.status == 0 &&
      courant.value.toBits ≤ 0x3FE0000000000000 then ratio
  else rejectedChecked

/-- One try of a timestep with the given ratio: status 0 with the new grid, which replaces
`grid`, or 9 to retry with half the timestep, keeping `grid`. -/
def reconstructedTry (n trials : UInt64) (grid : Array Cell) (ratio dt : Float) :
    UInt64 × Float × Array Cell :=
  let trial := reconstructedStepGrid n trials ratio grid
  if accepted trial then (0, dt, trial) else (9, 0.5 * dt, grid)

def reconstructedAttempt (n trials : UInt64) (time alpha dt : Float) (grid : Array Cell) :
    UInt64 × Float × Array Cell :=
  let ratio := gridRatio n dt alpha
  if validAdvance time dt then
    if ratio.status == 0 then reconstructedTry n trials grid ratio.value dt
    else (9, 0.5 * dt, grid)
  else (3, dt, grid)

/-- Tries `dt` from `time`, halving it after each rejected try, at most 2048 times, and then
advances, or returns `grid` with the status of the failure.  The loop state holds `grid` until a
try replaces it. -/
def reconstructedAdvanceWith (n trials : UInt64) (time dt alpha : Float) (grid : Array Cell) :
    UInt64 × Float × Array Cell :=
  match LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid)
      (fun (status, _, _) => status == 9)
      (fun (_, dt, g) => reconstructedAttempt n trials time alpha dt g) with
  | (status, dt, g) =>
    if status == 0 then (0, time + dt, g)
    else (if status == 9 then 4 else status, time, g)

/-- One accepted timestep, or the state with a nonzero status. -/
def reconstructedAdvanceStep (n trials : UInt64) (time : Float) (grid : Array Cell) :
    UInt64 × Float × Array Cell :=
  let stats := gridUpper grid
  if stats.status == 0 then
    reconstructedAdvanceWith n trials time (proposal n time stats.value) stats.value grid
  else (2, time, grid)

/-- Steps from time 0 until the time is 0.8, with status 0 when every step succeeds and 5 when
the fuel runs out first. -/
def reconstructedRunFrom (n trials : UInt64) : UInt64 × Float × Array Cell :=
  match LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n)
      (fun (status, time, _) => status == 0 && time.toBits != endTime.toBits)
      (fun (_, time, grid) => reconstructedAdvanceStep n trials time grid) with
  | (status, time, grid) =>
    if status == 0 && time.toBits != endTime.toBits then (5, time, grid)
    else (status, time, grid)

def reconstructedRun (n trials : UInt64) : UInt64 × Float × Array Cell :=
  if 2 ≤ n && n ≤ 800 then reconstructedRunFrom n trials else (1, 0, #[])

def reconstructedSolve (n trials : UInt64) : Array UInt64 :=
  match reconstructedRun n trials with
  | (status, time, grid) => pack n status time grid

end LeanExe.Examples.Euler
