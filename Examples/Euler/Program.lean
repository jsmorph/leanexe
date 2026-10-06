import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop
import LeanExe.Dialect.RepeatWhile

/-!
A first-order finite-volume solver for the two-dimensional Euler equations, on the four-quadrant
Riemann problem of the unit square.  Each cell holds density, both momenta, and total energy.  A
step is an x sweep followed by a y sweep, each cell updated from Rusanov fluxes at its two
interfaces, with transmissive boundaries by clamped neighbor indices.  The timestep targets CFL 0.4,
and a step whose cells fail a check is retried with half the timestep.

The arithmetic follows the earlier system's word-level model operation for operation, so that the
output words can be compared bit for bit: every float operation here is one binary64 operation, and
the checks inspect bit patterns as the earlier system's do.  Where the earlier system tests a check
before computing the next value, these functions compute every value and test the conjunction of the
checks once, at the end.  The float operations are total, so the returned values and statuses are
the earlier system's.
-/

namespace Examples.Euler

structure Conserved where
  density : Float
  mx : Float
  my : Float
  energy : Float
  deriving Inhabited

structure Cell where
  state : Conserved
  pressure : Float
  status : UInt64
  deriving Inhabited

abbrev absBits (bits : UInt64) : UInt64 := bits &&& 0x7FFFFFFFFFFFFFFF

/-- Neither infinite nor NaN. -/
abbrev finite (x : Float) : Bool := absBits x.toBits < 0x7FF0000000000000

/-- Positive and finite: a positive subnormal or normal number. -/
abbrev positive (x : Float) : Bool := 0 < x.toBits && x.toBits < 0x7FF0000000000000

/-- A state whose momenta are at most its density in magnitude and whose energy exceeds its
density has positive internal energy. -/
abbrev narrowGuard (rho momentum transverse energy : Float) : Bool :=
  positive rho && finite momentum && finite transverse && positive energy &&
    absBits momentum.toBits ≤ rho.toBits && absBits transverse.toBits ≤ rho.toBits &&
    rho.toBits < energy.toBits

abbrev exponentBits (bits : UInt64) : UInt64 := absBits bits >>> 52

abbrev maxWord (a b : UInt64) : UInt64 := if a < b then b else a

abbrev topExponent (rho mx my energy : Float) : UInt64 :=
  maxWord (maxWord (exponentBits rho.toBits) (exponentBits mx.toBits))
    (maxWord (exponentBits my.toBits) (exponentBits energy.toBits))

abbrev normalizable (x : Float) (top : UInt64) : Bool :=
  absBits x.toBits == 0 ||
    (0 < exponentBits x.toBits && top < exponentBits x.toBits + 1021)

/-- `x` scaled by a power of two so that the largest exponent among the four components is
1021, which keeps the residual below from overflowing.  For a normalizable `x` the word's
exponent field lies from 1 to 1021; any other word with an exponent field of all ones gives 0,
so the value is never built from a NaN pattern. -/
def normalized (x : Float) (top : UInt64) : Float :=
  let w := (exponentBits x.toBits + 1021 - top) <<< 52 + (x.toBits &&& 0x000FFFFFFFFFFFFF)
  if absBits x.toBits == 0 || (w >>> 52) &&& 0x7FF == 0x7FF then 0 else Float.ofBits w

abbrev energyResidual (rho mx my energy : Float) : Float :=
  rho * energy - 0.5 * (mx * mx + my * my)

/-- The internal energy `ρE - |m|²/2`, computed on the normalized components, is positive by a
margin. -/
def energyGuard (rho mx my energy : Float) : Bool :=
  let top := topExponent rho mx my energy
  let result := energyResidual (normalized rho top) (normalized mx top) (normalized my top)
    (normalized energy top)
  (positive rho && finite mx && finite my && positive energy) &&
    (normalizable rho top && normalizable mx top && normalizable my top &&
      normalizable energy top) &&
    (positive result && 0x3CE0000000000000 < result.toBits)

abbrev stateGuard (rho momentum transverse energy : Float) : Bool :=
  narrowGuard rho momentum transverse energy || energyGuard rho momentum transverse energy

/-- One state's thermodynamics and physical flux in the direction of `momentum`, with status 0
when every input and intermediate passes its check. -/
structure Side where
  status : UInt64
  velocity : Float
  pressure : Float
  speed : Float
  massFlux : Float
  momentumFlux : Float
  transverseFlux : Float
  energyFlux : Float
  deriving Inhabited

abbrev rejectedSide : Side := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

def side (rho momentum transverse energy : Float) : Side :=
  let velocity := momentum / rho
  let transport := momentum * velocity
  let transverseVelocity := transverse / rho
  let transverseTransport := transverse * transverseVelocity
  let kineticSum := transport + transverseTransport
  let halfKinetic := 0.5 * kineticSum
  let internal := energy - halfKinetic
  let pressure := 0.4 * internal
  let pressureOverDensity := pressure / rho
  let radicand := 1.4 * pressureOverDensity
  let soundSpeed := radicand.sqrt
  let speed := velocity.abs + soundSpeed
  let momentumFlux := transport + pressure
  let transverseFlux := transverse * velocity
  let enthalpy := energy + pressure
  let energyFlux := velocity * enthalpy
  if stateGuard rho momentum transverse energy &&
      (finite velocity && finite transport && finite transverseVelocity &&
        finite transverseTransport && finite kineticSum && finite halfKinetic &&
        positive internal) &&
      (positive pressure && positive pressureOverDensity && positive radicand) &&
      (positive soundSpeed && positive speed && finite momentumFlux &&
        finite transverseFlux && finite enthalpy && finite energyFlux) then
    ⟨0, velocity, pressure, speed, momentum, momentumFlux, transverseFlux, energyFlux⟩
  else rejectedSide

structure Component where
  status : UInt64
  value : Float
  deriving Inhabited

abbrev rejectedComponent : Component := ⟨1, 0⟩

/-- One Rusanov flux component. -/
def component (alpha fluxL fluxR stateL stateR : Float) : Component :=
  let sum := fluxL + fluxR
  let mean := 0.5 * sum
  let jump := stateR - stateL
  let viscosity := alpha * jump
  let halfViscosity := 0.5 * viscosity
  let value := mean - halfViscosity
  if (positive alpha && finite fluxL && finite fluxR && finite stateL && finite stateR) &&
      (finite sum && finite mean && finite jump && finite viscosity && finite halfViscosity &&
        finite value) then ⟨0, value⟩
  else rejectedComponent

structure Flux where
  status : UInt64
  mass : Float
  momentum : Float
  transverse : Float
  energy : Float
  alpha : Float
  deriving Inhabited

abbrev rejectedFlux : Flux := ⟨1, 0, 0, 0, 0, 0⟩

/-- The Rusanov flux between two states, with the larger signal speed. -/
def flux (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : Float) :
    Flux :=
  let left := side rhoL momentumL transverseL energyL
  let right := side rhoR momentumR transverseR energyR
  let alpha := if left.speed.toBits ≤ right.speed.toBits then right.speed else left.speed
  let mass := component alpha left.massFlux right.massFlux rhoL rhoR
  let momentum := component alpha left.momentumFlux right.momentumFlux momentumL momentumR
  let transverse := component alpha left.transverseFlux right.transverseFlux transverseL transverseR
  let energy := component alpha left.energyFlux right.energyFlux energyL energyR
  if left.status == 0 && right.status == 0 && mass.status == 0 && momentum.status == 0 &&
      transverse.status == 0 && energy.status == 0 then
    ⟨0, mass.value, momentum.value, transverse.value, energy.value, alpha⟩
  else rejectedFlux

/-- One conservative update. -/
def update (ratio state fluxL fluxR : Float) : Component :=
  let difference := fluxR - fluxL
  let increment := ratio * difference
  let value := state - increment
  if (positive ratio && finite state && finite fluxL && finite fluxR) &&
      (finite difference && finite increment && finite value) then ⟨0, value⟩
  else rejectedComponent

structure Updated where
  status : UInt64
  density : Float
  momentum : Float
  transverse : Float
  energy : Float
  pressure : Float
  alpha : Float
  courant : Float
  deriving Inhabited

abbrev rejectedCell : Updated := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- The center state advanced by its two interfaces, with the Courant number checked against
1/2. -/
def advanceCell (ratio rhoL momentumL transverseL energyL rho momentum transverse energy
    rhoR momentumR transverseR energyR : Float) : Updated :=
  let left := flux rhoL momentumL transverseL energyL rho momentum transverse energy
  let right := flux rho momentum transverse energy rhoR momentumR transverseR energyR
  let alpha := if left.alpha.toBits ≤ right.alpha.toBits then right.alpha else left.alpha
  let courant := ratio * alpha
  let nextDensity := update ratio rho left.mass right.mass
  let nextMomentum := update ratio momentum left.momentum right.momentum
  let nextTransverse := update ratio transverse left.transverse right.transverse
  let nextEnergy := update ratio energy left.energy right.energy
  let nextSide := side nextDensity.value nextMomentum.value nextTransverse.value nextEnergy.value
  if positive ratio && left.status == 0 && right.status == 0 &&
      (positive courant && courant.toBits ≤ 0x3FE0000000000000) &&
      (nextDensity.status == 0 && nextMomentum.status == 0 && nextTransverse.status == 0 &&
        nextEnergy.status == 0) && nextSide.status == 0 then
    ⟨0, nextDensity.value, nextMomentum.value, nextTransverse.value, nextEnergy.value,
      nextSide.pressure, alpha, courant⟩
  else rejectedCell

/-! Initial data: the four quadrants, with the cells cut by the interfaces at x = y = 0.8
holding area averages. -/

abbrev conservative (pressure density u v : Float) : Conserved :=
  ⟨density, density * u, density * v, pressure / 0.4 + 0.5 * density * (u * u + v * v)⟩

abbrev bottomLeft : Conserved := conservative 0.029 0.138 1.206 1.206
abbrev bottomRight : Conserved := conservative 0.3 0.5323 0 1.206
abbrev topLeft : Conserved := conservative 0.3 0.5323 1.206 0
abbrev topRight : Conserved := conservative 1.5 1.5 0 0

/-- `k / 5` for `k` from 0 to 5. -/
abbrev fifths (k : UInt64) : Float :=
  if k == 0 then 0 else if k == 1 then 0.2 else if k == 2 then 0.4 else if k == 3 then 0.6
  else if k == 4 then 0.8 else 1

abbrev weightedComponent (x y bl br tl tr : Float) : Float :=
  let right := 1 - x
  let top := 1 - y
  x * y * bl + right * y * br + x * top * tl + right * top * tr

/-- The share, in fifths, of the cell at `coordinate` that lies below the interface at 0.8. -/
abbrev lowerFifths (n coordinate : UInt64) : UInt64 :=
  if 5 * coordinate ≤ 4 * n then min 5 (4 * n - 5 * coordinate) else 0

def initialCell (n index : UInt64) : Cell :=
  let cx := index % n
  let cy := index / n
  let x := fifths (lowerFifths n cx)
  let y := fifths (lowerFifths n cy)
  let q : Conserved :=
    ⟨weightedComponent x y bottomLeft.density bottomRight.density topLeft.density
        topRight.density,
      weightedComponent x y bottomLeft.mx bottomRight.mx topLeft.mx topRight.mx,
      weightedComponent x y bottomLeft.my bottomRight.my topLeft.my topRight.my,
      weightedComponent x y bottomLeft.energy bottomRight.energy topLeft.energy
        topRight.energy⟩
  let out := side q.density q.mx q.my q.energy
  ⟨q, out.pressure, out.status⟩

def initialCells (n : UInt64) : Array Cell := LeanExe.build (n * n) (initialCell n)

/-! Sweeps. -/

/-- One sweep along an axis: each cell advanced by its two interfaces.  A y sweep exchanges
the momenta on the way in and out. -/
def sweep (n : UInt64) (axisY : Bool) (ratio : Float) (grid : Array Cell) : Array Cell :=
  LeanExe.build grid.size.toUInt64 fun index =>
    -- The neighbors along the axis, clamped at the boundary.
    let cx := index % n
    let cy := index / n
    let coordinate := if axisY then cy else cx
    let stride := if axisY then n else 1
    let lower := if coordinate == 0 then index else index - stride
    let upper := if coordinate + 1 < n then index + stride else index
    let l := grid[lower.toNat]!.state
    let c := grid[index.toNat]!.state
    let r := grid[upper.toNat]!.state
    let out := advanceCell ratio
      l.density (if axisY then l.my else l.mx) (if axisY then l.mx else l.my) l.energy
      c.density (if axisY then c.my else c.mx) (if axisY then c.mx else c.my) c.energy
      r.density (if axisY then r.my else r.mx) (if axisY then r.mx else r.my) r.energy
    ⟨⟨out.density, if axisY then out.transverse else out.momentum,
      if axisY then out.momentum else out.transverse, out.energy⟩, out.pressure, out.status⟩

/-- Whether every cell's status is 0. -/
def accepted (grid : Array Cell) : Bool :=
  LeanExe.loop grid.size.toUInt64 true fun i ok => ok && grid[i.toNat]!.status == 0

/-- The y sweep of an accepted x sweep, or the rejected x sweep. -/
def finishStep (n : UInt64) (ratio : Float) (middle : Array Cell) : Array Cell :=
  if accepted middle then sweep n true ratio middle else middle

def step (n : UInt64) (ratio : Float) (grid : Array Cell) : Array Cell :=
  finishStep n ratio (sweep n false ratio grid)

/-! Timesteps. -/

abbrev endTime : Float := 0.8

abbrev spacing (n : UInt64) : Float := 1 / n.toFloat

/-- The status of a scan, nonzero when some cell fails a check, and the largest signal speed. -/
def scan (grid : Array Cell) : UInt64 × Float :=
  LeanExe.loop grid.size.toUInt64 (0, 0) fun i acc =>
    let q := grid[i.toNat]!.state
    let x := side q.density q.mx q.my q.energy
    let y := side q.density q.my q.mx q.energy
    let speed := if x.speed.toBits < y.speed.toBits then y.speed else x.speed
    (acc.1 ||| x.status ||| y.status, if acc.2.toBits < speed.toBits then speed else acc.2)

abbrev proposal (n : UInt64) (time alpha : Float) : Float :=
  let a := 0.4 * spacing n / alpha
  let b := endTime - time
  if a.toBits ≤ b.toBits then a else b

abbrev validAdvance (time dt : Float) : Bool :=
  positive dt && time.toBits < (time + dt).toBits && (time + dt).toBits ≤ endTime.toBits

/-- One try of a timestep: status 0 with the new grid, which replaces `grid`, or 9 to retry with
half the timestep, keeping `grid`. -/
def tryStep (n : UInt64) (grid : Array Cell) (dt : Float) : UInt64 × Float × Array Cell :=
  let trial := step n (dt / spacing n) grid
  if accepted trial then (0, dt, trial) else (9, 0.5 * dt, grid)

/-- `tryStep`, or status 3 and `grid` when the timestep is not a valid advance. -/
def attempt (n : UInt64) (time dt : Float) (grid : Array Cell) : UInt64 × Float × Array Cell :=
  if validAdvance time dt then tryStep n grid dt else (3, dt, grid)

/-- Tries `dt` from `time`, halving it after each rejected try, at most 2048 times, and then
advances, or returns `grid` with the status of the failure: 3 for an invalid timestep and 4 when
the tries run out.  The loop state holds `grid` until a try replaces it. -/
def advanceWith (n : UInt64) (time dt : Float) (grid : Array Cell) :
    UInt64 × Float × Array Cell :=
  match LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid)
      (fun (status, _, _) => status == 9)
      (fun (_, dt, g) => attempt n time dt g) with
  | (status, dt, g) =>
    if status == 0 then (0, time + dt, g)
    else (if status == 9 then 4 else status, time, g)

/-- One accepted timestep, or the state with a nonzero status. -/
def advanceStep (n status : UInt64) (time : Float) (grid : Array Cell) :
    UInt64 × Float × Array Cell :=
  let stats := scan grid
  if stats.1 == 0 then advanceWith n time (proposal n time stats.2) grid
  else (2, time, grid)

/-- Steps from time 0 until the time is 0.8, with status 0 when every step succeeds and 5 when
the fuel runs out first. -/
def runFrom (n : UInt64) : UInt64 × Float × Array Cell :=
  match LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n)
      (fun (status, time, _) => status == 0 && time.toBits != endTime.toBits)
      (fun (status, time, grid) => advanceStep n status time grid) with
  | (status, time, grid) =>
    if status == 0 && time.toBits != endTime.toBits then (5, time, grid)
    else (status, time, grid)

def run (n : UInt64) : UInt64 × Float × Array Cell :=
  if 2 ≤ n && n ≤ 800 then runFrom n else (1, 0, #[])

/-- The status, the time's bits, `n` twice, the densities, and the pressures. -/
def pack (n status : UInt64) (time : Float) (grid : Array Cell) : Array UInt64 :=
  let k := grid.size.toUInt64
  LeanExe.build (4 + 2 * k) fun i =>
    if i == 0 then status else if i == 1 then time.toBits else if i < 4 then n
    else if i < 4 + k then grid[(i - 4).toNat]!.state.density.toBits
    else grid[(i - 4 - k).toNat]!.pressure.toBits

def solve (n : UInt64) : Array UInt64 :=
  match run n with
  | (status, time, grid) => pack n status time grid

end Examples.Euler
