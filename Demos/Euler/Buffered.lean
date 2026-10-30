import Demos.Euler.ReconstructedProgram

/-! The Euler solvers with three grids in the states of their loops.  A sweep writes its cells into
a grid of the state with `set!`, and an accepted try rotates the three grids, so that the compiled
solvers allocate three grids and the packed result for a whole run.  `solve` and
`reconstructedSolve` keep the names of the solvers that they equal, as
`Demos.Euler.Buffered.solve_eq` and `reconstructedSolve_eq` state, so that the verified module
exports them under those names. -/

namespace Demos.Euler.Buffered

/-- `Demos.Euler.sweep` written into the cells of `out`, in place. -/
def sweepInto (n : UInt64) (axisY : Bool) (ratio : Float) (grid out : Array Cell) : Array Cell :=
  LeanExe.loop grid.size.toUInt64 out fun index acc =>
    let cx := index % n
    let cy := index / n
    let coordinate := if axisY then cy else cx
    let stride := if axisY then n else 1
    let lower := if coordinate == 0 then index else index - stride
    let upper := if coordinate + 1 < n then index + stride else index
    let l := grid[lower.toNat]!.state
    let c := grid[index.toNat]!.state
    let r := grid[upper.toNat]!.state
    let o := advanceCell ratio
      l.density (if axisY then l.my else l.mx) (if axisY then l.mx else l.my) l.energy
      c.density (if axisY then c.my else c.mx) (if axisY then c.mx else c.my) c.energy
      r.density (if axisY then r.my else r.mx) (if axisY then r.mx else r.my) r.energy
    acc.set! index.toNat ⟨⟨o.density, if axisY then o.transverse else o.momentum,
      if axisY then o.momentum else o.transverse, o.energy⟩, o.pressure, o.status⟩

/-- `Demos.Euler.tryStep` with the x sweep into `a`, the y sweep into `b`, and a rotation of the
three grids when the try is accepted: status 0 with the new grid first, or 9 with `grid` first. -/
def tryInto (n : UInt64) (grid a b : Array Cell) (dt : Float) :
    UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  let ratio := dt / spacing n
  let a := sweepInto n false ratio grid a
  if accepted a then
    let b := sweepInto n true ratio a b
    if accepted b then (0, dt, b, a, grid) else (9, 0.5 * dt, grid, a, b)
  else (9, 0.5 * dt, grid, a, b)

/-- `Demos.Euler.attempt` on three grids. -/
def attemptInto (n : UInt64) (time dt : Float) (grid a b : Array Cell) :
    UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  if validAdvance time dt then tryInto n grid a b dt else (3, dt, grid, a, b)

/-- `Demos.Euler.advanceWith` on three grids. -/
def advanceInto (n : UInt64) (time dt : Float) (grid a b : Array Cell) :
    UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  match LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid, a, b)
      (fun (status, _, _, _, _) => status == 9)
      (fun (_, dt, g, a, b) => attemptInto n time dt g a b) with
  | (status, dt, g, a, b) =>
    if status == 0 then (0, time + dt, g, a, b)
    else (if status == 9 then 4 else status, time, g, a, b)

/-- `Demos.Euler.advanceStep` on three grids. -/
def stepInto (n : UInt64) (time : Float) (grid a b : Array Cell) :
    UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  let stats := scan grid
  if stats.1 == 0 then advanceInto n time (proposal n time stats.2) grid a b
  else (2, time, grid, a, b)

/-- `Demos.Euler.runFrom` on three grids, each of which starts as the initial grid. -/
def runFromInto (n : UInt64) : UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  match LeanExe.repeatWhile 4294967296
      ((0 : UInt64), (0 : Float), initialCells n, initialCells n, initialCells n)
      (fun (status, time, _, _, _) => status == 0 && time.toBits != endTime.toBits)
      (fun (_, time, grid, a, b) => stepInto n time grid a b) with
  | (status, time, grid, a, b) =>
    if status == 0 && time.toBits != endTime.toBits then (5, time, grid, a, b)
    else (status, time, grid, a, b)

/-- `Demos.Euler.run` through `runFromInto`. -/
def runInto (n : UInt64) : UInt64 × Float × Array Cell :=
  if 2 ≤ n && n ≤ 800 then
    match runFromInto n with
    | (status, time, grid, _, _) => (status, time, grid)
  else (1, 0, #[])

/-- `Demos.Euler.solve` through `runInto`. -/
def solve (n : UInt64) : Array UInt64 :=
  match runInto n with
  | (status, time, grid) => pack n status time grid

/-- `Demos.Euler.reconstructedSweep` written into the cells of `out`, in place. -/
def reconstructedSweepInto (n : UInt64) (axisY : Bool) (trials : UInt64) (ratio : Float)
    (grid out : Array Cell) : Array Cell :=
  LeanExe.loop grid.size.toUInt64 out fun index acc =>
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
    let o := reconstructedStep trials ratio (oriented axisY a) (oriented axisY b)
      (oriented axisY c) (oriented axisY d) (oriented axisY e)
    acc.set! index.toNat ⟨⟨o.density, if axisY then o.transverse else o.momentum,
      if axisY then o.momentum else o.transverse, o.energy⟩, o.pressure, o.status⟩

/-- `Demos.Euler.reconstructedTry` with the x sweep into `a`, the y sweep into `b`, and a rotation
of the three grids when the try is accepted. -/
def reconstructedTryInto (n trials : UInt64) (grid a b : Array Cell) (ratio dt : Float) :
    UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  let a := reconstructedSweepInto n false trials ratio grid a
  if accepted a then
    let b := reconstructedSweepInto n true trials ratio a b
    if accepted b then (0, dt, b, a, grid) else (9, 0.5 * dt, grid, a, b)
  else (9, 0.5 * dt, grid, a, b)

/-- `Demos.Euler.reconstructedAttempt` on three grids. -/
def reconstructedAttemptInto (n trials : UInt64) (time alpha dt : Float) (grid a b : Array Cell) :
    UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  let ratio := gridRatio n dt alpha
  if validAdvance time dt then
    if ratio.status == 0 then reconstructedTryInto n trials grid a b ratio.value dt
    else (9, 0.5 * dt, grid, a, b)
  else (3, dt, grid, a, b)

/-- `Demos.Euler.reconstructedAdvanceWith` on three grids. -/
def reconstructedAdvanceInto (n trials : UInt64) (time dt alpha : Float) (grid a b : Array Cell) :
    UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  match LeanExe.repeatWhile 2048 ((9 : UInt64), dt, grid, a, b)
      (fun (status, _, _, _, _) => status == 9)
      (fun (_, dt, g, a, b) => reconstructedAttemptInto n trials time alpha dt g a b) with
  | (status, dt, g, a, b) =>
    if status == 0 then (0, time + dt, g, a, b)
    else (if status == 9 then 4 else status, time, g, a, b)

/-- `Demos.Euler.reconstructedAdvanceStep` on three grids. -/
def reconstructedStepInto (n trials : UInt64) (time : Float) (grid a b : Array Cell) :
    UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  let stats := gridUpper grid
  if stats.status == 0 then
    reconstructedAdvanceInto n trials time (proposal n time stats.value) stats.value grid a b
  else (2, time, grid, a, b)

/-- `Demos.Euler.reconstructedRunFrom` on three grids, each of which starts as the initial
grid. -/
def reconstructedRunFromInto (n trials : UInt64) :
    UInt64 × Float × Array Cell × Array Cell × Array Cell :=
  match LeanExe.repeatWhile 4294967296
      ((0 : UInt64), (0 : Float), initialCells n, initialCells n, initialCells n)
      (fun (status, time, _, _, _) => status == 0 && time.toBits != endTime.toBits)
      (fun (_, time, grid, a, b) => reconstructedStepInto n trials time grid a b) with
  | (status, time, grid, a, b) =>
    if status == 0 && time.toBits != endTime.toBits then (5, time, grid, a, b)
    else (status, time, grid, a, b)

/-- `Demos.Euler.reconstructedRun` through `reconstructedRunFromInto`. -/
def reconstructedRunInto (n trials : UInt64) : UInt64 × Float × Array Cell :=
  if 2 ≤ n && n ≤ 800 then
    match reconstructedRunFromInto n trials with
    | (status, time, grid, _, _) => (status, time, grid)
  else (1, 0, #[])

/-- `Demos.Euler.reconstructedSolve` through `reconstructedRunInto`. -/
def reconstructedSolve (n trials : UInt64) : Array UInt64 :=
  match reconstructedRunInto n trials with
  | (status, time, grid) => pack n status time grid

end Demos.Euler.Buffered
