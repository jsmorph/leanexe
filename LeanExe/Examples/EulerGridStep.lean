import LeanExe.Examples.EulerCellStep

namespace LeanExe.Examples.EulerGridStep
open LeanExe.Examples.EulerConservative (positiveBits sideCheckedBits)
open LeanExe.Examples.EulerCellStep (cellCheckedBits)

structure CheckedSpeed where
  status : UInt64
  speed : UInt64
  deriving Inhabited

/-- One scan iteration with an explicit checked-side call boundary. -/
def scanAt (input : Array UInt64) (index : Nat) (speed : UInt64) : CheckedSpeed :=
  let offset := 3 * index
  let state := sideCheckedBits (input.getD offset 0)
    (input.getD (offset + 1) 0) (input.getD (offset + 2) 0)
  if state.status == 0 then
    ⟨0, if speed ≤ state.speed then state.speed else speed⟩
  else ⟨1, 0⟩

/-- Scan checked state speeds to choose the next dt/dx. The input is flat
conservative triples. Rejection returns status one and positive zero. -/
def maxSpeedCheckedBits (input : Array UInt64) : CheckedSpeed := Id.run do
  if input.size == 0 || input.size % 3 != 0 then return ⟨1, 0⟩
  let count := input.size / 3
  let mut index := 0
  let mut status : UInt64 := 0
  let mut speed : UInt64 := 0
  while index < count && status == 0 do
    let result := scanAt input index speed
    status := result.status
    speed := result.speed
    index := index + 1
  return ⟨status, speed⟩

/-- Store a checked cell or mark the output rejected. -/
def writeCell (output : Array UInt64) (index : Nat)
    (cell : LeanExe.Examples.EulerCellStep.CheckedCell) : Array UInt64 :=
  if cell.status == 0 then
    let destination := 1 + 6 * index
    let output := output.set! destination cell.density
    let output := output.set! (destination + 1) cell.momentum
    let output := output.set! (destination + 2) cell.energy
    let output := output.set! (destination + 3) cell.pressure
    let output := output.set! (destination + 4) cell.alpha
    output.set! (destination + 5) cell.courant
  else output.set! 0 1

/-- One array-loop body with an explicit checked-cell call boundary. -/
def advanceAt (ratio : UInt64) (input output : Array UInt64) (index : Nat) : Array UInt64 :=
  let offset := 3 * index
  let previous := if index == 0 then offset else offset - 3
  let next := if index + 1 < input.size / 3 then offset + 3 else offset
  let cell := cellCheckedBits ratio
    (input.getD (previous) 0) (input.getD (previous + 1) 0) (input.getD (previous + 2) 0)
    (input.getD (offset) 0) (input.getD (offset + 1) 0) (input.getD (offset + 2) 0)
    (input.getD (next) 0) (input.getD (next + 1) 0) (input.getD (next + 2) 0)
  writeCell output index cell

/-- Read an immutable grid of conservative triples and fill a separate result
buffer. Boundaries copy the end state (transmissive). Result word zero is
status; each accepted cell contributes density, momentum, energy, pressure,
signal speed and rounded Courant number. Rejected payload is not a grid. -/
def stepCheckedBits (ratio : UInt64) (input : Array UInt64) : Array UInt64 :=
  if !positiveBits ratio || input.size == 0 || input.size % 3 != 0 then #[1]
  else Id.run do
    let count := input.size / 3
    let mut output := Array.replicate (1 + 6 * count) (0 : UInt64)
    let mut index := 0
    while index < count && output[0]! == 0 do
      output := advanceAt ratio input output index
      index := index + 1
    return output

end LeanExe.Examples.EulerGridStep
