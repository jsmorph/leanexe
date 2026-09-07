import Project.EulerCellStep.Model

namespace Project.EulerGridStep.Model
open Project.EulerConservative.Model (positiveBits sideCheckedBits)

structure CheckedSpeed where
  status : UInt64
  speed : UInt64
  deriving DecidableEq, Inhabited, Repr

def scan (input : Array UInt64) (index : Nat) (speed : UInt64) : Nat → CheckedSpeed
  | 0 => ⟨0, speed⟩
  | fuel + 1 =>
    let offset := 3 * index
    let state := sideCheckedBits (input.getD (offset) 0) (input.getD (offset + 1) 0) (input.getD (offset + 2) 0)
    if state.status == 0 then
      scan input (index + 1) (if speed ≤ state.speed then state.speed else speed) fuel
    else ⟨1, 0⟩

def maxSpeedCheckedBits (input : Array UInt64) : CheckedSpeed :=
  if input.size == 0 || input.size % 3 != 0 then ⟨1, 0⟩
  else scan input 0 0 (input.size / 3)

def cellAt (ratio : UInt64) (input : Array UInt64) (index : Nat) : Project.EulerCellStep.Model.CheckedCell :=
  let offset := 3 * index
  let previous := if index == 0 then offset else offset - 3
  let next := if index + 1 < input.size / 3 then offset + 3 else offset
  Project.EulerCellStep.Model.cellCheckedBits ratio
    (input.getD (previous) 0) (input.getD (previous + 1) 0) (input.getD (previous + 2) 0)
    (input.getD (offset) 0) (input.getD (offset + 1) 0) (input.getD (offset + 2) 0)
    (input.getD (next) 0) (input.getD (next + 1) 0) (input.getD (next + 2) 0)

def payload (cell : Project.EulerCellStep.Model.CheckedCell) : List UInt64 :=
  [cell.density, cell.momentum, cell.energy, cell.pressure, cell.alpha, cell.courant]

def putCell (output : Array UInt64) (index : Nat) (cell : Project.EulerCellStep.Model.CheckedCell) : Array UInt64 :=
  let destination := 1 + 6 * index
  let output := output.set! destination cell.density
  let output := output.set! (destination + 1) cell.momentum
  let output := output.set! (destination + 2) cell.energy
  let output := output.set! (destination + 3) cell.pressure
  let output := output.set! (destination + 4) cell.alpha
  output.set! (destination + 5) cell.courant

def advanceAt (ratio : UInt64) (input output : Array UInt64) (index : Nat) : Array UInt64 :=
  let cell := cellAt ratio input index
  if cell.status == 0 then putCell output index cell else output.set! 0 1

/-- Fuel is the number of cells left, not a limit on WASM execution. -/
def fill (ratio : UInt64) (input : Array UInt64) (index : Nat) (output : Array UInt64) : Nat → Array UInt64
  | 0 => output
  | fuel + 1 =>
    if output[0]! == 0 then fill ratio input (index + 1) (advanceAt ratio input output index) fuel
    else output

def stepCheckedBits (ratio : UInt64) (input : Array UInt64) : Array UInt64 :=
  if !positiveBits ratio || input.size == 0 || input.size % 3 != 0 then #[1]
  else fill ratio input 0 (Array.replicate (1 + 6 * (input.size / 3)) 0) (input.size / 3)

end Project.EulerGridStep.Model
