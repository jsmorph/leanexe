import Project.EulerRiemann.InitialModel
import Project.EulerRiemann.NumericsSweep
import LeanExe.Runtime

namespace Project.EulerRiemann.Traversal
open Project.Euler2DCellStep.Sweep

structure Cell where
  index : Nat
  state : State
  pressure : UInt64
  status : UInt64
  deriving Inhabited

def initialCell (n index : Nat) : Cell :=
  let x := min 5 (4 * n - 5 * (index % n))
  let y := min 5 (4 * n - 5 * (index / n))
  let q := Initial.weighted x y
  let out := Numerics.sideCheckedBits q.density q.mx q.my q.energy
  ⟨index, q, out.pressure, out.status⟩

def growCells : Nat → Nat → Nat → Array Cell → Array Cell
  | 0, _, size, values => values.extract 0 size
  | fuel + 1, n, size, values =>
    if size ≤ values.size then values.extract 0 size
    else
      let offset := values.size
      let upper := values.map (fun cell => initialCell n (cell.index + offset))
      growCells fuel n size (values ++ upper)

def initialCells (n : Nat) : Array Cell :=
  if 2 ≤ n ∧ n ≤ 800 then growCells 20 n (n * n) #[initialCell n 0] else #[]

def neighborIndex (n index : Nat) (axis forward : Bool) : Nat :=
  let stride := if axis then n else 1
  let coordinate := if axis then index / n else index % n
  if forward then
    if coordinate + 1 < n then index + stride else index
  else
    if coordinate = 0 then index else index - stride

def cellInputs (n : Nat) (axis : Bool) (grid : Array Cell) (cell : Cell) : Inputs :=
  let leftIndex := neighborIndex n cell.index axis false
  let leftState := grid[leftIndex]!.state
  let left := orient axis leftState
  let center := orient axis cell.state
  let rightIndex := neighborIndex n cell.index axis true
  let rightState := grid[rightIndex]!.state
  let right := orient axis rightState
  ⟨left, center, right⟩

def updateCell (n : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Array Cell) (cell : Cell) : Cell :=
  let input := cellInputs n axis grid cell
  let out := Numerics.evaluate ratio input
  let next := orient axis ⟨out.density, out.momentum, out.transverse, out.energy⟩
  ⟨cell.index, next, out.pressure, out.status⟩

def sweep (n : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell) : Array Cell :=
  grid.map (fun cell => updateCell n axis ratio grid cell)

def accepted (grid : Array Cell) : Bool :=
  grid.all (fun cell => cell.status == 0)

def step (n : Nat) (ratio : UInt64) (grid : Array Cell) : Array Cell :=
  let middle := sweep n false ratio grid
  if accepted middle then
    let next := sweep n true ratio middle
    let _ := LeanExe.Runtime.release middle
    next
  else middle

structure Scan where
  status : UInt64
  alpha : UInt64
  deriving Inhabited

def scanCell (acc : Scan) (cell : Cell) : Scan :=
  let q := cell.state
  let x := Numerics.sideCheckedBits q.density q.mx q.my q.energy
  let y := Numerics.sideCheckedBits q.density q.my q.mx q.energy
  ⟨acc.status ||| x.status ||| y.status, max acc.alpha (max x.speed y.speed)⟩

def scan (grid : Array Cell) : Scan := grid.foldl (fun acc cell => scanCell acc cell) ⟨0, 0⟩

end Project.EulerRiemann.Traversal
