import LeanExe.Build
import LeanExe.Loop

/-!
Arrays of records.  An array of a structure, sum, or enumeration is stored as its elements'
components in order, one word each, so element `i` of an array of records of `k` components
occupies words `i · k` to `i · k + k - 1`.  Reading an element out of bounds gives the record of
the fields' defaults, as `xs[i]!` does in Lean.  `LeanExe.build` makes an array of records, and a
fold over one is a `LeanExe.loop` over its indices.
-/

namespace LeanExe.Examples.Grids

inductive Phase where
  | solid | liquid | gas
  deriving Inhabited

structure Conserved where
  density : Float
  mx : Float
  my : Float
  energy : Float
  deriving Inhabited

structure Cell where
  index : UInt64
  state : Conserved
  pressure : Float
  status : UInt64
  ok : Bool
  phase : Phase
  deriving Inhabited

structure Mass where
  value : Float
  deriving Inhabited

def density (grid : Array Cell) (i : UInt64) : Float := grid[i.toNat]!.state.density

def pressure (grid : Array Cell) (i : UInt64) : Float := grid[i.toNat]!.pressure

def indexAt (grid : Array Cell) (i : UInt64) : UInt64 := grid[i.toNat]!.index

def okAt (grid : Array Cell) (i : UInt64) : Bool := grid[i.toNat]!.ok

def count (grid : Array Cell) : UInt64 := grid.size.toUInt64

/-- The sum of two cells' energies. -/
def energySum (grid : Array Cell) (i j : UInt64) : Float :=
  grid[i.toNat]!.state.energy + grid[j.toNat]!.state.energy

def isGas (grid : Array Cell) (i : UInt64) : Bool :=
  match grid[i.toNat]!.phase with
  | .gas => true
  | _ => false

def flagAt (xs : Array Bool) (i : UInt64) : Bool := xs[i.toNat]!

def flagCount (xs : Array Bool) : UInt64 := xs.size.toUInt64

def massAt (xs : Array Mass) (i : UInt64) : Float := xs[i.toNat]!.value

/-- Each state with its density and energy scaled by `a`. -/
def scaled (xs : Array Conserved) (a : Float) : Array Conserved :=
  LeanExe.build xs.size.toUInt64 fun i =>
    let c := xs[i.toNat]!
    { c with density := a * c.density, energy := a * c.energy }

def ramp (n : UInt64) : Array Conserved :=
  LeanExe.build n fun i => ⟨i.toFloat, 0, 0, 1⟩

def flags (n : UInt64) : Array Bool := LeanExe.build n fun i => i % 3 == 1

/-- The total density. -/
def totalDensity (xs : Array Conserved) : Float :=
  LeanExe.loop xs.size.toUInt64 0 fun i acc => acc + xs[i.toNat]!.density

end LeanExe.Examples.Grids
