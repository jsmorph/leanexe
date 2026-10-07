import Verified.Reflect.Command

/-! The sixteenth program of the verified compiler: records.  A structure with a `Flat` instance is
represented as the tuple of its fields, as `Implements` represents it, and a nested structure as
its own tuple.  The programs build structures, update them with `{ s with … }`, read fields and
fields of fields, take them apart with `match`, choose between them with `if`, pass them to calls,
and carry one as a loop's state.  The theorem for each definition is stated for Lean's structures
and the instances Lean synthesizes for them. -/

namespace Verified.Examples.Records

open LeanExe.Pipeline

structure Conserved where
  density : Float
  momentum : Float
  energy : Float

structure Cell where
  index : UInt64
  state : Conserved
  pressure : Float
  ok : Bool

instance : Flat Conserved (Float × Float × Float) := ⟨fun c => (c.density, c.momentum, c.energy)⟩

instance : Flat Cell (UInt64 × Conserved × Float × Bool) :=
  ⟨fun c => (c.index, c.state, c.pressure, c.ok)⟩

def kinetic (c : Conserved) : Float := c.momentum * c.momentum / (2 * c.density)

def scale (a : Float) (c : Conserved) : Conserved :=
  { c with density := a * c.density, energy := a * c.energy }

def add (x y : Conserved) : Conserved :=
  ⟨x.density + y.density, x.momentum + y.momentum, x.energy + y.energy⟩

def mkCell (i : UInt64) (c : Conserved) (p : Float) : Cell :=
  { index := i, state := c, pressure := p, ok := decide (0.0 ≤ p) }

def cellEnergy (c : Cell) : Float := c.state.energy + c.pressure

def bumpIndex (c : Cell) : Cell := { c with index := c.index + 1 }

def reversed (c : Conserved) : Conserved :=
  match c with
  | ⟨d, m, e⟩ => ⟨e, m, d⟩

/-- `c` added to itself `n` times, from `c`. -/
def repeated (n : UInt64) (c : Conserved) : Conserved :=
  LeanExe.loop n c fun _ acc => add acc c

def pick (b : Bool) (x y : Conserved) : Conserved := if b then x else y

def withCount (c : Cell) : Cell × UInt64 := (bumpIndex c, c.index * 2)

verified_compile compiled := [kinetic, scale, add, mkCell, cellEnergy, bumpIndex, reversed,
  repeated, pick, withCount]

end Verified.Examples.Records
