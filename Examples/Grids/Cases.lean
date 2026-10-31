import Examples.Grids.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of `exampleGrids`. -/

namespace Examples.Grids

open TestSupport.Host

def phaseWord : Phase → UInt64
  | .solid => 0 | .liquid => 1 | .gas => 2

/-- A cell as the nine words of its fields. -/
def cellWords (c : Cell) : List UInt64 :=
  [c.index, c.state.density.toBits, c.state.mx.toBits, c.state.my.toBits, c.state.energy.toBits,
   c.pressure.toBits, c.status, if c.ok then 1 else 0, phaseWord c.phase]

/-- A state as the four words of its fields. -/
def stateWords (s : Conserved) : List UInt64 :=
  [s.density.toBits, s.mx.toBits, s.my.toBits, s.energy.toBits]

/-- Cell `i` of the grids of the cases. -/
def cell (i : Nat) : Cell :=
  let f (k : Nat) : Float := if (i + k) % 5 = 0 then specialFloats[(i + k) % specialFloats.length]!
    else small (7 * i + k)
  { index := rw i, state := ⟨f 1, f 2, f 3, f 4⟩, pressure := f 5, status := below 4 i,
    ok := i % 2 = 0, phase := match i % 3 with | 0 => .solid | 1 => .liquid | _ => .gas }

/-- The sizes of the grids of the cases. -/
def gridSizes : List Nat := [0, 1, 3, 7]

/-- The grid of `size` cells, its flags, and its masses. -/
def gridArgs (size : Nat) : Array Cell × Array Bool × Array Mass :=
  let grid : Array Cell := (List.range size).toArray.map cell
  (grid, (List.range size).toArray.map fun i => i % 3 == 1, grid.map fun c => ⟨c.pressure⟩)

/-- The positions of the cases on a grid of `size` cells: each position up to one past the end,
and positions whose word offsets do not fit in 32 or 64 bits. -/
def indexArgs (size : Nat) : List UInt64 :=
  (List.range (size + 1)).map UInt64.ofNat ++ [536870911, 536870912, 9223372036854775808, maxU]

/-- The second positions of the cases of `energySum`. -/
def secondIndexArgs : List UInt64 := [0, 2, maxU]

/-- The factors of the cases of `scaled`. -/
def scaleArgs : List Float := [1.5, -0.0, inf, 0.0 / 0.0]

end Examples.Grids
