import Examples.Grids.Program
import TestSupport.Host

/-! The module cases of `grids`, one line per case in the format of
`tests/modules/run.sh`. -/

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

/-- The sizes of the grids of the cases, which the verified compiler's cases also use. -/
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

def gridsCases : IO Unit := do
  let b (x : Bool) : String := toString (if x then 1 else 0)
  for size in gridSizes do
    let (grid, flags, masses) := gridArgs size
    let arg := arrU (grid.toList.flatMap cellWords)
    let flagArg := arrU (flags.toList.map fun x => if x then 1 else 0)
    let massArg := arrU (masses.toList.map (·.value.toBits))
    line "grids" "count" "i64" [arg] (toString (count grid))
    line "grids" "flagCount" "i64" [flagArg] (toString (flagCount flags))
    for i in indexArgs size do
      line "grids" "density" "f64" [arg, u i] (toString (density grid i).toBits)
      line "grids" "pressure" "f64" [arg, u i] (toString (pressure grid i).toBits)
      line "grids" "indexAt" "i64" [arg, u i] (toString (indexAt grid i))
      line "grids" "okAt" "i64" [arg, u i] (b (okAt grid i))
      line "grids" "isGas" "i64" [arg, u i] (b (isGas grid i))
      line "grids" "flagAt" "i64" [flagArg, u i] (b (flagAt flags i))
      line "grids" "massAt" "f64" [massArg, u i] (toString (massAt masses i).toBits)
      for j in secondIndexArgs do
        line "grids" "energySum" "f64" [arg, u i, u j] (toString (energySum grid i j).toBits)
    let states : Array Conserved := grid.map (·.state)
    for a in scaleArgs do
      line "grids" "scaled" "array-u64" [arrU (states.toList.flatMap stateWords), fl a]
        (words ((scaled states a).toList.flatMap stateWords))
    line "grids" "totalDensity" "f64" [arrU (states.toList.flatMap stateWords)]
      (toString (totalDensity states).toBits)
    line "grids" "ramp" "array-u64" [u (UInt64.ofNat size)]
      (words ((ramp (UInt64.ofNat size)).toList.flatMap stateWords))
    line "grids" "flags" "array-u64" [u (UInt64.ofNat size)]
      (words ((Examples.Grids.flags (UInt64.ofNat size)).toList.map fun x => if x then 1 else 0))

def cases : IO Unit := do
  gridsCases

end Examples.Grids
