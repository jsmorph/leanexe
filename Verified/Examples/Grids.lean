import Verified.Examples.Records

/-! The seventeenth program of the verified compiler: arrays of structures.  An array of
structures with `Flat` instances holds each element's flattening in consecutive words, as an array
of tuples does.  The programs build such arrays, read elements and their fields, update elements in
place, extend and join arrays, and return an array with a total.  The theorem for each definition
is stated for Lean's arrays of structures and the instances Lean synthesizes for them.  An array of
tuples has no `Represent` instance, so `pairTotal` holds one only inside its body. -/

namespace Verified.Examples.Grids

open Verified.Examples.Records

/-- A state per point, with density `i`, no momentum, and energy `2 i`. -/
def ramp (n : UInt64) : Array Conserved :=
  LeanExe.build n fun i => ⟨i.toFloat, 0.0, 2.0 * i.toFloat⟩

def density (grid : Array Cell) (i : UInt64) : Float := grid[i.toNat]!.state.density

def totalEnergy (us : Array Conserved) : Float :=
  LeanExe.loop us.size.toUInt64 0.0 fun i acc => acc + us[i.toNat]!.energy

/-- Each state with density and energy scaled by `a`, in place. -/
def scaled (a : Float) (us : Array Conserved) : Array Conserved :=
  LeanExe.loop us.size.toUInt64 us fun i acc =>
    let u := acc[i.toNat]!
    acc.set! i.toNat { u with density := a * u.density, energy := a * u.energy }

/-- A cell for each state, with pressure from its energy. -/
def cells (us : Array Conserved) : Array Cell :=
  LeanExe.build us.size.toUInt64 fun i =>
    let u := us[i.toNat]!
    ⟨i, u, 0.4 * u.energy, decide (0.0 ≤ u.energy)⟩

/-- Whether every cell is valid. -/
def allOk (grid : Array Cell) : Bool :=
  LeanExe.loop grid.size.toUInt64 true fun i acc => acc && grid[i.toNat]!.ok

/-- A cell with the next index, appended. -/
def addCell (grid : Array Cell) (u : Conserved) (p : Float) : Array Cell :=
  grid.push ⟨grid.size.toUInt64, u, p, decide (0.0 ≤ p)⟩

def joined (xs ys : Array Conserved) : Array Conserved := xs ++ ys

def count (grid : Array Cell) : UInt64 := grid.size.toUInt64

def withTotal (us : Array Conserved) : Array Conserved × Float :=
  let t := totalEnergy us
  (us, t)

/-- The sum of the second components of a local array of pairs. -/
def pairTotal (n : UInt64) : Float :=
  let ps : Array (UInt64 × Float) := LeanExe.build n fun i => (i, i.toFloat)
  LeanExe.loop ps.size.toUInt64 0.0 fun i acc => acc + ps[i.toNat]!.2

verified_compile compiled := [ramp, density, totalEnergy, scaled, cells, allOk, addCell, joined,
  count, withTotal, pairTotal]

end Verified.Examples.Grids
