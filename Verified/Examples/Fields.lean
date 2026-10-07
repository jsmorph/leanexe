import Verified.Reflect.Command

/-! The twenty-second program of the verified compiler: records with array fields.  A structure
whose `Flat` tuple holds arrays is represented as that tuple, by `instRepresentOfFlat`, so its
arrays are passed and returned as a tuple's arrays are.  The programs build records, read their
fields and elements, also past the end, update a field with `{ r with … }` on a borrowed
parameter, which copies the array, and in a loop's state, which updates it in place, pass a record
to a call, take one apart with `match`, choose one with `if`, return one in a pair, and hold one
record in another. -/

namespace Verified.Examples.Fields

open LeanExe.Pipeline

structure Book where
  prices : Array UInt64
  sizes : Array UInt64
  fills : UInt64
  deriving Inhabited

instance : Flat Book (Array UInt64 × Array UInt64 × UInt64) :=
  ⟨fun b => (b.prices, b.sizes, b.fills)⟩

structure Cell where
  level : Float
  count : UInt64
  deriving Inhabited

instance : Flat Cell (Float × UInt64) := ⟨fun c => (c.level, c.count)⟩

structure Grid where
  cells : Array Cell
  time : Float
  steps : UInt64
  deriving Inhabited

instance : Flat Grid (Array Cell × Float × UInt64) := ⟨fun g => (g.cells, g.time, g.steps)⟩

structure World where
  grid : Grid
  label : UInt64
  deriving Inhabited

instance : Flat World (Grid × UInt64) := ⟨fun w => (w.grid, w.label)⟩

/-- A book of `n` orders. -/
def mkBook (n : UInt64) : Book :=
  ⟨LeanExe.build n fun i => i * 10 + 1, LeanExe.build n fun i => i + 2, 0⟩

/-- The sum of price times size over the orders, reading past the end of `sizes` when it is
shorter. -/
def bookTotal (b : Book) : UInt64 :=
  LeanExe.loop b.prices.size.toUInt64 0 fun i acc => acc + b.prices[i.toNat]! * b.sizes[i.toNat]!

/-- `b` with size `q` at order `i` and one more fill. -/
def fillOrder (b : Book) (i q : UInt64) : Book :=
  { b with sizes := b.sizes.set! i.toNat q, fills := b.fills + 1 }

/-- A call with a record argument. -/
def bookValue (b : Book) : UInt64 := bookTotal b + b.fills

def pickBook (c : Bool) (a b : Book) : Book := if c then a else b

def bookShape (b : Book) : UInt64 :=
  match b with
  | ⟨p, s, f⟩ => p.size.toUInt64 * 1000 + s.size.toUInt64 + f

def withTotal (b : Book) : Book × UInt64 := (b, bookTotal b)

/-- `k` steps of `dt` on `g`, each recording the time and step count in one cell, in place. -/
def advance (g : Grid) (k : UInt64) (dt : Float) : Grid :=
  LeanExe.loop k g fun _ s =>
    let slot := s.steps % s.cells.size.toUInt64
    { s with
      cells := s.cells.set! slot.toNat (Cell.mk s.time s.steps)
      time := s.time + dt
      steps := s.steps + 1 }

/-- The sum of the levels of the cells. -/
def gridLevel (g : Grid) : Float :=
  LeanExe.loop g.cells.size.toUInt64 g.time fun i acc => acc + g.cells[i.toNat]!.level

def gridCells (g : Grid) : Array Cell := g.cells

/-- A record that holds a record. -/
def worldLevel (w : World) : Float := gridLevel w.grid + w.label.toFloat

def relabel (w : World) (k : UInt64) : World := { w with label := w.label + k }

verified_compile compiled := [mkBook, bookTotal, fillOrder, bookValue, pickBook, bookShape,
  withTotal, advance, gridLevel, gridCells, worldLevel, relabel]

end Verified.Examples.Fields
