import Demos.Events.Spec
import Demos.Screening.Program

/-!
The event-window program.  `eventsWith` reads an array of 21 binary64 values, sets up the
intervals of the orbit and the event (`setup`), isolates the times of the window at which the
event's condition may hold by bisection (`isolate` and `finalRuns`), and joins the kept cells
into runs (`joinRuns`).  `requirements.md` states the interface, and `Soundness.lean` proves
what the runs imply.  The cells, the runs, and the state of the search reuse the screening
program's `Span`, `Found`, `Search`, and `Merge`.
-/

namespace Demos.Events

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open Demos.Screening

/-- The intervals of an event: its code, the orbit, the day of minute 0, the cosine and sine of
its angle, the Earth's radius, the vector `b` and its length, the two rate bounds, and the two
margins. -/
structure Ev where
  code : UInt64
  o : Obj
  d0 : Interval
  ca : Interval
  sa : Interval
  radius : Interval
  b1 : Interval
  b2 : Interval
  b3 : Interval
  nb : Interval
  l1 : Interval
  l2 : Interval
  w1 : Interval
  w2 : Interval
  deriving Inhabited

/-- The event's two functions at `m` minutes. -/
def partsAt (inv half : Array UInt64) (ev : Ev) (m : Float) : Interval × Interval :=
  let s := Spec.sunDirI inv half inv inv ev.d0 (point m)
  if ev.code == 1 then
    let r := positionAt inv half ev.o m
    Spec.shadowPartsI inv half inv inv r.1 r.2.1 r.2.2 s.1 s.2.1 s.2.2 ev.ca ev.sa ev.radius
  else if ev.code == 2 then
    let g := Spec.vectorPartI inv half inv inv ev.nb ev.ca ev.b1 ev.b2 ev.b3 s.1 s.2.1 s.2.2
    (g, g)
  else
    let r := positionAt inv half ev.o m
    let v := Spec.rswVecI inv half inv inv r.1 r.2.1 r.2.2 ev.o.px ev.o.py ev.o.pz ev.o.qx ev.o.qy
      ev.o.qz ev.b1 ev.b2 ev.b3
    let g := Spec.vectorPartI inv half inv inv ev.nb ev.ca v.1 v.2.1 v.2.2 s.1 s.2.1 s.2.2
    (g, g)

/-- The test of a cell of time: 0 when the condition fails at every time of the cell, 2 when it
holds at every time of the cell, and 1 otherwise. -/
def cellTest (inv half : Array UInt64) (ev : Ev) (s : Span) : UInt64 :=
  let m := middle s.lo s.hi
  let p := partsAt inv half ev m
  let r := reach ⟨0, s.lo, s.hi⟩ m
  let e1 := add (mul ev.l1 (point r.value)) ev.w1
  let e2 := add (mul ev.l2 (point r.value)) ev.w2
  let u1 := add p.1 e1
  let u2 := add p.2 e2
  if r.status == 0 && ((p.1.status == 0 && e1.status == 0 && e1.hi < p.1.lo) ||
      (p.2.status == 0 && e2.status == 0 && e2.hi < p.2.lo)) then 0
  else if r.status == 0 && u1.status == 0 && u2.status == 0 && u1.hi ≤ 0.0 && u2.hi ≤ 0.0 then 2
  else 1

/-- The cells that `cellTest` keeps.  A cell is split at its computed middle when its test gives
1 and the middle lies strictly inside it. -/
def refineCells (inv half : Array UInt64) (ev : Ev) (cells : Array Span) : Array Span :=
  LeanExe.loop cells.size.toUInt64 #[] fun i acc =>
    let s := cells[i.toNat]!
    let r := cellTest inv half ev s
    if r == 0 then acc
    else
      let m := middle s.lo s.hi
      if r == 1 && finite m && s.lo < m && m < s.hi then (acc.push ⟨s.lo, m⟩).push ⟨m, s.hi⟩
      else acc.push s

/-- One level of the isolation: refine, or stop at the cap with the cells of the level. -/
def isolateLevel (inv half : Array UInt64) (ev : Ev) (cap : UInt64) (s : Search) : Search :=
  if s.status == 0 then
    let next := refineCells inv half ev s.cells
    let tests := s.tests + s.cells.size.toUInt64
    if next.size.toUInt64 ≤ cap then ⟨next, 0, tests, s.levels + 1⟩
    else ⟨s.cells, 1, tests, s.levels⟩
  else s

/-- The isolation from the cell `[t0, t1]`, with `levels` levels and at most `cap` cells. -/
def isolate (inv half : Array UInt64) (ev : Ev) (t0 t1 : Float) (levels cap : UInt64) : Search :=
  LeanExe.loop levels ⟨(#[] : Array Span).push ⟨t0, t1⟩, 0, 0, 0⟩ fun _ s =>
    isolateLevel inv half ev cap s

/-- The cells that the final test keeps, labeled 1 when the condition holds at every time of
them. -/
def finalRuns (inv half : Array UInt64) (ev : Ev) (cells : Array Span) : Array Found :=
  LeanExe.loop cells.size.toUInt64 #[] fun i acc =>
    let s := cells[i.toNat]!
    let r := cellTest inv half ev s
    if r == 0 then acc else acc.push ⟨s.lo, s.hi, if r == 2 then 1 else 0⟩

/-- One step of the join: a cell whose label agrees with the current run's and whose start lies
between the run's ends extends the run. -/
def joinStep (m : Merge) (x : Found) : Merge :=
  if m.has && x.certain == m.cur.certain && m.cur.lo ≤ x.lo && x.lo ≤ m.cur.hi then
    ⟨m.out, ⟨m.cur.lo, fmax m.cur.hi x.hi, m.cur.certain⟩, true⟩
  else if m.has then ⟨m.out.push m.cur, x, true⟩
  else ⟨m.out, x, true⟩

/-- The runs of the kept cells. -/
def joinRuns (xs : Array Found) : Array Found :=
  let m := LeanExe.loop xs.size.toUInt64 ⟨#[], ⟨0.0, 0.0, 0⟩, false⟩ fun i m =>
    joinStep m xs[i.toNat]!
  if m.has then m.out.push m.cur else m.out

/-! ### Input and output -/

/-- The entries of the event meet their requirements. -/
def eventOk (xs : Array Float) : Bool :=
  if rd xs 12 == 1.0 then
    -90.0 < rd xs 13 && rd xs 13 < 90.0 && 0.0 < rd xs 14 && 0.0 ≤ rd xs 15
  else if rd xs 12 == 2.0 || rd xs 12 == 3.0 then
    0.0 ≤ rd xs 13 && rd xs 13 ≤ 180.0 && (rd xs 16 != 0.0 || rd xs 17 != 0.0 || rd xs 18 != 0.0)
  else false

/-- The input meets the requirements of `requirements.md`. -/
def valid (xs : Array Float) : Bool :=
  xs.size.toUInt64 == 21 && allFinite xs && rd xs 0 == 1.0 && 0.0 < rd xs 1 &&
    0.0 ≤ rd xs 2 && rd xs 2 < 1.0 && 0.0 < rd xs 8 && -1.0e6 ≤ rd xs 9 && rd xs 9 ≤ 1.0e6 &&
    -1.0e9 ≤ rd xs 10 && rd xs 10 ≤ rd xs 11 && rd xs 11 ≤ 1.0e9 && eventOk xs &&
    isWhole (rd xs 19) 0 60 && isWhole (rd xs 20) 1 1048576

/-- The intervals of the event that `xs` describes. -/
def setup (inv half : Array UInt64) (xs : Array Float) : Ev :=
  let o := object inv half (rd xs 8) (rd xs 1) (rd xs 2) (rd xs 3) (rd xs 4) (rd xs 5) (rd xs 6)
    (rd xs 7)
  let code : UInt64 := if rd xs 12 == 1.0 then 1 else if rd xs 12 == 2.0 then 2 else 3
  let c := Spec.angleI inv half inv inv (point (rd xs 13))
  let b1 := point (rd xs 16)
  let b2 := point (rd xs 17)
  let b3 := point (rd xs 18)
  let nb := Spec.lengthI inv half inv inv b1 b2 b3
  let k := Spec.ratesI inv half inv inv o.speed o.apogee o.perigee c.1 c.2 nb b1 b2
  let l1 := if code == 1 then k.1 else if code == 2 then k.2.2.1 else k.2.2.2
  let p := point (rd xs 15)
  { code := code, o := o, d0 := point (rd xs 9), ca := c.1, sa := c.2,
    radius := point (rd xs 14), b1 := b1, b2 := b2, b3 := b3, nb := nb, l1 := l1,
    l2 := if code == 1 then k.2.1 else l1,
    w1 := if code == 1 then p else point 0.0,
    w2 := if code == 1 then Spec.padI inv half inv inv c.1 c.2 p else point 0.0 }

/-- The output of a search and its runs: the status, the number of runs, the number of cell
tests, the number of levels completed, and the runs. -/
def outputOf (s : Search) (rs : Array Found) : Array Float :=
  #[s.status.toFloat, rs.size.toUInt64.toFloat, (s.tests + s.cells.size.toUInt64).toFloat,
    s.levels.toFloat] ++ triples rs

/-- The event windows of the orbit and the event that `xs` describes. -/
def eventsWith (inv half : Array UInt64) (xs : Array Float) : Array Float :=
  if valid xs then
    let ev := setup inv half xs
    let s := isolate inv half ev (rd xs 10) (rd xs 11) (rd xs 19).toUInt64 (rd xs 20).toUInt64
    outputOf s (joinRuns (finalRuns inv half ev s.cells))
  else #[2.0, 0.0, 0.0, 0.0]

def events (xs : Array Float) : Array Float := eventsWith Trig.invPi Trig.halfPi xs

end Demos.Events
