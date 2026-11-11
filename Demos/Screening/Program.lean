import Demos.Screening.Spec
import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-!
The screening program.  `screenWith` reads an array of 25 binary64 values, applies the
apogee–perigee filter (`apsidesExclude`) and the orbit-path filter (`pathFilter`), and when
neither excludes the pair, isolates the close approaches of the window by bisection
(`isolate`, `finalSpans`, and `merge`).  `requirements.md` states the interface, and
`Soundness.lean` proves what each status and verdict implies.
-/

namespace Demos.Screening

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- The intervals of an object's quantities: its elements `a`, `e`, `M₀`, and `τ`, and the
components of `Spec.orbit`. -/
structure Obj where
  a : Interval
  e : Interval
  beta : Interval
  px : Interval
  py : Interval
  pz : Interval
  qx : Interval
  qy : Interval
  qz : Interval
  n : Interval
  m0 : Interval
  epoch : Interval
  speed : Interval
  perigee : Interval
  apogee : Interval
  deriving Inhabited

/-- An interval of time in minutes. -/
structure Span where
  lo : Float
  hi : Float
  deriving Inhabited

/-- A rectangle of eccentric anomalies, the first object's from `lo1` to `hi1` and the second's
from `lo2` to `hi2`. -/
structure Cell where
  lo1 : Float
  hi1 : Float
  lo2 : Float
  hi2 : Float
  deriving Inhabited

/-- An interval of time that the isolation keeps, with 1 in `certain` when it holds a close
approach. -/
structure Found where
  lo : Float
  hi : Float
  certain : UInt64
  deriving Inhabited

/-- The state of the isolation: the cells, the status, 0 while it refines and 3 once it stops at
the cap, the number of cell tests, and the number of levels completed. -/
structure Search where
  cells : Array Span
  status : UInt64
  tests : UInt64
  levels : UInt64
  deriving Inhabited

/-- The state of the orbit-path filter: the cells, the verdict, 0 while it refines, and the
number of cell tests. -/
structure PathSearch where
  cells : Array Cell
  verdict : UInt64
  tests : UInt64
  deriving Inhabited

/-- The state of the merge: the intervals written, and the interval `cur` being extended when
`has`. -/
structure Merge where
  out : Array Found
  cur : Found
  has : Bool
  deriving Inhabited

/-! ### Objects and positions -/

def rd (xs : Array Float) (i : UInt64) : Float := xs[i.toNat]!

/-- The intervals of an object for the gravitational parameter `mu`. -/
def object (inv half : Array UInt64) (mu a e incl node argp m0 epoch : Float) : Obj :=
  let c := Spec.orbitI inv half inv inv (point mu) (point a) (point e) (point incl) (point node)
    (point argp)
  { a := point a, e := point e, beta := c.2.1, px := c.2.2.1, py := c.2.2.2.1,
    pz := c.2.2.2.2.1, qx := c.2.2.2.2.2.1, qy := c.2.2.2.2.2.2.1, qz := c.2.2.2.2.2.2.2.1,
    n := c.1, m0 := point m0, epoch := point epoch, speed := c.2.2.2.2.2.2.2.2.1,
    perigee := c.2.2.2.2.2.2.2.2.2.1, apogee := c.2.2.2.2.2.2.2.2.2.2 }

/-- The point of the object's path at the eccentric anomalies of `E`. -/
def pointAt (inv half : Array UInt64) (o : Obj) (E : Interval) : Interval × Interval × Interval :=
  Spec.pathPointI inv half inv inv o.a o.e o.beta o.px o.py o.pz o.qx o.qy o.qz E

/-- The object's position at `t` minutes. -/
def positionAt (inv half : Array UInt64) (o : Obj) (t : Float) : Interval × Interval × Interval :=
  pointAt inv half o (Spec.anomalyI inv half inv inv o.e o.n o.m0 o.epoch (point t))

/-- The squared distance of two points. -/
def gapSq (inv half : Array UInt64) (p q : Interval × Interval × Interval) : Interval :=
  Spec.distSqI inv half inv inv p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2

/-- The computed middle of `[lo, hi]`. -/
def middle (lo hi : Float) : Float := lo + (hi - lo) * 0.5

/-! ### The apogee–perigee filter -/

/-- One object's perigee radius exceeds the other's apogee radius by more than the threshold
`thr`. -/
def apsidesExclude (o1 o2 : Obj) (thr : Interval) : Bool :=
  let g1 := sub o2.perigee o1.apogee
  let g2 := sub o1.perigee o2.apogee
  thr.status == 0 && ((g1.status == 0 && thr.hi < g1.lo) || (g2.status == 0 && thr.hi < g2.lo))

/-! ### The orbit-path filter -/

/-- Every pair of path points of the cell lies farther apart than the threshold whose square
`thr2` encloses. -/
def cellExclude (inv half : Array UInt64) (o1 o2 : Obj) (thr2 : Interval) (c : Cell) : Bool :=
  let s := gapSq inv half (pointAt inv half o1 (make c.lo1 c.hi1))
    (pointAt inv half o2 (make c.lo2 c.hi2))
  s.status == 0 && thr2.status == 0 && thr2.hi < s.lo

/-- The two path points at the cell's computed center lie within the threshold. -/
def cellClose (inv half : Array UInt64) (o1 o2 : Obj) (thr2 : Interval) (c : Cell) : Bool :=
  let s := gapSq inv half (pointAt inv half o1 (point (middle c.lo1 c.hi1)))
    (pointAt inv half o2 (point (middle c.lo2 c.hi2)))
  s.status == 0 && thr2.status == 0 && s.hi ≤ thr2.lo

/-- Some cell's center is close. -/
def anyClose (inv half : Array UInt64) (o1 o2 : Obj) (thr2 : Interval) (cells : Array Cell) :
    Bool :=
  LeanExe.loop cells.size.toUInt64 false fun i found =>
    if found then true else cellClose inv half o1 o2 thr2 cells[i.toNat]!

/-- The cells that `cellExclude` keeps, each split at its computed center into four. -/
def refineCells (inv half : Array UInt64) (o1 o2 : Obj) (thr2 : Interval) (cells : Array Cell) :
    Array Cell :=
  LeanExe.loop cells.size.toUInt64 #[] fun i acc =>
    let c := cells[i.toNat]!
    if cellExclude inv half o1 o2 thr2 c then acc
    else
      let m1 := middle c.lo1 c.hi1
      let m2 := middle c.lo2 c.hi2
      if finite m1 && finite m2 then
        (((acc.push ⟨c.lo1, m1, c.lo2, m2⟩).push ⟨c.lo1, m1, m2, c.hi2⟩).push
          ⟨m1, c.hi1, c.lo2, m2⟩).push ⟨m1, c.hi1, m2, c.hi2⟩
      else acc.push c

/-- One level of the orbit-path filter. -/
def pathLevel (inv half : Array UInt64) (o1 o2 : Obj) (thr2 : Interval) (cap : UInt64)
    (s : PathSearch) : PathSearch :=
  if s.verdict == 0 then
    if anyClose inv half o1 o2 thr2 s.cells then
      ⟨s.cells, 2, s.tests + s.cells.size.toUInt64⟩
    else
      let next := refineCells inv half o1 o2 thr2 s.cells
      let tests := s.tests + 2 * s.cells.size.toUInt64
      if next.size.toUInt64 == 0 then ⟨next, 1, tests⟩
      else if next.size.toUInt64 ≤ cap then ⟨next, 0, tests⟩
      else ⟨s.cells, 4, tests⟩
  else s

/-- The orbit-path filter from the cell `[0, 6.5] × [0, 6.5]`, with at most `levels` levels and
`cap` cells. -/
def pathFilter (inv half : Array UInt64) (o1 o2 : Obj) (thr2 : Interval) (levels cap : UInt64) :
    PathSearch :=
  let s := LeanExe.loop levels ⟨(#[] : Array Cell).push ⟨0.0, 6.5, 0.0, 6.5⟩, 0, 0⟩ fun _ s =>
    pathLevel inv half o1 o2 thr2 cap s
  if levels == 0 then s
  else if s.verdict == 0 then ⟨s.cells, 3, s.tests⟩ else s

/-! ### The isolation -/

/-- The test of a cell of time: 0 when no time of the cell is a close approach, 2 when its
computed middle is one, 3 when its computed middle is one and every time of the cell lies within
the threshold by the speed bound, and 1 otherwise.  `thr` encloses the threshold and `thr2` its
square. -/
def spanTest (inv half : Array UInt64) (o1 o2 : Obj) (thr thr2 : Interval) (s : Span) : UInt64 :=
  let m := middle s.lo s.hi
  let d2 := gapSq inv half (positionAt inv half o1 m) (positionAt inv half o2 m)
  let r := reach ⟨0, s.lo, s.hi⟩ m
  let moved := mul (add o1.speed o2.speed) (point r.value)
  let bound := add thr moved
  let b2 := mul bound bound
  let inner := sub thr moved
  let i2 := mul inner inner
  if d2.status == 0 && r.status == 0 && b2.status == 0 && 0 ≤ bound.lo && b2.hi < d2.lo then 0
  else if d2.status == 0 && thr2.status == 0 && finite m && s.lo ≤ m && m ≤ s.hi &&
      d2.hi ≤ thr2.lo then
    if r.status == 0 && i2.status == 0 && 0 ≤ inner.lo && d2.hi ≤ i2.lo then 3 else 2
  else 1

/-- The cells that `spanTest` keeps.  A cell is split at its computed middle when that lies
strictly inside it and the cell is not wholly within the threshold. -/
def refineSpans (inv half : Array UInt64) (o1 o2 : Obj) (thr thr2 : Interval)
    (cells : Array Span) : Array Span :=
  LeanExe.loop cells.size.toUInt64 #[] fun i acc =>
    let s := cells[i.toNat]!
    let r := spanTest inv half o1 o2 thr thr2 s
    if r == 0 then acc
    else
      let m := middle s.lo s.hi
      if r != 3 && finite m && s.lo < m && m < s.hi then (acc.push ⟨s.lo, m⟩).push ⟨m, s.hi⟩
      else acc.push s

/-- One level of the isolation: refine, or stop at the cap with the cells of the level. -/
def isolateLevel (inv half : Array UInt64) (o1 o2 : Obj) (thr thr2 : Interval) (cap : UInt64)
    (s : Search) : Search :=
  if s.status == 0 then
    let next := refineSpans inv half o1 o2 thr thr2 s.cells
    let tests := s.tests + s.cells.size.toUInt64
    if next.size.toUInt64 ≤ cap then ⟨next, 0, tests, s.levels + 1⟩
    else ⟨s.cells, 3, tests, s.levels⟩
  else s

/-- The isolation from the cell `[t0, t1]`, with `levels` levels and at most `cap` cells. -/
def isolate (inv half : Array UInt64) (o1 o2 : Obj) (thr thr2 : Interval) (t0 t1 : Float)
    (levels cap : UInt64) : Search :=
  LeanExe.loop levels ⟨(#[] : Array Span).push ⟨t0, t1⟩, 0, 0, 0⟩ fun _ s =>
    isolateLevel inv half o1 o2 thr thr2 cap s

/-- The cells that the final test keeps, with their certainty. -/
def finalSpans (inv half : Array UInt64) (o1 o2 : Obj) (thr thr2 : Interval)
    (cells : Array Span) : Array Found :=
  LeanExe.loop cells.size.toUInt64 #[] fun i acc =>
    let s := cells[i.toNat]!
    let r := spanTest inv half o1 o2 thr thr2 s
    if r == 0 then acc else acc.push ⟨s.lo, s.hi, if r == 1 then 0 else 1⟩

/-- One step of the merge. -/
def mergeStep (m : Merge) (x : Found) : Merge :=
  if m.has then
    if x.lo ≤ m.cur.hi then
      ⟨m.out, ⟨fmin m.cur.lo x.lo, fmax m.cur.hi x.hi,
        if x.certain == 1 then 1 else m.cur.certain⟩, true⟩
    else ⟨m.out.push m.cur, x, true⟩
  else ⟨m.out, x, true⟩

/-- The kept cells with consecutive cells that touch or overlap merged. -/
def merge (xs : Array Found) : Array Found :=
  let m := LeanExe.loop xs.size.toUInt64 ⟨#[], ⟨0.0, 0.0, 0⟩, false⟩ fun i m =>
    mergeStep m xs[i.toNat]!
  if m.has then m.out.push m.cur else m.out

/-- The intervals as triples `lo`, `hi`, and the certainty. -/
def triples (ys : Array Found) : Array Float :=
  LeanExe.build (3 * ys.size.toUInt64) fun i =>
    let y := ys[(i / 3).toNat]!
    if i % 3 == 0 then y.lo else if i % 3 == 1 then y.hi else y.certain.toFloat

/-! ### Input and output -/

/-- `x` is a whole number from `lo` to `hi`. -/
def isWhole (x : Float) (lo hi : UInt64) : Bool :=
  let n := x.toUInt64
  n.toFloat == x && lo ≤ n && n ≤ hi

/-- The elements from index `b` have `a > 0` and `0 ≤ e < 1`. -/
def orbitOk (xs : Array Float) (b : UInt64) : Bool :=
  0.0 < rd xs b && 0.0 ≤ rd xs (b + 1) && rd xs (b + 1) < 1.0

def allFinite (xs : Array Float) : Bool :=
  LeanExe.loop xs.size.toUInt64 true fun i ok => ok && finite (rd xs i)

/-- The input meets the requirements of `requirements.md`. -/
def valid (xs : Array Float) : Bool :=
  xs.size.toUInt64 == 25 && allFinite xs && rd xs 0 == 1.0 && orbitOk xs 1 && orbitOk xs 8 &&
    0.0 < rd xs 15 && -1.0e9 ≤ rd xs 16 && rd xs 16 ≤ rd xs 17 && rd xs 17 ≤ 1.0e9 &&
    0.0 ≤ rd xs 18 && 0.0 ≤ rd xs 19 &&
    (rd xs 20 == 0.0 || rd xs 20 == 1.0) && isWhole (rd xs 21) 0 40 &&
    isWhole (rd xs 22) 1 1048576 && isWhole (rd xs 23) 0 60 && isWhole (rd xs 24) 1 1048576

def objectAt (inv half : Array UInt64) (xs : Array Float) (b : UInt64) : Obj :=
  object inv half (rd xs 15) (rd xs b) (rd xs (b + 1)) (rd xs (b + 2)) (rd xs (b + 3))
    (rd xs (b + 4)) (rd xs (b + 5)) (rd xs (b + 6))

/-- The isolation's part of the output: the header and the merged intervals. -/
def isolationOutput (inv half : Array UInt64) (o1 o2 : Obj) (thr thr2 : Interval)
    (xs : Array Float) (p : PathSearch) : Array Float :=
  let s := isolate inv half o1 o2 thr thr2 (rd xs 16) (rd xs 17) (rd xs 23).toUInt64
    (rd xs 24).toUInt64
  let ivs := merge (finalSpans inv half o1 o2 thr thr2 s.cells)
  #[s.status.toFloat, ivs.size.toUInt64.toFloat, p.verdict.toFloat,
    (p.tests + s.tests + s.cells.size.toUInt64).toFloat, s.levels.toFloat] ++ triples ivs

/-- The screening of the pair that `xs` describes. -/
def screenWith (inv half : Array UInt64) (xs : Array Float) : Array Float :=
  if valid xs then
    let o1 := objectAt inv half xs 1
    let o2 := objectAt inv half xs 8
    let thr := add (point (rd xs 18)) (point (rd xs 19))
    let thr2 := mul thr thr
    if rd xs 20 == 1.0 && apsidesExclude o1 o2 thr then #[1.0, 0.0, 0.0, 0.0, 0.0]
    else
      let p := pathFilter inv half o1 o2 thr2 (rd xs 21).toUInt64 (rd xs 22).toUInt64
      if p.verdict == 1 then #[2.0, 0.0, 1.0, p.tests.toFloat, 0.0]
      else isolationOutput inv half o1 o2 thr thr2 xs p
  else #[4.0, 0.0, 0.0, 0.0, 0.0]

def screen (xs : Array Float) : Array Float := screenWith Trig.invPi Trig.halfPi xs

end Demos.Screening
