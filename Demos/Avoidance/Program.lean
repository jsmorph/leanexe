import Demos.Avoidance.Spec
import Demos.Conjunction.Box
import Demos.Screening.Program
import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile

/-!
The authorizer.  `authorizeWith` reads an array of binary64 values: the gravitational parameter,
the primary's state at the burn, the box of velocity changes, the padding, the threshold, and a
block of 20 values for each conjunction, with the panel count `n` and the split budget `s`.  For
each conjunction, `searchOne` subdivides the box of velocity changes into cells.  `assessCell`
evaluates `afterI` with a cell and the padding as intervals, checks that both propagated states
are bound with `e² < 1` and that the plane's axes are defined, and encloses the probability with
`Demos.Conjunction.pcBoxWith`.  A cell whose interval lies below the threshold is done, a cell
whose interval lies at or above it, or whose center gives such an interval, shows the
probability at or above the threshold, and the search splits any other cell at the middle of its
longest side while splits remain.  While splits remain, it also probes the center of each
undecided cell whose depth is a multiple of 3.  The burn is accepted when every conjunction's hull of
intervals is accepted with an upper end below the threshold.  `requirements.md` states the
interface.
-/

namespace Demos.Avoidance

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

def rd (xs : Array Float) (i : UInt64) : Float := xs[i.toNat]!

/-- A cell of the search: a box of velocity changes, the interval of the evaluation of the cell
that it was split from, rejected for the first cell, and the number of splits that made it. -/
structure Cell where
  lx : Float
  hx : Float
  ly : Float
  hy : Float
  lz : Float
  hz : Float
  bound : Interval
  depth : UInt64
  deriving Inhabited

/-- The state of the search of one conjunction: the cells, the index of the next cell to
evaluate, the hull of the intervals of the cells evaluated and not split, whether the hull holds
one, the splits left, and whether an interval showed the probability at or above the
threshold. -/
structure Search where
  cells : Array Cell
  next : UInt64
  hull : Interval
  seen : Bool
  budget : UInt64
  above : Bool
  deriving Inhabited

/-- The result of the search of one conjunction: the hull of its intervals and whether an
interval showed the probability at or above the threshold. -/
structure Outcome where
  bound : Interval
  above : Bool
  deriving Inhabited

/-- The intervals of the encounter of conjunction `j` for every velocity change of the intervals
`dvx`, `dvy`, and `dvz` and every displacement whose components lie in `pad`: the miss vector and
the projected covariance, `α` and `e²` of the state after the burn and of the nominal state,
`|r₁ × ν|²`, and `|ν|²`.  The covariance is projected in the form centered at the middles of the
axes' intervals. -/
def afterAt (inv half : Array UInt64) (xs : Array Float) (j : UInt64) (dvx dvy dvz pad : Interval) :
    Interval × Interval × Interval × Interval × Interval × Interval × Interval × Interval ×
      Interval × Interval × Interval :=
  let b := 15 + 20 * j
  let mu := point (rd xs 0)
  let rbx := point (rd xs 1)
  let rby := point (rd xs 2)
  let rbz := point (rd xs 3)
  let vbx := point (rd xs 4)
  let vby := point (rd xs 5)
  let vbz := point (rd xs 6)
  let r1x := point (rd xs (b + 1))
  let r1y := point (rd xs (b + 2))
  let r1z := point (rd xs (b + 3))
  let rel := relativeI inv half inv inv mu rbx rby rbz vbx vby vbz dvx dvy dvz (point (rd xs b))
    r1x r1y r1z (point (rd xs (b + 4))) (point (rd xs (b + 5))) (point (rd xs (b + 6)))
    (point (rd xs (b + 7))) (point (rd xs (b + 8))) (point (rd xs (b + 9)))
    (point (rd xs (b + 10))) (point (rd xs (b + 11))) (point (rd xs (b + 12))) pad pad pad
  let s1 := shapeI inv half inv inv mu rbx rby rbz (add vbx dvx) (add vby dvy) (add vbz dvz)
  let s0 := shapeI inv half inv inv mu rbx rby rbz vbx vby vbz
  let ax := axesI inv half inv inv rel.2.2.2.1 rel.2.2.2.2.1 rel.2.2.2.2.2 r1x r1y r1z
  let pr := projectI inv half inv inv rel.1 rel.2.1 rel.2.2.1 ax.1 ax.2.1 ax.2.2.1 ax.2.2.2.1
    ax.2.2.2.2.1 ax.2.2.2.2.2.1 (point (mid ax.1)) (point (mid ax.2.1)) (point (mid ax.2.2.1))
    (point (mid ax.2.2.2.1)) (point (mid ax.2.2.2.2.1)) (point (mid ax.2.2.2.2.2.1))
    (point (rd xs (b + 13))) (point (rd xs (b + 14))) (point (rd xs (b + 15)))
    (point (rd xs (b + 16))) (point (rd xs (b + 17))) (point (rd xs (b + 18)))
  (pr.1, pr.2.1, pr.2.2.1, pr.2.2.2.1, pr.2.2.2.2, s1.1, s1.2, s0.1, s0.2, ax.2.2.2.2.2.2.1,
    ax.2.2.2.2.2.2.2)

/-- The interval of the probability of conjunction `j` for every velocity change of the intervals
`dvx`, `dvy`, and `dvz` and every displacement whose components lie in `pad`, or a rejected
interval. -/
def assessCell (tab inv half : Array UInt64) (xs : Array Float) (n j : UInt64)
    (dvx dvy dvz pad : Interval) : Interval :=
  let a := afterAt inv half xs j dvx dvy dvz pad
  let a1 := a.2.2.2.2.2.1
  let e1 := a.2.2.2.2.2.2.1
  let a0 := a.2.2.2.2.2.2.2.1
  let e0 := a.2.2.2.2.2.2.2.2.1
  let xn2 := a.2.2.2.2.2.2.2.2.2.1
  let zn2 := a.2.2.2.2.2.2.2.2.2.2
  if a1.status == 0 && 0 < a1.lo && e1.status == 0 && e1.hi < 1.0 && a0.status == 0 &&
      0 < a0.lo && e0.status == 0 && e0.hi < 1.0 && xn2.status == 0 && 0 < xn2.lo &&
      zn2.status == 0 && 0 < zn2.lo then
    Demos.Conjunction.pcBoxWith tab a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1
      (rd xs (15 + 20 * j + 19)) n
  else rejected

/-! ### Cells -/

/-- The interval of conjunction `j` for every velocity change of the cell and every displacement
within the padding. -/
def evalCell (tab inv half : Array UInt64) (xs : Array Float) (n j : UInt64) (c : Cell) :
    Interval :=
  assessCell tab inv half xs n j (make c.lx c.hx) (make c.ly c.hy) (make c.lz c.hz)
    (make (-rd xs 13) (rd xs 13))

/-- `m` is finite and lies between `lo` and `hi`. -/
def inside (lo hi m : Float) : Bool := finite m && lo ≤ m && m ≤ hi

/-- The interval of conjunction `j` at the center of the cell with no displacement, when the
middle of each side is finite and lies on the side, and a rejected interval otherwise. -/
def probe (tab inv half : Array UInt64) (xs : Array Float) (n j : UInt64) (c : Cell) : Interval :=
  let mx := Demos.Screening.middle c.lx c.hx
  let my := Demos.Screening.middle c.ly c.hy
  let mz := Demos.Screening.middle c.lz c.hz
  if inside c.lx c.hx mx && inside c.ly c.hy my && inside c.lz c.hz mz then
    assessCell tab inv half xs n j (point mx) (point my) (point mz) (point 0.0)
  else rejected

/-- The longest side of the cell: 0, 1, or 2 for the components x, y, and z. -/
def side (c : Cell) : UInt64 :=
  let a := c.hx - c.lx
  let b := c.hy - c.ly
  let d := c.hz - c.lz
  if b ≤ a && d ≤ a then 0 else if d ≤ b then 1 else 2

def sideLo (c : Cell) (k : UInt64) : Float := if k == 0 then c.lx else if k == 1 then c.ly else c.lz

def sideHi (c : Cell) (k : UInt64) : Float := if k == 0 then c.hx else if k == 1 then c.hy else c.hz

/-- The half of the cell below `m` on side `k`, with the interval `r`. -/
def lowerHalf (c : Cell) (k : UInt64) (m : Float) (r : Interval) : Cell :=
  if k == 0 then { c with hx := m, bound := r, depth := c.depth + 1 }
  else if k == 1 then { c with hy := m, bound := r, depth := c.depth + 1 }
  else { c with hz := m, bound := r, depth := c.depth + 1 }

/-- The half of the cell above `m` on side `k`, with the interval `r`. -/
def upperHalf (c : Cell) (k : UInt64) (m : Float) (r : Interval) : Cell :=
  if k == 0 then { c with lx := m, bound := r, depth := c.depth + 1 }
  else if k == 1 then { c with ly := m, bound := r, depth := c.depth + 1 }
  else { c with lz := m, bound := r, depth := c.depth + 1 }

/-- The middle of the cell's longest side is finite and lies strictly between the side's ends. -/
def splits (c : Cell) : Bool :=
  let k := side c
  let m := Demos.Screening.middle (sideLo c k) (sideHi c k)
  finite m && sideLo c k < m && m < sideHi c k

/-- The cell's depth is a multiple of 3, and the interval at its center is accepted with a lower
end at or above `t`. -/
def shown (tab inv half : Array UInt64) (xs : Array Float) (n j : UInt64) (t : Float) (c : Cell) :
    Bool :=
  if c.depth % 3 == 0 then
    let p := probe tab inv half xs n j c
    p.status == 0 && t ≤ p.lo
  else false

/-- What the search does with a cell whose interval is `r`: 1 when `r` is accepted with a lower
end at or above `t`, or when splits remain and `shown` holds, 2 when it splits the cell, and 0
when it adds `r` to the hull. -/
def action (tab inv half : Array UInt64) (xs : Array Float) (n j : UInt64) (t : Float) (c : Cell)
    (r : Interval) (budget : UInt64) : UInt64 :=
  if r.status == 0 && r.hi < t then 0
  else if r.status == 0 && t ≤ r.lo then 1
  else if budget != 0 then
    if shown tab inv half xs n j t c then 1 else if splits c then 2 else 0
  else 0

/-- The hull of `a` and `b`, or `b` when `a` holds no interval yet. -/
def hullOf (seen : Bool) (a b : Interval) : Interval :=
  if seen then
    if a.status == 0 && b.status == 0 then ⟨0, fmin a.lo b.lo, fmax a.hi b.hi⟩ else rejected
  else b

/-- The search over the box of velocity changes for conjunction `j` and the threshold `t`, with at
most `s` splits: it evaluates the cells in the order of their creation while cells remain and no
interval has shown the probability at or above `t`. -/
def search (tab inv half : Array UInt64) (xs : Array Float) (n j : UInt64) (t : Float)
    (s : UInt64) : Search :=
  LeanExe.repeatWhile (2 * s + 1)
    ⟨#[⟨rd xs 7, rd xs 8, rd xs 9, rd xs 10, rd xs 11, rd xs 12, rejected, 0⟩], 0, rejected,
      false, s, false⟩
    (fun q => q.next < q.cells.size.toUInt64 && !q.above)
    fun q =>
      let c := q.cells[q.next.toNat]!
      let r := evalCell tab inv half xs n j c
      let a := action tab inv half xs n j t c r q.budget
      if a == 2 then
        let k := side c
        let m := Demos.Screening.middle (sideLo c k) (sideHi c k)
        { q with cells := (q.cells.push (lowerHalf c k m r)).push (upperHalf c k m r),
                 next := q.next + 1, budget := q.budget - 1 }
      else
        { q with next := q.next + 1, hull := hullOf q.seen q.hull r, seen := true,
                 above := a == 1 }

/-- The hull of the search's intervals with the intervals of the cells left unevaluated. -/
def finish (q : Search) : Interval :=
  let h := LeanExe.loop (q.cells.size.toUInt64 - q.next) (q.hull, q.seen) fun i h =>
    (hullOf h.2 h.1 q.cells[(q.next + i).toNat]!.bound, true)
  if h.2 then h.1 else rejected

/-- The outcome of conjunction `j`. -/
def searchOne (tab inv half : Array UInt64) (xs : Array Float) (n s j : UInt64) : Outcome :=
  let q := search tab inv half xs n j (rd xs 14) s
  ⟨finish q, q.above⟩

/-! ### The input and the output -/

/-- The verdict of an outcome against the threshold `t`: 0 when its hull is accepted with an upper
end below `t`, 1 when it is accepted otherwise and an interval showed the probability at or above
`t`, 3 when it is accepted otherwise, and 2 when it is rejected. -/
def verdict (o : Outcome) (t : Float) : Float :=
  if o.bound.status == 0 then
    if o.bound.hi < t then 0.0 else if o.above then 1.0 else 3.0
  else 2.0

/-- Every hull is accepted with an upper end below `t`. -/
def allBelow (rs : Array Outcome) (t : Float) : Bool :=
  LeanExe.loop rs.size.toUInt64 true fun j ok =>
    ok && (rs[j.toNat]!.bound.status == 0 && rs[j.toNat]!.bound.hi < t)

/-- Some hull is rejected. -/
def anyRejected (rs : Array Outcome) : Bool :=
  LeanExe.loop rs.size.toUInt64 false fun j found => found || rs[j.toNat]!.bound.status != 0

/-- Some outcome has verdict 1. -/
def anyShown (rs : Array Outcome) (t : Float) : Bool :=
  LeanExe.loop rs.size.toUInt64 false fun j found =>
    found || (rs[j.toNat]!.bound.status == 0 && !(rs[j.toNat]!.bound.hi < t) &&
      rs[j.toNat]!.above)

def allFinite (xs : Array Float) : Bool :=
  LeanExe.loop xs.size.toUInt64 true fun i ok => ok && finite (rd xs i)

/-- Each of the `k` conjunctions has `Δt > 0` and `R > 0`. -/
def blocksOk (xs : Array Float) (k : UInt64) : Bool :=
  LeanExe.loop k true fun j ok =>
    ok && 0.0 < rd xs (15 + 20 * j) && 0.0 < rd xs (34 + 20 * j)

/-- The number of conjunctions of an array of the required size. -/
def count (xs : Array Float) : UInt64 := (xs.size.toUInt64 - 15) / 20

/-- The input meets the requirements of `requirements.md`. -/
def valid (xs : Array Float) (n s : UInt64) : Bool :=
  35 ≤ xs.size.toUInt64 && xs.size.toUInt64 ≤ 1295 && (xs.size.toUInt64 - 15) % 20 == 0 &&
    allFinite xs && 0.0 < rd xs 0 && rd xs 7 ≤ rd xs 8 && rd xs 9 ≤ rd xs 10 &&
    rd xs 11 ≤ rd xs 12 && 0.0 ≤ rd xs 13 && 1 ≤ n && n ≤ 1048576 && s ≤ 65536 &&
    blocksOk xs (count xs)

/-- The verdicts and intervals as triples. -/
def triples (rs : Array Outcome) (t : Float) : Array Float :=
  LeanExe.build (3 * rs.size.toUInt64) fun i =>
    let r := rs[(i / 3).toNat]!
    if i % 3 == 0 then verdict r t
    else if r.bound.status == 0 then (if i % 3 == 1 then r.bound.lo else r.bound.hi)
    else 0.0

def authorizeWith (tab inv half : Array UInt64) (xs : Array Float) (n s : UInt64) : Array Float :=
  if valid xs n s then
    let k := count xs
    let rs := LeanExe.build k fun j => searchOne tab inv half xs n s j
    let t := rd xs 14
    let status := if allBelow rs t then 0.0 else if anyRejected rs then 3.0
      else if anyShown rs t then 2.0 else 4.0
    #[status, k.toFloat] ++ triples rs t
  else #[1.0, 0.0]

def authorize (xs : Array Float) (n s : UInt64) : Array Float :=
  authorizeWith Exp.expTable Trig.invPi Trig.halfPi xs n s

end Demos.Avoidance
