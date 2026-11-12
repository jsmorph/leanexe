import Demos.Avoidance.Spec
import Demos.Conjunction.Box
import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

/-!
The authorizer.  `authorizeWith` reads an array of binary64 values: the gravitational parameter,
the primary's state at the burn, the box of velocity changes, the padding, the threshold, and a
block of 20 values for each conjunction.  For each conjunction, `assessOne` evaluates `afterI`
with the box of velocity changes and the padding as intervals, checks that both propagated states
are bound with `e² < 1` and that the plane's axes are defined, and encloses the probability with
`Demos.Conjunction.pcBoxWith`.  The burn is accepted when every enclosure is accepted with an
upper end below the threshold.  `requirements.md` states the interface.
-/

namespace Demos.Avoidance

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

def rd (xs : Array Float) (i : UInt64) : Float := xs[i.toNat]!

/-- The intervals of the encounter of conjunction `j` for every velocity change of the box and
every displacement within the padding: the miss vector and the projected covariance, `α` and `e²`
of the state after the burn and of the nominal state, `|r₁ × ν|²`, and `|ν|²`.  The covariance is
projected in the form centered at the middles of the axes' intervals. -/
def afterAt (inv half : Array UInt64) (xs : Array Float) (j : UInt64) :
    Interval × Interval × Interval × Interval × Interval × Interval × Interval × Interval ×
      Interval × Interval × Interval :=
  let b := 15 + 20 * j
  let pad := make (-rd xs 13) (rd xs 13)
  let mu := point (rd xs 0)
  let rbx := point (rd xs 1)
  let rby := point (rd xs 2)
  let rbz := point (rd xs 3)
  let vbx := point (rd xs 4)
  let vby := point (rd xs 5)
  let vbz := point (rd xs 6)
  let dvx := make (rd xs 7) (rd xs 8)
  let dvy := make (rd xs 9) (rd xs 10)
  let dvz := make (rd xs 11) (rd xs 12)
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

/-- The interval of the probability of conjunction `j` for every velocity change of the box and
every displacement within the padding, or a rejected interval. -/
def assessOne (tab inv half : Array UInt64) (xs : Array Float) (n j : UInt64) : Interval :=
  let a := afterAt inv half xs j
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

/-- The verdict of an enclosure against the threshold `t`: 0 when it is accepted with an upper
end below `t`, 1 when it is accepted otherwise, and 2 when it is rejected. -/
def verdict (r : Interval) (t : Float) : Float :=
  if r.status == 0 then
    if r.hi < t then 0.0 else 1.0
  else 2.0

/-- Every enclosure is accepted with an upper end below `t`. -/
def allBelow (rs : Array Interval) (t : Float) : Bool :=
  LeanExe.loop rs.size.toUInt64 true fun j ok =>
    ok && (rs[j.toNat]!.status == 0 && rs[j.toNat]!.hi < t)

/-- Some enclosure is rejected. -/
def anyRejected (rs : Array Interval) : Bool :=
  LeanExe.loop rs.size.toUInt64 false fun j found => found || rs[j.toNat]!.status != 0

def allFinite (xs : Array Float) : Bool :=
  LeanExe.loop xs.size.toUInt64 true fun i ok => ok && finite (rd xs i)

/-- Each of the `k` conjunctions has `Δt > 0` and `R > 0`. -/
def blocksOk (xs : Array Float) (k : UInt64) : Bool :=
  LeanExe.loop k true fun j ok =>
    ok && 0.0 < rd xs (15 + 20 * j) && 0.0 < rd xs (34 + 20 * j)

/-- The number of conjunctions of an array of the required size. -/
def count (xs : Array Float) : UInt64 := (xs.size.toUInt64 - 15) / 20

/-- The input meets the requirements of `requirements.md`. -/
def valid (xs : Array Float) (n : UInt64) : Bool :=
  35 ≤ xs.size.toUInt64 && xs.size.toUInt64 ≤ 1295 && (xs.size.toUInt64 - 15) % 20 == 0 &&
    allFinite xs && 0.0 < rd xs 0 && rd xs 7 ≤ rd xs 8 && rd xs 9 ≤ rd xs 10 &&
    rd xs 11 ≤ rd xs 12 && 0.0 ≤ rd xs 13 && 1 ≤ n && n ≤ 1048576 && blocksOk xs (count xs)

/-- The verdicts and intervals as triples. -/
def triples (rs : Array Interval) (t : Float) : Array Float :=
  LeanExe.build (3 * rs.size.toUInt64) fun i =>
    let r := rs[(i / 3).toNat]!
    if i % 3 == 0 then verdict r t
    else if r.status == 0 then (if i % 3 == 1 then r.lo else r.hi)
    else 0.0

def authorizeWith (tab inv half : Array UInt64) (xs : Array Float) (n : UInt64) : Array Float :=
  if valid xs n then
    let k := count xs
    let rs := LeanExe.build k fun j => assessOne tab inv half xs n j
    let t := rd xs 14
    let status := if allBelow rs t then 0.0 else if anyRejected rs then 3.0 else 2.0
    #[status, k.toFloat] ++ triples rs t
  else #[1.0, 0.0]

def authorize (xs : Array Float) (n : UInt64) : Array Float :=
  authorizeWith Exp.expTable Trig.invPi Trig.halfPi xs n

end Demos.Avoidance
