import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile
import Library.Numerics.Float64.Atan.Program

/-! A slew planner for a spacecraft under pointing constraints, in the verified compiler's dialect.

A spacecraft attitude is a quaternion `[w, x, y, z]` that maps body coordinates to inertial
coordinates.  The planner finds a sequence of rest-to-rest eigenaxis rotations from a start
attitude to a goal attitude through a set of waypoint attitudes, such that every rotation keeps
each constrained body vector outside each keep-out cone and inside each keep-in cone.  It returns
the sequence of least total duration in whole milliseconds among the paths of its graph.

Input, one array of binary64 values:

* `0..7`: version (2), body count `nb` (1 to 8), cone count `nc` (0 to 16), waypoint count `nw`
  (0 to 1024), rate limit (rad/s), acceleration limit (rad/s²), settling time (s), and the
  largest rotation of an edge (rad);
* `8..15`: start and goal quaternions;
* `16..`: `nb` body vectors, three values each, in the body frame;
* then `nc` cones, six values each: body index, axis (three values, inertial), cosine of the
  half-angle, and kind (0 keep-out, 1 keep-in);
* then `nw` waypoint quaternions, four values each.

Output: a header of status, segment count `k`, total cost in milliseconds, and nodes finalized;
then `k` segments of eleven values each: start quaternion, rotation axis, rotation angle, cost in
milliseconds, and the indices of the nodes the segment joins; then the goal quaternion.  Status 1
is a plan, 0 no path, -1 a start attitude that violates a cone, -2 a goal attitude that violates
a cone, and -3 invalid input; only status 1 has segments and the goal.

Each check tightens its cone by `margin`, which covers the rounding error of the computation and
a tube of `1e-9` rad around the commanded path.  The rotation angle comes from the library's
`atan2` and affects only the cost and the edge-length test, never the check. -/

namespace Demos.Slew

open Library.Numerics.Float64.Atan

structure V3 where
  x : Float
  y : Float
  z : Float
  deriving Inhabited

structure Q4 where
  w : Float
  x : Float
  y : Float
  z : Float
  deriving Inhabited

/-- The dimensions of an input and the positions of its sections. -/
structure Dims where
  nb : UInt64
  nc : UInt64
  nw : UInt64
  coneOff : UInt64
  wayOff : UInt64
  total : UInt64
  deriving Inhabited

/-- The state of the search: the best known cost and parent of each node, which nodes are
finalized and which pass the static check, whether the search has stopped, and how many nodes
it has finalized. -/
structure Search where
  cost : Array UInt64
  parent : Array UInt64
  done : Array Bool
  ok : Array Bool
  finished : Bool
  examined : UInt64
  deriving Inhabited

/-- `1.1e-9`: the rounding allowance `1e-10` plus the tube radius `1e-9`. -/
abbrev margin : Float := Float.ofBits 0x3E12E5D9E5C45270
/-- `1e-12`: the error allowance of the stationary-point tests. -/
abbrev eta : Float := Float.ofBits 0x3D719799812DEA11
/-- `1e-7`: below this vector part, a rotation is checked by its start attitude. -/
abbrev sMin : Float := Float.ofBits 0x3E7AD7F29ABCAF48
/-- `1e-12`: the tolerance on squared norms of input vectors and quaternions. -/
abbrev tolNorm : Float := Float.ofBits 0x3D719799812DEA11
/-- `1e-5` rad/s and `1e-7` rad/s²: the least rate and acceleration limits. -/
abbrev rateMin : Float := Float.ofBits 0x3EE4F8B588E368F1
abbrev accelMin : Float := Float.ofBits 0x3E7AD7F29ABCAF48
/-- `1e-150`: below this vector part, the output axis is `+X`. -/
abbrev axisMin : Float := Float.ofBits 0x20CA2FE76A3F9475
/-- The largest finite binary64 value. -/
abbrev maxFinite : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF
/-- The cost of an unreached node, `2 ^ 62`. -/
abbrev infinity : UInt64 := 4611686018427387904

@[inline] def dot (a b : V3) : Float := a.x * b.x + a.y * b.y + a.z * b.z

@[inline] def cross (a b : V3) : V3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

/-- The rotation of `v` by `q`: `v + w t + q × t` with `t = 2 q × v`. -/
def qrot (q : Q4) (v : V3) : V3 :=
  let tx := 2.0 * (q.y * v.z - q.z * v.y)
  let ty := 2.0 * (q.z * v.x - q.x * v.z)
  let tz := 2.0 * (q.x * v.y - q.y * v.x)
  ⟨v.x + q.w * tx + (q.y * tz - q.z * ty),
    v.y + q.w * ty + (q.z * tx - q.x * tz),
    v.z + q.w * tz + (q.x * ty - q.y * tx)⟩

/-- The rotation from `qa` to `qb` in the inertial frame, `qb qa*`, with a non-negative scalar
part, which selects the rotation of angle at most `π`. -/
def relative (qa qb : Q4) : Q4 :=
  let w := qb.w * qa.w + qb.x * qa.x + qb.y * qa.y + qb.z * qa.z
  let x := qb.x * qa.w - qb.w * qa.x - qb.y * qa.z + qb.z * qa.y
  let y := qb.y * qa.w - qb.w * qa.y - qb.z * qa.x + qb.x * qa.z
  let z := qb.z * qa.w - qb.w * qa.z - qb.x * qa.y + qb.y * qa.x
  if w < 0.0 then ⟨-w, -x, -y, -z⟩ else ⟨w, x, y, z⟩

@[inline] def rd (xs : Array Float) (i : UInt64) : Float := xs[i.toNat]!

@[inline] def v3At (xs : Array Float) (i : UInt64) : V3 := ⟨rd xs i, rd xs (i + 1), rd xs (i + 2)⟩

@[inline] def q4At (xs : Array Float) (i : UInt64) : Q4 :=
  ⟨rd xs i, rd xs (i + 1), rd xs (i + 2), rd xs (i + 3)⟩

/-- The attitude of node `i`: the start, the goal, or waypoint `i - 2`. -/
def nodeAt (xs : Array Float) (d : Dims) (i : UInt64) : Q4 :=
  if i == 0 then q4At xs 8 else if i == 1 then q4At xs 12 else q4At xs (d.wayOff + 4 * (i - 2))

/-- The dimensions that the header states. -/
def dims (xs : Array Float) : Dims :=
  let nb := (rd xs 1).toUInt64
  let nc := (rd xs 2).toUInt64
  let nw := (rd xs 3).toUInt64
  let coneOff := 16 + 3 * nb
  let wayOff := coneOff + 6 * nc
  ⟨nb, nc, nw, coneOff, wayOff, wayOff + 4 * nw⟩

/-- `x` is a whole number from `lo` to `hi`. -/
@[inline] def isWord (x : Float) (lo hi : UInt64) : Bool :=
  let n := x.toUInt64
  n.toFloat == x && lo ≤ n && n ≤ hi

@[inline] def unitV (v : V3) : Bool := (dot v v - 1.0).abs ≤ tolNorm

@[inline] def unitQ (q : Q4) : Bool :=
  (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z - 1.0).abs ≤ tolNorm

def allFinite (xs : Array Float) : Bool :=
  LeanExe.loop xs.size.toUInt64 true fun i ok => ok && (rd xs i).abs ≤ maxFinite

def bodiesOk (xs : Array Float) (d : Dims) : Bool :=
  LeanExe.loop d.nb true fun k ok => ok && unitV (v3At xs (16 + 3 * k))

def conesOk (xs : Array Float) (d : Dims) : Bool :=
  LeanExe.loop d.nc true fun k ok =>
    let o := d.coneOff + 6 * k
    let c := rd xs (o + 4)
    let kind := rd xs (o + 5)
    ok && isWord (rd xs o) 0 (d.nb - 1) && unitV (v3At xs (o + 1)) && -1.0 ≤ c && c ≤ 1.0 &&
      (kind == 0.0 || kind == 1.0)

def waysOk (xs : Array Float) (d : Dims) : Bool :=
  LeanExe.loop d.nw true fun k ok => ok && unitQ (q4At xs (d.wayOff + 4 * k))

/-- The input is well formed: version 2, sizes within bounds and consistent with the length,
every value finite, limits within their ranges, vectors and quaternions of unit norm within the
tolerance, cone indices in range, cosines in `[-1, 1]`, and kinds 0 or 1. -/
def validInput (xs : Array Float) : Bool :=
  let size := xs.size.toUInt64
  if size < 16 then false
  else if !(rd xs 0 == 2.0 && isWord (rd xs 1) 1 8 && isWord (rd xs 2) 0 16 &&
      isWord (rd xs 3) 0 1024) then false
  else
    let d := dims xs
    if size != d.total then false
    else if !allFinite xs then false
    else
      let wmax := rd xs 4
      let amax := rd xs 5
      let settle := rd xs 6
      let maxEdge := rd xs 7
      rateMin ≤ wmax && wmax ≤ 1.0 && accelMin ≤ amax && amax ≤ 1.0 && 0.0 ≤ settle &&
        settle ≤ 3600.0 && 0.0 ≤ maxEdge && maxEdge ≤ 4.0 && unitQ (q4At xs 8) &&
        unitQ (q4At xs 12) && bodiesOk xs d && conesOk xs d && waysOk xs d

/-- Attitude `q` satisfies every cone with the margin plus `slack`. -/
def attitudeOk (xs : Array Float) (d : Dims) (q : Q4) (slack : Float) : Bool :=
  LeanExe.loop d.nc true fun k ok =>
    if !ok then false
    else
      let o := d.coneOff + 6 * k
      let b := v3At xs (16 + 3 * (rd xs o).toUInt64)
      let u := v3At xs (o + 1)
      let c := rd xs (o + 4)
      let f := dot u (qrot q b)
      if rd xs (o + 5) == 0.0 then f ≤ c - margin - slack else f ≥ c + margin + slack

/-- The rotation `rel` applied to attitude `qa` satisfies every cone at every angle.  During a
rotation by `φ` about the unit axis `n`, the cosine of a body vector `v₀` with a cone axis `u` is
`A cos φ + B sin φ + C`, with `A = u·v₀ - (n·u)(n·v₀)`, `B = u·(n × v₀)`, and `C = (n·u)(n·v₀)`.
On `[0, θ]` it has an interior maximum only when `B > 0` and `B cos θ - A sin θ < 0`, of value
`C + √(A² + B²)`, and an interior minimum only when `B < 0` and `B cos θ - A sin θ > 0`, of value
`C - √(A² + B²)`.  The check includes the stationary value unless a computed test excludes it by
more than `eta`.  Below `sMin`, the rotation is at most `2.125 s`, and the start attitude is
checked with that much more slack. -/
def edgeOk (xs : Array Float) (d : Dims) (qa rel : Q4) : Bool :=
  let s := Float.sqrt (rel.x * rel.x + rel.y * rel.y + rel.z * rel.z)
  if s < sMin then attitudeOk xs d qa (2.125 * s)
  else
    let n : V3 := ⟨rel.x / s, rel.y / s, rel.z / s⟩
    let ct := rel.w * rel.w - s * s
    let st := 2.0 * rel.w * s
    LeanExe.loop d.nc true fun k ok =>
      if !ok then false
      else
        let o := d.coneOff + 6 * k
        let b := v3At xs (16 + 3 * (rd xs o).toUInt64)
        let u := v3At xs (o + 1)
        let c := rd xs (o + 4)
        let v0 := qrot qa b
        let nu := dot n u
        let nv := dot n v0
        let f0 := dot u v0
        let aa := f0 - nu * nv
        let bb := dot u (cross n v0)
        let cc := nu * nv
        let f1 := aa * ct + bb * st + cc
        let d1 := bb * ct - aa * st
        let r := Float.sqrt (aa * aa + bb * bb)
        if rd xs (o + 5) == 0.0 then
          let m1 := max f0 f1
          let m2 := if bb < -eta || d1 > eta then m1 else max m1 (cc + r)
          m2 ≤ c - margin
        else
          let m1 := min f0 f1
          let m2 := if bb > eta || d1 < -eta then m1 else min m1 (cc - r)
          m2 ≥ c + margin

/-- The rotation angle of `rel`, from the library's `atan2`. -/
def angleOf (rel : Q4) : Float :=
  2.0 * atan2 (Float.sqrt (rel.x * rel.x + rel.y * rel.y + rel.z * rel.z)) rel.w

/-- `t` seconds in whole milliseconds, rounded up. -/
def ceilMs (t : Float) : UInt64 :=
  let y := t * 1000.0
  let n := y.toUInt64
  if n.toFloat < y then n + 1 else n

/-- The duration in milliseconds of a rest-to-rest rotation by `theta`. -/
def slewTicks (theta wmax amax : Float) : UInt64 :=
  ceilMs (if theta ≥ wmax * wmax / amax then theta / wmax + wmax / amax
    else 2.0 * Float.sqrt (theta / amax))

/-- The unvisited admitted node of least cost and that cost, the lowest index among equals, or
`n` when every such node is unreached. -/
def selectNext (s : Search) (n : UInt64) : UInt64 × UInt64 :=
  LeanExe.loop n (n, infinity) fun i acc =>
    let c := s.cost[i.toNat]!
    if !s.done[i.toNat]! && s.ok[i.toNat]! && c < acc.2 then (i, c) else acc

/-- Relaxes every edge out of node `u`.  An edge is checked only when it would improve the
target's cost.  The check sits in its own `if` because the compiled code evaluates both operands
of `&&`. -/
def relax (xs : Array Float) (d : Dims) (n u settleTicks : UInt64) (s : Search) : Search :=
  let qa := nodeAt xs d u
  let cu := s.cost[u.toNat]!
  let wmax := rd xs 4
  let amax := rd xs 5
  let maxEdge := rd xs 7
  LeanExe.loop n s fun v st =>
    if st.done[v.toNat]! || !st.ok[v.toNat]! || v == u then st
    else
      let rel := relative qa (nodeAt xs d v)
      let theta := angleOf rel
      if theta > maxEdge && !(u == 0 && v == 1) then st
      else
        let cand := cu + slewTicks theta wmax amax + settleTicks
        if cand < st.cost[v.toNat]! then
          if edgeOk xs d qa rel then
            { st with cost := st.cost.set! v.toNat cand, parent := st.parent.set! v.toNat u }
          else st
        else st

/-- One round of the search: finalize the next node and relax its edges, or stop. -/
def round (xs : Array Float) (d : Dims) (n settleTicks : UInt64) (s : Search) : Search :=
  match selectNext s n with
  | (u, _) =>
    if u == n then { s with finished := true }
    else
      let s1 := { s with done := s.done.set! u.toNat true, examined := s.examined + 1 }
      if u == 1 then { s1 with finished := true } else relax xs d n u settleTicks s1

def initial (xs : Array Float) (d : Dims) (n : UInt64) : Search :=
  { cost := LeanExe.build n fun i => if i == 0 then 0 else infinity,
    parent := LeanExe.build n fun _ => n,
    done := LeanExe.build n fun _ => false,
    ok := LeanExe.build n fun i => i < 2 || attitudeOk xs d (nodeAt xs d i) 0.0,
    finished := false,
    examined := 0 }

def search (xs : Array Float) (d : Dims) (n settleTicks : UInt64) : Search :=
  LeanExe.repeatWhile (n + 1) (initial xs d n) (fun s => !s.finished)
    (fun s => round xs d n settleTicks s)

/-- The number of edges on the parent chain from the goal back to the start. -/
def pathLength (s : Search) (n : UInt64) : UInt64 :=
  match LeanExe.repeatWhile n ((1 : UInt64), (0 : UInt64)) (fun p => p.1 != 0)
      (fun p => (s.parent[p.1.toNat]!, p.2 + 1)) with
  | (_, k) => k

/-- Node `j` of the path of `k` edges, counted from the start. -/
def pathNode (s : Search) (k j : UInt64) : UInt64 :=
  LeanExe.loop (k - j) (1 : UInt64) fun _ x => s.parent[x.toNat]!

/-- Field `f` of segment `g` of the path. -/
def segmentField (xs : Array Float) (d : Dims) (s : Search) (k settleTicks g f : UInt64) :
    Float :=
  let a := pathNode s k g
  let b := pathNode s k (g + 1)
  let qa := nodeAt xs d a
  let rel := relative qa (nodeAt xs d b)
  let sn := Float.sqrt (rel.x * rel.x + rel.y * rel.y + rel.z * rel.z)
  let big := sn ≥ axisMin
  if f == 0 then qa.w else if f == 1 then qa.x else if f == 2 then qa.y else if f == 3 then qa.z
  else if f == 4 then (if big then rel.x / sn else 1.0)
  else if f == 5 then (if big then rel.y / sn else 0.0)
  else if f == 6 then (if big then rel.z / sn else 0.0)
  else if f == 7 then angleOf rel
  else if f == 8 then (slewTicks (angleOf rel) (rd xs 4) (rd xs 5) + settleTicks).toFloat
  else if f == 9 then a.toFloat
  else b.toFloat

/-- A result with no segments. -/
def statusOnly (status : Float) (examined : UInt64) : Array Float :=
  LeanExe.build 4 fun i => if i == 0 then status else if i == 3 then examined.toFloat else 0.0

def output (xs : Array Float) (d : Dims) (s : Search) (n settleTicks : UInt64) : Array Float :=
  if s.cost[(1 : UInt64).toNat]! == infinity then statusOnly 0.0 s.examined
  else
    let k := pathLength s n
    LeanExe.build (8 + 11 * k) fun e =>
      if e == 0 then 1.0
      else if e == 1 then k.toFloat
      else if e == 2 then (s.cost[(1 : UInt64).toNat]!).toFloat
      else if e == 3 then s.examined.toFloat
      else if e < 4 + 11 * k then segmentField xs d s k settleTicks ((e - 4) / 11) ((e - 4) % 11)
      else rd xs (12 + (e - 4 - 11 * k))

/-- The planner: validation, the static checks of the start and the goal, the search, and the
output. -/
def plan (xs : Array Float) : Array Float :=
  if !validInput xs then statusOnly (-3.0) 0
  else
    let d := dims xs
    let n := d.nw + 2
    if !attitudeOk xs d (q4At xs 8) 0.0 then statusOnly (-1.0) 0
    else if !attitudeOk xs d (q4At xs 12) 0.0 then statusOnly (-2.0) 0
    else
      let settleTicks := ceilMs (rd xs 6)
      output xs d (search xs d n settleTicks) n settleTicks

end Demos.Slew
