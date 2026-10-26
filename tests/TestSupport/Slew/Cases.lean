import Demos.Slew.Program
import Library.Random.SplitMix64.Program
import Library.Numerics.Float64.Trig.Program

/-! The cases of the module `slew`: `plan` on inputs that a deterministic generator builds, and
`atan2` on special and random arguments, with native Lean's results.  The generator draws from
SplitMix64 with a fixed seed for each class of inputs and uses only correctly rounded operations:
it builds an angle from a tangent `t` by `cos = (1 - t²)/(1 + t²)` and `sin = 2t/(1 + t²)`, and an
attitude from an orthonormal frame, and it takes the cosines of the realistic cones from the
library's `Trig.cos`.  The inputs are therefore the same on every host.

The classes are realistic plans with 0, 60, 200, and 500 waypoints and variations of the limits;
cones whose limit grazes a rotation's designed extremum; stationary points of the cosine near the
start and the end of a rotation; rotations near the small-angle threshold and near `π`; extreme
cones; vectors and quaternions at the norm tolerance; and invalid inputs.  A plan case requires two
retained blocks, the host's input and the result, which holds when `plan` borrows its input.  The
safety theorem `Demos.Slew.Safety.plan_safe` replaced a sampled safety check that the generator
ran before the theorem was proved. -/

namespace TestSupport.Slew.Cases

open Demos.Slew (V3 Q4 plan)

abbrev Gen := StateM UInt64

def word : Gen UInt64 := modifyGet fun s =>
  let (s', v) := Library.Random.SplitMix64.splitMix s
  (v, s')

def uniform : Gen Float := return Library.Random.SplitMix64.unitFloat (← word)

def between (lo hi : Float) : Gen Float := return lo + (hi - lo) * (← uniform)

def pick (xs : List Float) : Gen Float := return xs[((← word) % xs.length.toUInt64).toNat]!

def vadd (a b : V3) : V3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def vsub (a b : V3) : V3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def vscale (a : V3) (k : Float) : V3 := ⟨a.x * k, a.y * k, a.z * k⟩
def vdot (a b : V3) : Float := a.x * b.x + a.y * b.y + a.z * b.z
def vcross (a b : V3) : V3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
def vunit (a : V3) : V3 := vscale a (1 / (vdot a a).sqrt)

def qmul (a b : Q4) : Q4 :=
  ⟨a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z, a.w * b.x + a.x * b.w + a.y * b.z - a.z * b.y,
    a.w * b.y - a.x * b.z + a.y * b.w + a.z * b.x, a.w * b.z + a.x * b.y - a.y * b.x + a.z * b.w⟩
def qscale (q : Q4) (k : Float) : Q4 := ⟨q.w * k, q.x * k, q.y * k, q.z * k⟩
def qunit (q : Q4) : Q4 := qscale q (1 / (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z).sqrt)

/-- The rotation matrix of the unit quaternion `q` applied to `v`. -/
def rot (q : Q4) (v : V3) : V3 :=
  let w := q.w
  let x := q.x
  let y := q.y
  let z := q.z
  ⟨(1 - 2 * (y * y + z * z)) * v.x + 2 * (x * y - w * z) * v.y + 2 * (x * z + w * y) * v.z,
    2 * (x * y + w * z) * v.x + (1 - 2 * (x * x + z * z)) * v.y + 2 * (y * z - w * x) * v.z,
    2 * (x * z - w * y) * v.x + 2 * (y * z + w * x) * v.y + (1 - 2 * (x * x + y * y)) * v.z⟩

/-- The cosine and sine of `2 atan t`. -/
def cosOf (t : Float) : Float := (1 - t * t) / (1 + t * t)
def sinOf (t : Float) : Float := 2 * t / (1 + t * t)

/-- The rotation by `4 atan t` about the unit axis `n`. -/
def turn (n : V3) (t : Float) : Q4 :=
  let s := sinOf t
  ⟨cosOf t, n.x * s, n.y * s, n.z * s⟩

/-- The rotation by `2 atan t` about the unit axis `n`. -/
def halfTurn (n : V3) (t : Float) : Q4 :=
  let r := (1 + t * t).sqrt
  ⟨1 / r, n.x * t / r, n.y * t / r, n.z * t / r⟩

/-- The attitude whose body axes are the orthonormal columns `a`, `b`, and `c`, by the largest
diagonal term of the matrix. -/
def ofFrame (a b c : V3) : Q4 :=
  let tr := a.x + b.y + c.z
  qunit <|
    if tr > 0 then
      let s := 2 * (tr + 1).sqrt
      ⟨0.25 * s, (b.z - c.y) / s, (c.x - a.z) / s, (a.y - b.x) / s⟩
    else if a.x > b.y && a.x > c.z then
      let s := 2 * (1 + a.x - b.y - c.z).sqrt
      ⟨(b.z - c.y) / s, 0.25 * s, (b.x + a.y) / s, (c.x + a.z) / s⟩
    else if b.y > c.z then
      let s := 2 * (1 + b.y - a.x - c.z).sqrt
      ⟨(c.x - a.z) / s, (b.x + a.y) / s, 0.25 * s, (c.y + b.z) / s⟩
    else
      let s := 2 * (1 + c.z - a.x - b.y).sqrt
      ⟨(a.y - b.x) / s, (c.x + a.z) / s, (c.y + b.z) / s, 0.25 * s⟩

def unitVec : Gen V3 := do
  for _ in [0:1000] do
    let v : V3 := ⟨(← between (-1) 1), (← between (-1) 1), (← between (-1) 1)⟩
    let n2 := vdot v v
    if n2 > 0.01 && n2 ≤ 1 then return vscale v (1 / n2.sqrt)
  return ⟨1, 0, 0⟩

def unitQuat : Gen Q4 := do
  for _ in [0:1000] do
    let q : Q4 :=
      ⟨(← between (-1) 1), (← between (-1) 1), (← between (-1) 1), (← between (-1) 1)⟩
    let n2 := q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z
    if n2 > 0.01 && n2 ≤ 1 then return qscale q (1 / n2.sqrt)
  return ⟨1, 0, 0, 0⟩

/-- A unit vector perpendicular to the unit vector `n`. -/
def perpendicular (n : V3) : Gen V3 := do
  for _ in [0:1000] do
    let r ← unitVec
    let p := vsub r (vscale n (vdot r n))
    if vdot p p > 0.01 then return vunit p
  return vunit (vcross n ⟨0.6, 0.48, 0.64⟩)

/-- The attitude with boresight `d` (body `+X`) and the direction `first` in the body's `X`–`Z`
plane on the `+Z` side, if `first` is not along `d`. -/
def nominal (d first : V3) : Option Q4 :=
  let z := vsub first (vscale d (vdot first d))
  let n2 := vdot z z
  if n2 < 1e-6 then none
  else
    let z := vscale z (1 / n2.sqrt)
    some (ofFrame d (vcross z d) z)

structure Cone where
  body : Nat
  u : V3
  cos : Float
  keepIn : Bool

def d2r : Float := 3.141592653589793 / 180

def cosd (deg : Float) : Float := Library.Numerics.Float64.Trig.cos (deg * d2r)

structure Scene where
  q0 : Q4
  q1 : Q4
  bodies : List V3
  cones : List Cone
  ways : List Q4
  wmax : Float := 0.12 * d2r
  amax : Float := 0.0008 * d2r
  settle : Float := 20
  maxEdge : Float := 60 * d2r

def v3s (v : V3) : List Float := [v.x, v.y, v.z]
def q4s (q : Q4) : List Float := [q.w, q.x, q.y, q.z]

def pack (s : Scene) : Array Float :=
  ([2, s.bodies.length.toFloat, s.cones.length.toFloat, s.ways.length.toFloat, s.wmax, s.amax,
      s.settle, s.maxEdge] ++ q4s s.q0 ++ q4s s.q1 ++ s.bodies.flatMap v3s ++
    s.cones.flatMap (fun c => c.body.toFloat :: (v3s c.u ++ [c.cos, if c.keepIn then 1 else 0])) ++
    s.ways.flatMap q4s).toArray

def xAxis : V3 := ⟨1, 0, 0⟩

/-- A rotation from `q0` to `q1` of the body vector `+X` under one cone, with edges of up to 3.2
rad. -/
def single (q0 q1 : Q4) (cone : Cone) (ways : List Q4 := []) : Array Float :=
  pack { q0, q1, bodies := [xAxis], cones := [cone], ways, maxEdge := 3.2 }

/-- The body vectors of the realistic plans: the boresight `+X`, the array normal `+Z`, and `±Y`. -/
def planBodies : List V3 := [⟨1, 0, 0⟩, ⟨0, 0, 1⟩, ⟨0, 1, 0⟩, ⟨0, -1, 0⟩]

/-- Attitude `q` satisfies every cone with `slack` to spare. -/
def passes (bodies : List V3) (cones : List Cone) (q : Q4) (slack : Float) : Bool :=
  cones.all fun c =>
    let f := vdot c.u (rot q (bodies.getD c.body xAxis))
    if c.keepIn then decide (f ≥ c.cos + slack) else decide (f ≤ c.cos - slack)

/-- Three constraint directions and the six cones of a telescope's usual shape: the boresight at
least 50° from the first direction and 20° and 15° beyond the angular radii of the other two, the
array normal within 70° of the first, and `±Y` at least 75° from it. -/
def environment : Gen (V3 × List Cone) := do
  let first ← unitVec
  let second ← unitVec
  let third ← unitVec
  let r2 ← pick [3, 8, 25]
  let r3 ← pick [0.1, 0.5]
  return (first, [⟨0, first, cosd 50, false⟩, ⟨0, second, cosd (r2 + 20), false⟩,
    ⟨0, third, cosd (r3 + 15), false⟩, ⟨1, first, cosd 70, true⟩, ⟨2, first, cosd 75, false⟩,
    ⟨3, first, cosd 75, false⟩])

def waypoints (first : V3) (n : Nat) : Gen (List Q4) := do
  let mut ways : Array Q4 := #[]
  for _ in [0:n] do
    if let some q := nominal (← unitVec) first then ways := ways.push q
  return ways.toList

/-- A nominal attitude that passes every cone with `1e-6` to spare, if one of 500 draws does. -/
def pointing (first : V3) (cones : List Cone) : Gen (Option Q4) := do
  for _ in [0:500] do
    if let some q := nominal (← unitVec) first then
      if passes planBodies cones q 1e-6 then return some q
  return none

def realisticScene (n : Nat) : Gen (Option Scene) := do
  let (first, cones) ← environment
  let ways ← waypoints first n
  match (← pointing first cones), (← pointing first cones) with
  | some q0, some q1 => return some { q0, q1, bodies := planBodies, cones, ways }
  | _, _ => return none

def realistic : Gen (List (Array Float)) := do
  let mut out : Array (Array Float) := #[]
  for i in [0:48] do
    match ← realisticScene ([500, 200, 60, 0].getD (i % 4) 0) with
    | some s => out := out.push (pack s)
    | none => pure ()
  return out.toList

/-- Variations of the limits on scenes of 500 waypoints: fast and slow slews, shorter edges, no
edges but the direct one, and edges of at most 15° and 10°. -/
def limits : Gen (List (Array Float)) := do
  let mut out : Array (Array Float) := #[]
  for _ in [0:3] do
    match ← realisticScene 500 with
    | none => pure ()
    | some s =>
      out := out ++ #[pack { s with wmax := 0.5 * d2r, amax := 0.005 * d2r, settle := 0 },
        pack { s with wmax := 0.01 * d2r, amax := 0.0001 * d2r, settle := 300 },
        pack { s with maxEdge := 20 * d2r }, pack { s with maxEdge := 0 },
        pack { s with maxEdge := 15 * d2r }, pack { s with maxEdge := 10 * d2r }]
  return out.toList

/-- A single cone whose limit sits at a chosen distance from the designed extremum of a rotation.
With `p ⊥ n`, `v₀ = cos γ p + sin γ n`, and `u = cos β R(n, φ*) p + sin β n`, the cosine along the
rotation is `cos β cos γ cos (φ - φ*) + sin β sin γ`, whose maximum `cos (β - γ)` lies at `φ*`
inside the rotation. -/
def grazing : Gen (List (Array Float)) := do
  let mut out : Array (Array Float) := #[]
  for i in [0:24] do
    let n ← unitVec
    let p ← perpendicular n
    let t ← between 0.05 0.75
    let ts := (← between 0.2 0.8) * (2 * t / (1 - t * t))
    let pstar := vadd (vscale p (cosOf ts)) (vscale (vcross n p) (sinOf ts))
    let tg ← between (-0.4) 0.4
    let tb ← between (-0.4) 0.4
    let v0 := vadd (vscale p (cosOf tg)) (vscale n (sinOf tg))
    let y0 := vunit (vcross n v0)
    let qa := ofFrame v0 y0 (vcross v0 y0)
    let qb := qmul (turn n t) qa
    let extremum := cosOf tb * cosOf tg + sinOf tb * sinOf tg
    let keepIn := i % 2 == 1
    let sign := if keepIn then -1 else 1
    let u := vscale (vadd (vscale pstar (cosOf tb)) (vscale n (sinOf tb))) sign
    for eps in [-1e-8, -2e-9, -1.1e-9, -1e-10, 0, 1e-10, 1.1e-9, 1.2e-9, 2e-9, 1e-8] do
      let c := if keepIn then -extremum - eps else extremum + eps
      if -1 ≤ c && c ≤ 1 then
        out := out.push (single qa qb ⟨0, u, c, keepIn⟩)
  return out.toList

/-- A stationary point of the cosine at the start of a rotation, and by reversal at its end: `u`
has a component `t (n × v₀)`, so `B` is proportional to `t`. -/
def stationary : Gen (List (Array Float)) := do
  let mut out : Array (Array Float) := #[]
  for _ in [0:6] do
    let qa ← unitQuat
    let n ← unitVec
    let qb := qmul (turn n (← between 0.08 0.45)) qa
    let v0 := rot qa xAxis
    let perp := vsub v0 (vscale n (vdot n v0))
    for t in [-1e-6, -1e-11, -1e-13, 0, 1e-13, 1e-11, 1e-6] do
      for keepIn in [false, true] do
        let u := vunit (vadd (vadd (vscale perp (if keepIn then -1 else 1)) (vscale n 0.8))
          (vscale (vcross n v0) t))
        let f0 := vdot u v0
        for gap in [2e-9, 1e-12] do
          let c := if keepIn then f0 - gap else f0 + gap
          if -1 ≤ c && c ≤ 1 then
            out := out.push (single qa qb ⟨0, u, c, keepIn⟩)
            out := out.push (single qb qa ⟨0, u, c, keepIn⟩)
  return out.toList

/-- Rotations whose relative quaternion has a vector length `s` near 0 and near the small-angle
threshold `1e-7`, or a scalar part near 0, so an angle near `π`, small rotations whose start lies
`1e-8` inside the limit, and antipodal quaternions. -/
def angles : Gen (List (Array Float)) := do
  let mut out : Array (Array Float) := #[]
  for _ in [0:6] do
    let qa ← unitQuat
    let n ← unitVec
    let u ← unitVec
    let f0 := vdot u (rot qa xAxis)
    let cosOut := if f0 + 0.3 ≤ 1 then f0 + 0.3 else 1
    let one (d : Q4) (c : Float) : Array Float := single qa (qmul d qa) ⟨0, u, c, false⟩
    for s in [0, 1e-15, 1e-12, 1e-9, 0.995e-7, 1e-7, 1.005e-7, 1e-6, 1e-3] do
      out := out.push (one ⟨(1 - s * s).sqrt, n.x * s, n.y * s, n.z * s⟩ cosOut)
    for w in [1e-3, 1e-6, 1e-9, 1e-15, 0] do
      let s := (1 - w * w).sqrt
      out := out.push (one ⟨w, n.x * s, n.y * s, n.z * s⟩ cosOut)
    for s in [5e-10, 5e-9, 2.5e-8, 0.95e-7] do
      out := out.push (one ⟨(1 - s * s).sqrt, n.x * s, n.y * s, n.z * s⟩ (f0 + 1.1e-9 + 1e-8))
    out := out.push
      (pack { q0 := qa, q1 := qscale qa (-1), bodies := [xAxis], cones := [], ways := [] })
  return out.toList

/-- Cones of cosine 0, 1, and -1, and of half-angle `1e-6` on and beside the path, placed so that
the endpoints pass and the edge check decides. -/
def extremeCones : Gen (List (Array Float)) := do
  let mut out : Array (Array Float) := #[]
  let tiny := Library.Numerics.Float64.Trig.cos 1e-6
  for i in [0:8] do
    let qa ← unitQuat
    let n ← unitVec
    let t ← between 0.08 0.35
    let qb := qmul (turn n t) qa
    let mid := rot (qmul (halfTurn n t) qa) xAxis
    let mean := vunit (vadd (rot qa xAxis) (rot qb xAxis))
    let offset := [3e-7, 1e-6, 3e-6, 1e-5].getD (i % 4) 0
    let near := vunit (vadd mid (vscale (vunit (vcross n mid)) offset))
    let ways := [(← unitQuat), (← unitQuat), (← unitQuat)]
    let away := vscale mean (-1)
    let cones : List Cone := [⟨0, away, 0, false⟩, ⟨0, mean, 0, true⟩, ⟨0, near, tiny, false⟩,
      ⟨0, mid, tiny, false⟩, ⟨0, mean, -1, false⟩, ⟨0, mean, 1, true⟩, ⟨0, away, 1, false⟩,
      ⟨0, mean, -1, true⟩]
    for c in cones do
      out := out.push (single qa qb c ways)
  return out.toList

/-- A body vector and the start quaternion scaled just inside and just outside the tolerance on
squared norms. -/
def norms : Gen (List (Array Float)) := do
  for _ in [0:4] do
    match ← realisticScene 60 with
    | none => pure ()
    | some s =>
      let mut out : Array (Array Float) := #[]
      for f in [1 + 4.9e-13, 1 + 5.1e-13, 1 - 4.9e-13, 1 - 5.1e-13] do
        let bodies := planBodies.mapIdx fun i b => if i == 1 then vscale b f else b
        out := out.push (pack { s with bodies })
        out := out.push (pack { s with q0 := qscale s.q0 f })
      return out.toList
  return []

def nan : Float := 0 / 0
def inf : Float := 1 / 0

/-- Inputs of every kind that `validInput` rejects, a start and a goal that violate a cone, and
no cones. -/
def invalid : Gen (List (Array Float)) := do
  for _ in [0:20] do
    match ← realisticScene 10 with
    | none => pure ()
    | some s =>
      let good := pack s
      let x0 := rot s.q0 xAxis
      let x1 := rot s.q1 xAxis
      let many := (List.range 1025).foldl (fun a _ => a ++ #[1, 0, 0, 0])
        ((pack { s with ways := [] }).set! 3 1025)
      return [good, good.set! 20 nan, good.set! 30 inf, good.set! 31 (-inf), good.set! 0 1,
        good.set! 1 0, good.set! 1 3.5, good.set! 2 17, good.push 0, good.pop, good.set! 28 4,
        good.set! 33 2, good.set! 32 1.0000001, good.set! 4 0, good.set! 5 2, good.set! 6 (-1),
        good.set! 7 5, good.set! 8 (good[8]! * 1.001), #[2, 1, 0, 0], #[], many,
        pack { s with bodies := [xAxis], cones := [], ways := [] },
        pack { s with bodies := [xAxis], cones := [⟨0, x0, 0.5, false⟩], ways := [] },
        pack { s with bodies := [xAxis], cones := [⟨0, x1, 0.5, false⟩], ways := [] }]
  return []

def specials : List Float :=
  [0, -0.0, 1, -1, 1e-300, -1e-300, 5e-324, 1e300, inf, -inf, nan, 0.5, 2, 1e-8, 1e8]

/-- `10 ^ (k - 20)`, correctly rounded. -/
def power (k : Nat) : Float :=
  if k < 20 then Float.ofScientific 1 true (20 - k) else Float.ofScientific 1 false (k - 20)

/-- A float from the bit pattern `w`, with the canonical NaN for every NaN pattern, since the host
canonicalizes NaN results and native code need not. -/
def pattern (w : UInt64) : Float := let x := Float.ofBits w; if x.isNaN then nan else x

/-- The arguments of the `atan2` cases: all pairs of special values, random bit patterns, and
random values with decimal exponents from -20 to 19. -/
def atanArgs : Gen (List (Float × Float)) := do
  let mut out : Array (Float × Float) := #[]
  for y in specials do
    for x in specials do
      out := out.push (y, x)
  for i in [0:1000] do
    if i % 2 == 0 then
      out := out.push (pattern (← word), pattern (← word))
    else
      let y := (2 * (← uniform) - 1) * power ((← word) % 40).toNat
      let x := (2 * (← uniform) - 1) * power ((← word) % 40).toNat
      out := out.push (y, x)
  return out.toList

def words (xs : Array Float) : String := ",".intercalate (xs.toList.map fun x => toString x.toBits)

def planLine (xs out : Array Float) : String :=
  let result := ", ".intercalate (out.toList.map fun x => toString x.toBits)
  s!"slew|plan|array-u64|array-u64:{words xs}|[{result}]|2"

def classes : List (String × List (Array Float)) :=
  [("realistic", Id.run (realistic.run' 1)), ("limits", Id.run (limits.run' 2)),
    ("grazing", Id.run (grazing.run' 3)), ("stationary", Id.run (stationary.run' 4)),
    ("angles", Id.run (angles.run' 5)), ("extreme cones", Id.run (extremeCones.run' 6)),
    ("norms", Id.run (norms.run' 7)), ("invalid", Id.run (invalid.run' 8))]

def statusIndex (s : Float) : Nat :=
  if s == 1 then 0 else if s == 0 then 1 else if s == -1 then 2 else if s == -2 then 3 else 4

/-- Prints the cases, or with `summary` the count of each class's statuses. -/
def run (summary : Bool) : IO Unit := do
  for (name, inputs) in classes do
    let mut counts : Array Nat := #[0, 0, 0, 0, 0]
    for xs in inputs do
      let out := plan xs
      if !summary then IO.println (planLine xs out)
      counts := counts.modify (statusIndex out[0]!) (· + 1)
    if summary then
      IO.println s!"{name}: {inputs.length} plans, statuses 1 0 -1 -2 -3: {counts}"
  for (y, x) in Id.run (atanArgs.run' 9) do
    if !summary then
      let r := Library.Numerics.Float64.Atan.atan2 y x
      IO.println s!"slew|atan2|f64|f64:{y.toBits} f64:{x.toBits}|{r.toBits}"

def cases : IO Unit := run false

end TestSupport.Slew.Cases
