import Demos.Attitude.Program
import TestSupport.Host

/-! Cases of the attitude module.  `cases` prints the module cases of `triad` for
`tests/verified/run.sh`, and `bits` prints, for each input, its class, the bits of the fourteen
arguments and of the true attitude's quaternion, and the result, which
`tests/attitude/reference.py` checks against an independent computation in mpmath.

The generator draws from SplitMix64 with fixed seeds.  A case of class `good` lies in the region
where the requirements require status 0: references at an angle `θ` from 10° to 170°, vector
lengths from `1e-3` to `1e3`, and `ε1 + ε2` at most `0.9 min(θ, π - θ)`.  Its measurements are the
references, each moved by up to 0.99 of its error bound and carried into the body frame by a
random true attitude.  A case of class `worst` moves the two observations by 0.999 of their
bounds toward opposite sides of the plane of the references, the direction of the first-order
worst case.  The classes `bad1` and `bad2` require status 1 and 2, and `any` requires none. -/

namespace TestSupport.Attitude.Cases

open TestSupport.Host Demos.Attitude

/-- SplitMix64: the output and the next state. -/
def mix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- A float in `[0, 1)` and the next state. -/
def unif (s : UInt64) : Float × UInt64 :=
  let (z, s) := mix s
  ((z >>> 11).toFloat / 9007199254740992.0, s)

structure V where
  x : Float
  y : Float
  z : Float

def V.scale (k : Float) (a : V) : V := ⟨k * a.x, k * a.y, k * a.z⟩
def V.add (a b : V) : V := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def V.cross (a b : V) : V := ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
def V.unit (a : V) : V := a.scale (1.0 / Float.sqrt (a.x * a.x + a.y * a.y + a.z * a.z))

/-- A random unit vector. -/
def randUnit (s : UInt64) : V × UInt64 :=
  let (u, s) := unif s
  let (w, s) := unif s
  let z := 2.0 * u - 1.0
  let r := Float.sqrt (1.0 - z * z)
  let f := 6.283185307179586 * w
  (⟨r * Float.cos f, r * Float.sin f, z⟩, s)

/-- A unit vector perpendicular to `a`. -/
def perp (a : V) : V :=
  let e : V := if Float.abs a.x < 0.9 then ⟨1.0, 0.0, 0.0⟩ else ⟨0.0, 1.0, 0.0⟩
  (a.cross e).unit

/-- `a` turned by the angle `t` toward the unit `p` perpendicular to it. -/
def turn (a p : V) (t : Float) : V := (a.scale (Float.cos t)).add (p.scale (Float.sin t))

/-- The slew planner's rotation `v ↦ q v q*` for a unit quaternion. -/
def rot (q : Float × Float × Float × Float) (v : V) : V :=
  let (w, x, y, z) := q
  let tx := 2.0 * (y * v.z - z * v.y)
  let ty := 2.0 * (z * v.x - x * v.z)
  let tz := 2.0 * (x * v.y - y * v.x)
  ⟨v.x + w * tx + (y * tz - z * ty), v.y + w * ty + (z * tx - x * tz),
    v.z + w * tz + (x * ty - y * tx)⟩

/-- A class, the fourteen arguments, and the true attitude's quaternion. -/
abbrev Case := String × (V × V × V × V × Float × Float) × (Float × Float × Float × Float)

def deg : Float := 0.017453292519943295

/-- A generated case of class `good`, or of class `worst` when `worst` holds. -/
def gen (worst : Bool) (seed : UInt64) : Case :=
  let (r1, s) := randUnit seed
  let (u, s) := unif s
  let θ := (10.0 + 160.0 * u) * deg
  let (c, s) := unif s
  let p0 := perp r1
  let p := turn p0 (r1.cross p0).unit (6.283185307179586 * c)
  let r2 := turn r1 p θ
  let lim := 0.9 * (if θ < 3.141592653589793 - θ then θ else 3.141592653589793 - θ)
  let (f, s) := unif s
  let (g, s) := unif s
  let (k, s) := unif s
  let e1 := lim * f * k
  let e2 := lim * (1.0 - f) * k * g
  let n := (r1.cross r2).unit
  let (d1, s) := randUnit s
  let (d2, s) := randUnit s
  let (a1, s) := unif s
  let (a2, s) := unif s
  let p1 := if worst then n else (r1.cross d1).unit
  let p2 := if worst then n.scale (-1.0) else (r2.cross d2).unit
  let t1 := if worst then 0.999 * e1 else 0.99 * e1 * a1
  let t2 := if worst then 0.999 * e2 else 0.99 * e2 * a2
  let u1 := turn r1 p1 t1
  let u2 := turn r2 p2 t2
  let (qa, s) := unif s
  let (qb, s) := unif s
  let (qc, s) := unif s
  let (qd, s) := unif s
  let qn := Float.sqrt ((qa - 0.5) ^ 2 + (qb - 0.5) ^ 2 + (qc - 0.5) ^ 2 + (qd - 0.5) ^ 2)
  let q := ((qa - 0.5) / qn, (qb - 0.5) / qn, (qc - 0.5) / qn, (qd - 0.5) / qn)
  let qinv := (q.1, -q.2.1, -q.2.2.1, -q.2.2.2)
  let (l1, s) := unif s
  let (l2, s) := unif s
  let (l3, s) := unif s
  let (l4, _) := unif s
  let len := fun (t : Float) => Float.exp ((6.0 * t - 3.0) * 2.302585092994046)
  let b1 := (rot qinv u1).scale (len l1)
  let b2 := (rot qinv u2).scale (len l2)
  (if worst then "worst" else "good", (b1, b2, r1.scale (len l3), r2.scale (len l4), e1, e2), q)

def ex : V := ⟨1.0, 0.0, 0.0⟩
def ey : V := ⟨0.0, 1.0, 0.0⟩
def one : Float × Float × Float × Float := (1.0, 0.0, 0.0, 0.0)

/-- Inputs that require status 1 or 2, and inputs at the edges of the region. -/
def edges : List Case :=
  [ ("bad1", (⟨0.0, 0.0, 0.0⟩, ey, ex, ey, 0.01, 0.01), one),
    ("bad1", (ex, ex, ex, ey, 0.01, 0.01), one),
    ("bad1", (ex, ey, ex, ex, 0.01, 0.01), one),
    ("bad1", (ex, ey, ex.scale (-2.0), ex, 0.01, 0.01), one),
    ("bad1", (⟨nan, 0.0, 0.0⟩, ey, ex, ey, 0.01, 0.01), one),
    ("bad1", (ex, ⟨0.0, inf, 0.0⟩, ex, ey, 0.01, 0.01), one),
    ("bad1", (ex, ey, ex, ⟨0.0, 0.0, -inf⟩, 0.01, 0.01), one),
    ("bad1", (ex.scale 1e200, ey.scale 1e200, ex, ey, 0.01, 0.01), one),
    ("bad1", (ex, ey, ex, ⟨1.0, 1e-170, 0.0⟩, 0.01, 0.01), one),
    ("bad2", (ex, ey, ex, ey, nan, 0.01), one),
    ("bad2", (ex, ey, ex, ey, 0.01, inf), one),
    ("bad2", (ex, ey, ex, ey, -0.01, 0.01), one),
    ("bad2", (ex, ey, ex, ey, 0.0, -1e-300), one),
    ("bad2", (ex, ey, ex, ey, 0.8, 0.8), one),
    ("bad2", (ex, ey, ex, ⟨1.0, 0.01, 0.0⟩, 0.01, 0.01), one),
    ("bad2", (ex, ey, ex, ⟨1.0, 0.1, 0.0⟩, 0.05, 0.05), one),
    ("good", (ex, ey, ex, ey, 0.0, 0.0), one),
    ("good", (ex, ey, ex, ey, 0.1, 0.0), one),
    ("good", (ex, ⟨1.0, 1.7320508075688772, 0.0⟩, ex, ⟨2.0, 3.4641016151377544, 0.0⟩, 0.01,
      0.003), one),
    ("good", (ex, ⟨-1.0, 1.7320508075688772, 0.0⟩, ex, ⟨-0.5, 0.8660254037844386, 0.0⟩, 0.003,
      0.01), one),
    ("any", (ex, ey, ex, ey, 0.7, 0.7), one),
    ("any", (ex, ey, ex, ⟨1.0, 0.1, 0.0⟩, 0.05, 0.04), one) ]

def all : List Case :=
  edges ++ (List.range 120).map (fun i => gen false (UInt64.ofNat (1000 + i))) ++
    (List.range 60).map (fun i => gen true (UInt64.ofNat (5000 + i)))

def call (c : Case) : Estimate :=
  let (_, (b1, b2, r1, r2, e1, e2), _) := c
  triad b1.x b1.y b1.z b2.x b2.y b2.z r1.x r1.y r1.z r2.x r2.y r2.z e1 e2

def args (c : Case) : List Float :=
  let (_, (b1, b2, r1, r2, e1, e2), _) := c
  [b1.x, b1.y, b1.z, b2.x, b2.y, b2.z, r1.x, r1.y, r1.z, r2.x, r2.y, r2.z, e1, e2]

def ivs (e : Estimate) : List Library.Numerics.Interval.Interval :=
  [e.m11, e.m12, e.m13, e.m21, e.m22, e.m23, e.m31, e.m32, e.m33]

def kind : String :=
  "list:i64," ++ ",".intercalate ((List.range 9).map fun _ => "i64,f64,f64") ++ ",f64"

def render (e : Estimate) : String :=
  s!"{e.status} " ++
    " ".intercalate ((ivs e).map fun i => s!"{i.status} {i.lo.toBits} {i.hi.toBits}") ++
    s!" {e.err.toBits}"

def cases : IO Unit := do
  for c in all do
    line "attitude" "triad" kind ((args c).map fl) (render (call c))

def bits : IO Unit := do
  for c in all do
    let (cls, _, (qw, qx, qy, qz)) := c
    let input := " ".intercalate ((args c ++ [qw, qx, qy, qz]).map fun x => toString x.toBits)
    IO.println s!"{cls} {input} {render (call c)}"

end TestSupport.Attitude.Cases
