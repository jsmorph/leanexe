import Demos.Attitude.QProgram
import TestSupport.Attitude.Cases

/-! Cases of the q-method module.  `cases` prints the module cases of `qmethod` for
`tests/verified/run.sh`, and `bits` prints, for each input, its class, the number of input
values, the bits of the input and of the true attitude's quaternion, and the bits of the result,
which `tests/attitude/qreference.py` checks against an independent computation in mpmath.

The generator draws from SplitMix64 with fixed seeds.  A case of class `good` has from 2 to 16
observations with references in random directions, two references at an angle from 20° to 160°
when there are two, weights from 0.5 to 2, error bounds from 0.1 to 1 times a largest bound of
`1e-4`, `1e-3`, `1e-2`, or `3e-2`, and vector lengths from `1e-3` to `1e3`.  Its measurements
are the references, each moved by up to 0.99 of its error bound in a random direction and
carried into the body frame by a random true attitude.  A case of class `bias` moves every
reference by 0.999 of its bound perpendicular to the plane of the reference and one common
axis.  The classes `bad1` and `bad2` require status 1 and 2, and the class `edge` requires
status 0.  A case of class `turned` applies `certify` to the program's quaternion turned by
`1e-6`, `1e-4`, or `1e-2` toward the column of the second largest estimate, so that `errOpt` is
large enough for the reference to compare it with its formula.  Such a case appears in `bits`
only, since the module test calls the export `qmethod`. -/

namespace TestSupport.Attitude.QCases

open TestSupport.Host Demos.Attitude.QMethod TestSupport.Attitude.Cases

/-- A class, the input, and the true attitude's quaternion. -/
abbrev Case := String × List Float × (Float × Float × Float × Float)

/-- A random unit quaternion and the next state. -/
def randQuat (s : UInt64) : (Float × Float × Float × Float) × UInt64 :=
  let (qa, s) := unif s
  let (qb, s) := unif s
  let (qc, s) := unif s
  let (qd, s) := unif s
  let qn := Float.sqrt ((qa - 0.5) ^ 2 + (qb - 0.5) ^ 2 + (qc - 0.5) ^ 2 + (qd - 0.5) ^ 2)
  (((qa - 0.5) / qn, (qb - 0.5) / qn, (qc - 0.5) / qn, (qd - 0.5) / qn), s)

/-- A length from `1e-3` to `1e3` and the next state. -/
def randLen (s : UInt64) : Float × UInt64 :=
  let (t, s) := unif s
  (Float.exp ((6.0 * t - 3.0) * 2.302585092994046), s)

/-- The record of one observation: the reference `r` moved by the angle `t` toward the unit `p`
perpendicular to it and carried into the body frame by `qinv`, with random lengths. -/
def record (qinv : Float × Float × Float × Float) (r p : V) (t a e : Float) (s : UInt64) :
    List Float × UInt64 :=
  let u := turn r p t
  let (lb, s) := randLen s
  let (lr, s) := randLen s
  let b := (rot qinv u).scale lb
  let r' := r.scale lr
  ([b.x, b.y, b.z, r'.x, r'.y, r'.z, a, e], s)

/-- The references of `n` observations: random directions, or two at an angle from 20° to
160°. -/
def references (n : Nat) (s : UInt64) : List V × UInt64 :=
  if n == 2 then
    let (r1, s) := randUnit s
    let (u, s) := unif s
    let (c, s) := unif s
    let p0 := perp r1
    let p := turn p0 (r1.cross p0).unit (6.283185307179586 * c)
    ([r1, turn r1 p ((20.0 + 140.0 * u) * deg)], s)
  else
    (List.range n).foldl (fun (acc : List V × UInt64) _ =>
      let (r, s) := randUnit acc.2
      (acc.1 ++ [r], s)) ([], s)

def emaxOf (k : Nat) : Float :=
  if k % 4 == 0 then 1e-4 else if k % 4 == 1 then 1e-3 else if k % 4 == 2 then 1e-2 else 3e-2

/-- A generated case of class `good`, or of class `bias` when `bias` holds. -/
def gen (bias : Bool) (n : Nat) (emax : Float) (seed : UInt64) : Case :=
  let (q, s) := randQuat seed
  let qinv := (q.1, -q.2.1, -q.2.2.1, -q.2.2.2)
  let (axis, s) := randUnit s
  let (rs, s) := references n s
  let (body, _) := rs.foldl (fun (acc : List Float × UInt64) r =>
    let (ua, s) := unif acc.2
    let (ue, s) := unif s
    let (ut, s) := unif s
    let (d, s) := randUnit s
    let a := 0.5 + 1.5 * ua
    let e := emax * (0.1 + 0.9 * ue)
    let p := if bias then (r.cross axis).unit else (r.cross d).unit
    let t := if bias then 0.999 * e else 0.99 * e * ut
    let (rec, s) := record qinv r p t a e s
    (acc.1 ++ rec, s)) ([], s)
  (if bias then "bias" else "good", n.toFloat :: body, q)

def ex : V := ⟨1.0, 0.0, 0.0⟩
def ey : V := ⟨0.0, 1.0, 0.0⟩
def ez : V := ⟨0.0, 0.0, 1.0⟩
def id4 : Float × Float × Float × Float := (1.0, 0.0, 0.0, 0.0)

/-- An input of the given observations, each `(b, r, a, ε)`. -/
def input (obs : List (V × V × Float × Float)) : List Float :=
  obs.length.toFloat :: obs.flatMap fun (b, r, a, e) => [b.x, b.y, b.z, r.x, r.y, r.z, a, e]

/-- Three exact observations of the identity attitude. -/
def three : List (V × V × Float × Float) := [(ex, ex, 1.0, 0.01), (ey, ey, 1.0, 0.01),
  (ez, ez, 1.0, 0.01)]

/-- The rotation by `arccos (-0.875)` about `(1, 0.3, -0.2)`, at which the first diagonal entry of
`K - c I` is zero for three orthogonal exact observations, so that an unpivoted factorization
fails. -/
def turnedFrame : Float × Float × Float × Float :=
  let n : V := V.unit ⟨1.0, 0.3, -0.2⟩
  let h := 0.5 * Float.acos (-0.875)
  (Float.cos h, Float.sin h * n.x, Float.sin h * n.y, Float.sin h * n.z)

def inverse (q : Float × Float × Float × Float) : Float × Float × Float × Float :=
  (q.1, -q.2.1, -q.2.2.1, -q.2.2.2)

/-- Inputs that require status 1 or 2, and inputs at the edges of the region. -/
def edges : List Case :=
  [ ("bad1", [], id4),
    ("bad1", [2.5] ++ (input three).drop 1, id4),
    ("bad1", 2.5 :: (input [(ex, ex, 1.0, 0.01), (ey, ey, 1.0, 0.01)]).drop 1, id4),
    ("bad1", input [(ex, ex, 1.0, 0.01)], id4),
    ("bad1", 17.0 :: (input three).drop 1, id4),
    ("bad1", input ((List.range 17).map fun k =>
      if k % 3 == 0 then (ex, ex, 1.0, 0.01) else if k % 3 == 1 then (ey, ey, 1.0, 0.01)
      else (ez, ez, 1.0, 0.01)), id4),
    ("bad1", input three ++ [0.0], id4),
    ("bad1", input [(ex, ex, 1.0, 0.01), (⟨nan, 0.0, 0.0⟩, ey, 1.0, 0.01)], id4),
    ("bad1", input [(ex, ex, 1.0, 0.01), (ey, ⟨0.0, inf, 0.0⟩, 1.0, 0.01)], id4),
    ("bad1", input [(ex, ex, 1.0, 0.01), (ey, ey, 0.0, 0.01)], id4),
    ("bad1", input [(ex, ex, 1.0, 0.01), (ey, ey, -1.0, 0.01)], id4),
    ("bad1", input [(ex, ex, 1.0, 0.01), (ey, ey, 1.0, -0.01)], id4),
    ("bad1", input [(ex, ex, 1.0, 0.01), (ey, ey, 1.0, 1.6)], id4),
    ("bad1", input [(ex, ex, 1.0, 0.01), (ey, ey, 1.0, nan)], id4),
    ("bad1", input [(ex, ex, 1.0, 0.01), (⟨0.0, 0.0, 0.0⟩, ey, 1.0, 0.01)], id4),
    ("bad1", input [(ex, ex, 1.0, 0.01), (ey, ⟨0.0, 0.0, 0.0⟩, 1.0, 0.01)], id4),
    ("bad1", input [(ex.scale 1e200, ex, 1.0, 0.01), (ey, ey, 1.0, 0.01)], id4),
    ("bad1", input [(ex, ex, 1e308, 0.01), (ey, ey, 1e308, 0.01)], id4),
    ("bad2", input [(ex, ex, 1.0, 0.01), (ex, ex, 1.0, 0.01)], id4),
    ("bad2", input [(ex, ex, 1.0, 0.01), (ex.scale 2.0, ex, 1.0, 0.01), (ex, ex, 3.0, 0.0)],
      id4),
    ("bad2", input [(ex, ex, 1.0, 1.4), (ey, ey, 1.0, 1.4)], id4),
    ("bad2", input [(ex, ex, 1.0, 1.2), (ey, ey, 1.0, 1.2), (ez, ez, 1.0, 1.2)], id4),
    ("edge", input [(ex, ex, 1.0, 0.5), (ey, ey, 1.0, 0.5), (ez, ez, 1.0, 0.5)], id4),
    ("edge", input [(ex, ex, 1.0, 0.0), (ey, ey, 1.0, 0.0)], id4),
    ("edge", input three, id4),
    ("edge", input [(ex, ex, 1.0, 0.01), (ey, ey, 1.0, 0.01)], id4),
    ("edge", input [(ex, ex, 1.0, 0.01), (⟨0.0, 0.0, -1.0⟩, ⟨0.0, -1.0, 0.0⟩, 1.0, 0.01)],
      (0.7071067811865476, -0.7071067811865476, 0.0, 0.0)),
    ("edge", input ([ex, ey, ez].map fun r => (rot (inverse turnedFrame) r, r, 1.0, 0.01)),
      turnedFrame) ]

def all : List Case :=
  edges ++ (List.range 180).map (fun i => gen false (2 + i % 15) (emaxOf (i / 15))
      (UInt64.ofNat (7000 + i))) ++
    (List.range 45).map (fun i => gen true (2 + i % 15) (emaxOf (i / 15)) (UInt64.ofNat (9000 + i)))

/-- The index of the largest of the estimates other than the one at `i`. -/
def secondIndex (i : Nat) (d : List Float) : Nat :=
  ((List.range 4).filter (· != i)).foldl (fun b k => if d[k]! > d[b]! then k else b)
    (if i == 0 then 1 else 0)

/-- The result of the certificate for the program's quaternion turned by the angle `δ` toward
the column of the second largest estimate, with the program's cut. -/
def turnedResult (xs : Array Float) (δ : Float) : Array Float :=
  let s := accumulate Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi xs
    (rd xs 0).toUInt64
  let j := jacobi s.k
  let i := top4 j.a00 j.a11 j.a22 j.a33
  let l := pick i j.a00 j.a11 j.a22 j.a33
  let q := normalize (column i j)
  let v := normalize (column (secondIndex i.toNat [j.a00, j.a11, j.a22, j.a33]).toUInt64 j)
  let c := Float.cos δ
  let n := Float.sin δ
  certify Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi s.k s.rho s.mu
    (l.2 + (l.1 - l.2) / 16.0)
    (normalize ⟨c * q.w + n * v.w, c * q.x + n * v.x, c * q.y + n * v.y, c * q.z + n * v.z⟩)

/-- Inputs of class `good` with the program's quaternion turned by `1e-6`, `1e-4`, and `1e-2`. -/
def turnedCases : List (Case × Float) :=
  (List.range 30).map fun i =>
    let (_, xs, q) := gen false (2 + i % 15) (emaxOf (i / 3)) (UInt64.ofNat (11000 + i))
    (("turned", xs, q), if i % 3 == 0 then 1e-6 else if i % 3 == 1 then 1e-4 else 1e-2)

def words (ys : Array Float) : String := " ".intercalate (ys.toList.map fun y => toString y.toBits)

def cases : IO Unit := do
  for (_, xs, _) in all do
    let ys := qmethod xs.toArray
    line "qmethod" "qmethod" "array-u64" [arrF xs]
      s!"[{", ".intercalate (ys.toList.map fun y => toString y.toBits)}]"

def bits : IO Unit := do
  for (cls, xs, (qw, qx, qy, qz)) in all do
    IO.println s!"{cls} {xs.length} {words xs.toArray} {words #[qw, qx, qy, qz]} {words (qmethod xs.toArray)}"
  for ((cls, xs, (qw, qx, qy, qz)), δ) in turnedCases do
    IO.println
      s!"{cls} {xs.length} {words xs.toArray} {words #[qw, qx, qy, qz]} {words (turnedResult xs.toArray δ)}"

end TestSupport.Attitude.QCases
