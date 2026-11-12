import Demos.Gate.GateProgram
import TestSupport.Host

/-! Cases of the export `gate`.  `covariance d c seed` builds a symmetric `d × d` matrix
`H diag(λ) H` from a Householder reflection `H = I - 2vv'/(v'v)` of a vector `v` drawn from a
linear congruential generator and eigenvalues `λ` spread geometrically from 1 to `1/c`, computed
in binary64 with each entry below the diagonal copied from the one above it.  `calls` gives
covariances of dimensions 1 to 6, 10, 32, and 64 with condition numbers from 1 to `1e12`, a
correlation of `1 - 1e-12`, matrices with a negative or a zero eigenvalue, asymmetric and
nonfinite matrices, an asymmetry between entries that are not adjacent, wrong sizes, an
innovation whose distance overflows, innovations scaled so that the squared Mahalanobis distance
lies inside, outside, and at the threshold, and thresholds equal to the ends of an earlier
result's interval.  `cases` prints the module cases, and `bits` prints
one line per call for `tests/gate/gate.py`: `gate d nu s g status lo hi verdict`, with
the arrays as comma-separated bit patterns. -/

namespace TestSupport.Gate.GateCases

open TestSupport.Host Demos.Gate

def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A value in `[-1, 1)` from a state of the generator. -/
def unit (s : Nat) : Float := (s / 2 ^ 11).toUInt64.toFloat / 9007199254740992.0 * 2.0 - 1.0

def vector (d seed : Nat) : Array Float := Id.run do
  let mut s := next (seed + 17)
  let mut v : Array Float := #[]
  for _ in [0:d] do
    s := next s
    v := v.push (unit s)
  return v

/-- `H diag(λ) H` with `λ_i = c^(-i/(d-1))`, or the eigenvalues `lams` when they are given. -/
def covariance (d : Nat) (lams : Array Float) (seed : Nat) : Array Float := Id.run do
  let v := vector d seed
  let vv := v.foldl (fun a x => a + x * x) 0.0
  let h := fun i j => (if i == j then 1.0 else 0.0) - 2.0 * v[i]! * v[j]! / vv
  let mut s : Array Float := Array.replicate (d * d) 0.0
  for i in [0:d] do
    for j in [i:d] do
      let mut x := 0.0
      for m in [0:d] do
        x := x + h i m * lams[m]! * h m j
      s := (s.set! (i * d + j) x).set! (j * d + i) x
  return s

def spread (d : Nat) (c : Float) : Array Float :=
  (Array.range d).map fun i =>
    if d == 1 then 1.0 else Float.pow c (-(i.toUInt64.toFloat) / (d - 1).toUInt64.toFloat)

/-- The innovation `scale · v` for a vector `v` of the generator. -/
def innovation (d seed : Nat) (scale : Float) : Array Float :=
  (vector d (seed + 1000)).map (· * scale)

structure Call where
  nu : Array Float
  s : Array Float
  g : Float

def calls : List Call :=
  let dims := [1, 2, 3, 4, 5, 6, 10, 32, 64]
  let conds : List Float := [1.0, 100.0, 1e6, 1e12]
  let regular := dims.flatMap fun d => conds.flatMap fun c =>
    let s := covariance d (spread d c) (d * 7 + 3)
    [0.1, 1.0, 3.0, 30.0].flatMap fun scale =>
      [9.21, 16.81].map fun g => ⟨innovation d (d + 5) scale, s, g⟩
  let negative := [2, 3, 6, 32].map fun d =>
    ⟨innovation d d 1.0, covariance d ((spread d 10.0).set! (d - 1) (-0.5)) d, 9.21⟩
  let singular := [2, 3, 6, 32].map fun d =>
    ⟨innovation d d 1.0, covariance d ((spread d 10.0).set! (d - 1) 0.0) d, 9.21⟩
  let correlated : List Call :=
    [⟨#[1.0, -1.0], #[1.0, 1.0 - 1e-12, 1.0 - 1e-12, 1.0], 9.21⟩,
     ⟨#[1.0, 1.0], #[1.0, 1.0 - 1e-12, 1.0 - 1e-12, 1.0], 9.21⟩,
     ⟨#[1e-6, -1e-6], #[1.0, 1.0 - 1e-12, 1.0 - 1e-12, 1.0], 9.21⟩]
  let edges : List Call := [2, 3, 6].flatMap fun d =>
    let s := covariance d (spread d 100.0) (d * 7 + 3)
    let nu := innovation d (d + 5) 1.0
    let r := gate nu s 9.21
    [⟨nu, s, r.hi⟩, ⟨nu, s, r.lo⟩]
  let boundary : List Call :=
    [⟨#[3.0], #[1.0], 9.0⟩, ⟨#[3.0, 4.0], #[1.0, 0.0, 0.0, 1.0], 25.0⟩,
     ⟨#[0.0, 0.0, 0.0], #[1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0], 0.0⟩,
     ⟨#[0.0, 0.0], #[1.0, 0.0, 0.0, 1.0], 0.0⟩, ⟨#[0.0], #[2.0], 0.0⟩,
     ⟨#[1.0], #[1.0], 1e-323⟩]
  let rejected : List Call :=
    [⟨#[], #[], 9.21⟩, ⟨#[1.0, 2.0], #[1.0, 0.0, 0.0], 9.21⟩,
     ⟨#[1.0, 2.0], #[1.0, 0.5, 0.25, 1.0], 9.21⟩, ⟨#[1.0, nan], #[1.0, 0.0, 0.0, 1.0], 9.21⟩,
     ⟨#[1.0, 2.0], #[1.0, 0.0, 0.0, inf], 9.21⟩, ⟨#[1.0], #[1.0], -1.0⟩, ⟨#[1.0], #[1.0], nan⟩,
     ⟨#[1.0], #[1.0], inf⟩, ⟨#[1.0], #[0.0], 9.21⟩, ⟨#[1.0], #[-1.0], 9.21⟩,
     ⟨(Array.replicate 65 1.0), covariance 65 (spread 65 1.0) 1, 9.21⟩,
     ⟨#[1.0, 2.0, 3.0], #[1.0, 0.0, 0.5, 0.0, 1.0, 0.0, 0.25, 0.0, 1.0], 9.21⟩,
     ⟨#[1e200, 0.0], #[1.0, 0.0, 0.0, 1.0], 9.21⟩, ⟨#[1.0], #[1e-320], 9.21⟩]
  regular ++ negative ++ singular ++ correlated ++ edges ++ boundary ++ rejected

def result (r : Gate) : String :=
  s!"{r.status} {r.lo.toBits} {r.hi.toBits} {r.verdict}"

def cases : IO Unit := do
  for c in calls do
    line "gate" "gate" "list:i64,f64,f64,i64" [arrF c.nu.toList, arrF c.s.toList, fl c.g]
      (result (gate c.nu c.s c.g))

def bitsOf (xs : Array Float) : String := ",".intercalate (xs.toList.map fun x => toString x.toBits)

def bits : IO Unit := do
  for c in calls do
    IO.println s!"gate {c.nu.size} {bitsOf c.nu} {bitsOf c.s} {c.g.toBits} {result (gate c.nu c.s c.g)}"

end TestSupport.Gate.GateCases
