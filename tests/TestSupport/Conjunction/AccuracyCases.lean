import Demos.Conjunction.Accuracy
import TestSupport.Host

/-! Cases of the accuracy module.  `cases` prints the module cases of `circularError` and
`linearError` for `tests/verified/run.sh`, and `bits` prints the bit patterns of the inputs and
results that `tests/conjunction/accuracy.py` checks against reference radii: one line
`circular m1 m2 c11 c12 c22 p n k status lo hi` or `linear b v p k status lo hi` per call. -/

namespace TestSupport.Conjunction.AccuracyCases

open TestSupport.Host Demos.Conjunction.Accuracy

/-- Means and covariances of the circular error: isotropic, elongated with either axis of larger
variance, rotated with eigenvalues 10,000 and 1 at 45°, 30°, 10°, and 60°, a correlation of 0.99,
biases of 1 and 3 standard deviations, and an input and its exchange of axes, which detects an
exchange that negates `c12`. -/
def disks : List (Float × Float × Float × Float × Float) :=
  [ (0, 0, 1, 0, 1),
    (0, 0, 1, 0, 9), (0, 0, 9, 0, 1),
    (0, 0, 1, 0, 100), (0, 0, 100, 0, 1),
    (0, 0, 1, 0, 10000), (0, 0, 10000, 0, 1),
    (0, 0, 5000.5, 4999.5, 5000.5),
    (0, 0, 7500.25, 4329.6940062203, 2500.75),
    (0, 0, 9698.49325761915, 1709.9297065566807, 302.506742380851),
    (0, 0, 2500.75, 4329.6940062203, 7500.25),
    (0, 0, 1, 0.99, 1),
    (1, 0, 1, 0, 1), (3, 0, 1, 0, 1),
    (0, 3, 1, 0, 100), (3, 0, 100, 0, 1),
    (2, -1, 25, 6, 16), (-1, 2, 16, 6, 25) ]

/-- Means and variances of the linear error, among them a negative bias, a variance of `1e-6`,
and a variance of `1e6` with a bias of one standard deviation. -/
def normals : List (Float × Float) :=
  [(0, 1), (1, 1), (3, 4), (0.5, 0.25), (-2, 1), (0, 1e-6), (1000, 1e6)]

def probabilities : List Float := [1e-6, 0.5, 0.9, 0.95, 0.99]

/-- Inputs that `circularError` rejects. -/
def diskRejected : List (Float × Float × Float × Float × Float × Float × UInt64 × UInt64) :=
  [ (nan, 0, 1, 0, 1, 0.9, 16, 4), (0, inf, 1, 0, 1, 0.9, 16, 4), (0, 0, 1, nan, 1, 0.9, 16, 4),
    (0, 0, 1, 0, 1, nan, 16, 4), (0, 0, 1, 0, 1, 0, 16, 4), (0, 0, 1, 0, 1, 1, 16, 4),
    (0, 0, 1, 0, 1, -0.5, 16, 4), (0, 0, 0, 0, 1, 0.9, 16, 4), (0, 0, 1, 0, 0, 0.9, 16, 4),
    (0, 0, -1, 0, 1, 0.9, 16, 4), (0, 0, 1, 2, 1, 0.9, 16, 4), (0, 0, 1, 1, 1, 0.9, 16, 4),
    (0, 0, 4, 2, 1, 0.9, 16, 4), (0, 0, 1, 0, 1, 0.9, 0, 4), (0, 0, 1, 0, 1, 0.9, 1048577, 4),
    (0, 0, 1, 0, 1, 0.9, 16, 65) ]

/-- Inputs whose search ends with status 2: probabilities too close to 1 for the panels, and one
or two panels, whose enclosures at every radius have the lower endpoint 0. -/
def diskUnfinished : List (Float × Float × Float × Float × Float × Float × UInt64 × UInt64) :=
  [ (0, 0, 1, 0, 1, 0.9999999, 16, 4), (0, 0, 1, 0, 1, 0.999999, 256, 4),
    (0, 0, 1, 0, 1, 0.99, 256, 4), (0, 0, 1, 0, 1, 0.5, 1, 4), (0, 0, 1, 0, 1, 0.5, 2, 4) ]

/-- Inputs that `linearError` rejects, and one whose search ends with status 2. -/
def lineOthers : List (Float × Float × Float × UInt64) :=
  [ (nan, 1, 0.9, 10), (0, inf, 0.9, 10), (0, 1, nan, 10), (0, 0, 0.9, 10), (0, -1, 0.9, 10),
    (0, 1, 0, 10), (0, 1, 1, 10), (0, 1, 0.9, 65), (0, 1, 0.9999999999999999, 10) ]

def diskLine (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) : IO Unit :=
  let r := circularError m1 m2 c11 c12 c22 p n k
  line "accuracy" "circularError" "list:i64,f64,f64"
    [fl m1, fl m2, fl c11, fl c12, fl c22, fl p, u n, u k]
    s!"{r.status} {r.lo.toBits} {r.hi.toBits}"

def lineLine (b v p : Float) (k : UInt64) : IO Unit :=
  let r := linearError b v p k
  line "accuracy" "linearError" "list:i64,f64,f64" [fl b, fl v, fl p, u k]
    s!"{r.status} {r.lo.toBits} {r.hi.toBits}"

def cases : IO Unit := do
  for (m1, m2, c11, c12, c22) in disks do
    for p in [0.9, 0.99] do
      for n in [(16 : UInt64), 256] do
        for k in [(0 : UInt64), 20] do
          diskLine m1 m2 c11 c12 c22 p n k
  for (m1, m2, c11, c12, c22, p, n, k) in diskRejected ++ diskUnfinished do
    diskLine m1 m2 c11 c12 c22 p n k
  for (b, v) in normals do
    for p in [1e-6, 0.9, 0.99] do
      for k in [(0 : UInt64), 10, 64] do
        lineLine b v p k
  for (b, v, p, k) in lineOthers do
    lineLine b v p k

def diskBits (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) : IO Unit := do
  let r := circularError m1 m2 c11 c12 c22 p n k
  IO.println s!"circular {m1.toBits} {m2.toBits} {c11.toBits} {c12.toBits} {c22.toBits} {p.toBits} {n} {k} {r.status} {r.lo.toBits} {r.hi.toBits}"

def bits : IO Unit := do
  for (m1, m2, c11, c12, c22) in disks do
    for p in probabilities do
      for n in (if p == 0.99 then [(4096 : UInt64), 65536] else [256, 4096, 65536]) do
        diskBits m1 m2 c11 c12 c22 p n 30
  for (m1, m2, c11, c12, c22, p, n, k) in diskUnfinished do
    diskBits m1 m2 c11 c12 c22 p n k
  for (b, v) in normals do
    for p in probabilities do
      let r := linearError b v p 64
      IO.println s!"linear {b.toBits} {v.toBits} {p.toBits} 64 {r.status} {r.lo.toBits} {r.hi.toBits}"

end TestSupport.Conjunction.AccuracyCases
