import Demos.Conjunction.Program
import TestSupport.Host

/-! Cases of the conjunction module.  `cases` prints the module cases of `pc` and `assess` for
`tests/verified/run.sh`, and `bits` prints, for each valid input and each panel count, the bit
patterns `m1 m2 c11 c12 c22 r n status lo hi` that `tests/conjunction/reference.py` checks
against a reference value. -/

namespace TestSupport.Conjunction.Cases

open TestSupport.Host Demos.Conjunction

/-- The mean, the covariance, and the radius of each valid input: isotropic and elongated
covariances, correlations near ±1, a radius far below and far above the standard deviations, a
zero miss vector, and miss distances of 12 and 50 standard deviations. -/
def inputs : List (Float × Float × Float × Float × Float × Float) :=
  [ (0.0, 0.0, 10000.0, 0.0, 10000.0, 10.0),
    (100.0, 50.0, 10000.0, 0.0, 40000.0, 20.0),
    (200.0, -100.0, 250000.0, 120000.0, 90000.0, 15.0),
    (30.0, 30.0, 10000.0, 9990.0, 10000.0, 5.0),
    (30.0, -30.0, 10000.0, -9990.0, 10000.0, 5.0),
    (0.0, 0.0, 1000000.0, 0.0, 1000000.0, 0.01),
    (3.0, 4.0, 100.0, 0.0, 100.0, 10000.0),
    (0.0, 0.0, 1000000.0, 0.0, 1.0, 5.0),
    (0.0, 0.0, 1.0, 0.0, 1000000.0, 5.0),
    (1200.0, 0.0, 10000.0, 0.0, 10000.0, 10.0),
    (0.0, 5000.0, 10000.0, 0.0, 10000.0, 10.0),
    (300.0, 0.0, 10000.0, 0.0, 1000000.0, 20.0),
    (-12.5, 7.25, 30.0, 12.0, 20.0, 6.0) ]

/-- Inputs that the program rejects: a covariance that is not positive definite, a first variance
or a radius that is not positive, nonfinite values, and a radius whose square overflows. -/
def rejected : List (Float × Float × Float × Float × Float × Float) :=
  [ (0.0, 0.0, 1.0, 2.0, 1.0, 1.0),
    (0.0, 0.0, 1.0, 1.0, 1.0, 1.0),
    (0.0, 0.0, 0.0, 0.0, 1.0, 1.0),
    (0.0, 0.0, -1.0, 0.0, 1.0, 1.0),
    (0.0, 0.0, 1.0, 0.0, -1.0, 1.0),
    (0.0, 0.0, 1.0, 0.0, 1.0, 0.0),
    (0.0, 0.0, 1.0, 0.0, 1.0, -1.0),
    (nan, 0.0, 1.0, 0.0, 1.0, 1.0),
    (0.0, inf, 1.0, 0.0, 1.0, 1.0),
    (0.0, 0.0, inf, 0.0, 1.0, 1.0),
    (0.0, 0.0, 1.0, nan, 1.0, 1.0),
    (0.0, 0.0, 1.0, 0.0, 1.0, inf),
    (0.0, 0.0, 1.0, 0.0, 1.0, 1e200) ]

def cases : IO Unit := do
  for (m1, m2, c11, c12, c22, r) in inputs ++ rejected do
    for n in [(0 : UInt64), 1, 16, 256, 1048577] do
      let args := [fl m1, fl m2, fl c11, fl c12, fl c22, fl r]
      let p := pc m1 m2 c11 c12 c22 r n
      line "conjunction" "pc" "list:i64,f64,f64" (args ++ [u n])
        s!"{p.status} {p.lo.toBits} {p.hi.toBits}"
      for t in [1e-4, 0.0, 1.0, 5e-3, nan] do
        let a := assess m1 m2 c11 c12 c22 r t n
        line "conjunction" "assess" "list:i64,f64,f64,i64" (args ++ [fl t, u n])
          s!"{a.status} {a.lo.toBits} {a.hi.toBits} {a.verdict}"

def bits : IO Unit := do
  for (m1, m2, c11, c12, c22, r) in inputs do
    for n in [(16 : UInt64), 256, 4096] do
      let p := pc m1 m2 c11 c12 c22 r n
      IO.println s!"{m1.toBits} {m2.toBits} {c11.toBits} {c12.toBits} {c22.toBits} {r.toBits} {n} {p.status} {p.lo.toBits} {p.hi.toBits}"

end TestSupport.Conjunction.Cases
