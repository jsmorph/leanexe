import Demos.Gate.Program
import TestSupport.Host

/-! Cases of the module `chisquare`.  `cases` prints the module cases of `tail`, `cdf`, and
`quantile` for `tests/verified/run.sh`, and `bits` prints the bit patterns of the inputs and results that
`tests/gate/distribution.py` checks against mpmath: one line `tail k x status lo hi`,
`cdf k x status lo hi`, or `quantile k p h status lo hi` per call. -/

namespace TestSupport.Gate.ChiSquareCases

open TestSupport.Host Demos.Gate

def degrees : List UInt64 := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 30, 64, 100, 999, 1000]

/-- Points from the negative ones through zero, the smallest subnormal, the quantiles of common
gates, and the region where `exp(-x/2)` underflows, from about 1,490, to the largest values. -/
def points : List Float :=
  [-1, -0.0, 0, 5e-324, 1e-300, 1e-12, 0.1, 0.5, 1, 2, 3.84, 6.63, 9.21, 16.8, 30, 50, 100, 300,
    1000, 1200, 1480, 1500, 1600, 3000, 1e6, 1e300]

def probabilities : List Float :=
  [1e-300, 1e-100, 1e-12, 1e-6, 0.001, 0.05, 0.5, 0.9, 0.95, 0.99, 0.997, 0.9999, 0.999999,
    0.9999999999999999]

/-- Inputs that `tail` and `cdf` reject. -/
def rejected : List (UInt64 × Float) :=
  [(0, 1), (1001, 1), (maxU, 1), (1, nan), (1, inf), (1, -inf)]

/-- Inputs that `quantile` rejects, and a subnormal `p`, which it accepts. -/
def quantileOthers : List (UInt64 × Float × UInt64) :=
  [(0, 0.5, 64), (1001, 0.5, 64), (1, 0, 64), (1, 1, 64), (1, -0.5, 64), (1, nan, 64),
    (1, inf, 64), (1, 0.5, 65), (2, 1e-320, 64)]

def interval (r : Library.Numerics.Interval.Interval) : String :=
  s!"{r.status} {r.lo.toBits} {r.hi.toBits}"

def cases : IO Unit := do
  for k in degrees do
    for x in points do
      line "chisquare" "tail" "list:i64,f64,f64" [u k, fl x] (interval (tail k x))
      line "chisquare" "cdf" "list:i64,f64,f64" [u k, fl x] (interval (cdf k x))
    for p in probabilities do
      for h in [(0 : UInt64), 64] do
        let q := quantile k p h
        line "chisquare" "quantile" "list:i64,f64,f64" [u k, fl p, u h]
          s!"{q.status} {q.lo.toBits} {q.hi.toBits}"
  for (k, x) in rejected do
    line "chisquare" "tail" "list:i64,f64,f64" [u k, fl x] (interval (tail k x))
    line "chisquare" "cdf" "list:i64,f64,f64" [u k, fl x] (interval (cdf k x))
  for (k, p, h) in quantileOthers do
    let q := quantile k p h
    line "chisquare" "quantile" "list:i64,f64,f64" [u k, fl p, u h]
      s!"{q.status} {q.lo.toBits} {q.hi.toBits}"

def bits : IO Unit := do
  for k in degrees do
    for x in points do
      IO.println s!"tail {k} {x.toBits} {interval (tail k x)}"
      IO.println s!"cdf {k} {x.toBits} {interval (cdf k x)}"
    for p in probabilities do
      let q := quantile k p 64
      IO.println s!"quantile {k} {p.toBits} 64 {q.status} {q.lo.toBits} {q.hi.toBits}"
  for (k, x) in rejected do
    IO.println s!"tail {k} {x.toBits} {interval (tail k x)}"
    IO.println s!"cdf {k} {x.toBits} {interval (cdf k x)}"
  for (k, p, h) in quantileOthers do
    let q := quantile k p h
    IO.println s!"quantile {k} {p.toBits} {h} {q.status} {q.lo.toBits} {q.hi.toBits}"

end TestSupport.Gate.ChiSquareCases
