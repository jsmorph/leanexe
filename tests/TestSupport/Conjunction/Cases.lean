import Demos.Conjunction.Message
import TestSupport.Host

/-! Cases of the conjunction module.  `cases` prints the module cases of `pc`, `assess`,
`pcMessage`, and `assessMessage` for `tests/verified/run.sh`.  `bits` prints, for each valid input
of `pc` and each panel count, the bit patterns `m1 m2 c11 c12 c22 r n status lo hi` that
`tests/conjunction/reference.py` checks against a reference value.  `messageBits` prints, for each
input of the message form and each panel count, its kind, the bit patterns of the 25 inputs, `n`,
the status, `lo`, and `hi` of `pcMessage`, and the status and endpoints of each interval of
`encounterAt`, which `tests/conjunction/message.py` checks. -/

namespace TestSupport.Conjunction.Cases

open TestSupport.Host Demos.Conjunction Library.Numerics.Interval

/-- The mean, the covariance, and the radius of each valid input: isotropic and elongated
covariances, correlations near ±1, a radius far below and far above the standard deviations, a
zero miss vector, a miss of 12 standard deviations along the first axis and of 12, 30, and 50
along the second, and a correlated covariance with a miss of 11.5 standard deviations in its
metric. -/
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
    (0.0, 1200.0, 10000.0, 0.0, 10000.0, 10.0),
    (0.0, 3000.0, 10000.0, 0.0, 10000.0, 10.0),
    (-400.0, 900.0, 40000.0, -15000.0, 10000.0, 8.0),
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

/-- Inputs of the message form: each object's position in km, velocity in km/s, and position
covariance in m² in its RTN frame, and the radius in m.  The valid inputs hold a crossing and a
head-on encounter in low orbit, a slow encounter in geostationary orbit, an inclined encounter with
correlated covariances, misses of about 12 and 30 standard deviations, and a probability near 1. -/
def messages : List (List Float × Float) :=
  [ ([7000.0, 0.0, 0.0, 0.0, 7.546, 0.0, 1e4, 0.0, 1e6, 0.0, 0.0, 2500.0,
      7000.2, 0.1, 0.1, 0.0, 0.0, 7.546, 2e4, 1e3, 4e6, 0.0, 0.0, 1e4], 20.0),
    ([6800.0, 0.0, 0.0, 0.0, 7.656, 0.0, 2500.0, 300.0, 90000.0, 0.0, 0.0, 900.0,
      6800.05, 0.02, 0.12, 0.0, -7.656, 0.01, 1e4, -5e3, 1e6, 100.0, 0.0, 2500.0], 10.0),
    ([42164.0, 0.0, 0.0, 0.0, 3.0747, 0.0, 1e4, 0.0, 1e7, 0.0, 0.0, 1e4,
      42164.3, 1.5, 0.2, -0.0002, 3.0745, 0.002, 4e4, 0.0, 4e7, 0.0, 0.0, 4e4], 30.0),
    ([-2563.2, 5824.7, 2781.9, -5.4182, -3.6417, 2.6432, 400.0, 150.0, 25000.0, -30.0, 200.0,
      900.0, -2563.0, 5824.5, 2782.3, 1.0571, 2.3184, -6.902, 900.0, -400.0, 160000.0, 50.0,
      -1000.0, 1600.0], 15.0),
    ([7000.0, 0.0, 0.0, 0.0, 7.546, 0.0, 100.0, 0.0, 400.0, 0.0, 0.0, 100.0,
      7000.15, 0.05, 0.05, 0.0, 0.0, 7.546, 100.0, 0.0, 400.0, 0.0, 0.0, 100.0], 5.0),
    ([7000.0, 0.0, 0.0, 0.0, 7.546, 0.0, 25.0, 0.0, 100.0, 0.0, 0.0, 25.0,
      7000.2, 0.1, 0.1, 0.0, 0.0, 7.546, 25.0, 0.0, 100.0, 0.0, 0.0, 25.0], 10.0),
    ([7000.0, 0.0, 0.0, 0.0, 7.546, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 1.0,
      7000.0005, 0.0, 0.0, 0.0, 0.0, 7.546, 1.0, 0.0, 1.0, 0.0, 0.0, 1.0], 20.0) ]

/-- Inputs of the message form that the program rejects: a position at the origin, a velocity
along the position, equal velocities, a relative position along the relative velocity, equal
positions, a covariance that is not positive definite, zero covariances, nonfinite values, and a
radius that is zero, negative, or infinite. -/
def rejectedMessages : List (List Float × Float) :=
  let a := [7000.0, 0.0, 0.0, 0.0, 7.546, 0.0, 1e4, 0.0, 1e6, 0.0, 0.0, 2500.0]
  let b := [7000.2, 0.1, 0.1, 0.0, 0.0, 7.546, 2e4, 1e3, 4e6, 0.0, 0.0, 1e4]
  [ ([0.0, 0.0, 0.0, 0.0, 7.546, 0.0, 1e4, 0.0, 1e6, 0.0, 0.0, 2500.0] ++ b, 20.0),
    ([7000.0, 0.0, 0.0, 7.546, 0.0, 0.0, 1e4, 0.0, 1e6, 0.0, 0.0, 2500.0] ++ b, 20.0),
    (a ++ [7000.2, 0.1, 0.1, 0.0, 7.546, 0.0, 2e4, 1e3, 4e6, 0.0, 0.0, 1e4], 20.0),
    (a ++ [7000.0, 0.1, 0.0, 0.0, 7.6, 0.0, 2e4, 1e3, 4e6, 0.0, 0.0, 1e4], 20.0),
    (a ++ [7000.0, 0.0, 0.0, 0.0, 0.0, 7.546, 2e4, 1e3, 4e6, 0.0, 0.0, 1e4], 20.0),
    ([7000.0, 0.0, 0.0, 0.0, 7.546, 0.0, -1e4, 0.0, -1e6, 0.0, 0.0, -2500.0,
      7000.2, 0.1, 0.1, 0.0, 0.0, 7.546, -2e4, 0.0, -4e6, 0.0, 0.0, -1e4], 20.0),
    ([7000.0, 0.0, 0.0, 0.0, 7.546, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0,
      7000.2, 0.1, 0.1, 0.0, 0.0, 7.546, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0], 20.0),
    ([nan, 0.0, 0.0, 0.0, 7.546, 0.0, 1e4, 0.0, 1e6, 0.0, 0.0, 2500.0] ++ b, 20.0),
    (a ++ [7000.2, 0.1, 0.1, 0.0, 0.0, 7.546, inf, 1e3, 4e6, 0.0, 0.0, 1e4], 20.0),
    (a ++ b, 0.0),
    (a ++ b, -1.0),
    (a ++ b, inf) ]

def messagePc (xs : List Float) (r : Float) (n : UInt64) : Interval :=
  pcMessage xs[0]! xs[1]! xs[2]! xs[3]! xs[4]! xs[5]! xs[6]! xs[7]! xs[8]! xs[9]! xs[10]!
    xs[11]! xs[12]! xs[13]! xs[14]! xs[15]! xs[16]! xs[17]! xs[18]! xs[19]! xs[20]! xs[21]!
    xs[22]! xs[23]! r n

def messageAssess (xs : List Float) (r t : Float) (n : UInt64) : Assessment :=
  assessMessage xs[0]! xs[1]! xs[2]! xs[3]! xs[4]! xs[5]! xs[6]! xs[7]! xs[8]! xs[9]! xs[10]!
    xs[11]! xs[12]! xs[13]! xs[14]! xs[15]! xs[16]! xs[17]! xs[18]! xs[19]! xs[20]! xs[21]!
    xs[22]! xs[23]! r t n

def messagePlane (xs : List Float) : Interval × Interval × Interval × Interval × Interval :=
  encounterAt Library.Numerics.Float64.Exp.expTable xs[0]! xs[1]! xs[2]! xs[3]! xs[4]! xs[5]!
    xs[6]! xs[7]! xs[8]! xs[9]! xs[10]! xs[11]! xs[12]! xs[13]! xs[14]! xs[15]! xs[16]! xs[17]!
    xs[18]! xs[19]! xs[20]! xs[21]! xs[22]! xs[23]!

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
  for (xs, r) in messages ++ rejectedMessages do
    for n in [(0 : UInt64), 1, 16, 256] do
      let args := xs.map fl ++ [fl r]
      let p := messagePc xs r n
      line "conjunction" "pcMessage" "list:i64,f64,f64" (args ++ [u n])
        s!"{p.status} {p.lo.toBits} {p.hi.toBits}"
      for t in [1e-4, 1e-7, nan] do
        let a := messageAssess xs r t n
        line "conjunction" "assessMessage" "list:i64,f64,f64,i64" (args ++ [fl t, u n])
          s!"{a.status} {a.lo.toBits} {a.hi.toBits} {a.verdict}"

def bits : IO Unit := do
  for (m1, m2, c11, c12, c22, r) in inputs do
    for n in [(16 : UInt64), 256, 4096] do
      let p := pc m1 m2 c11 c12 c22 r n
      IO.println s!"{m1.toBits} {m2.toBits} {c11.toBits} {c12.toBits} {c22.toBits} {r.toBits} {n} {p.status} {p.lo.toBits} {p.hi.toBits}"

def interval (i : Interval) : String := s!"{i.status} {i.lo.toBits} {i.hi.toBits}"

def messageBits : IO Unit := do
  let kinds := messages.map (fun m => ("valid", m)) ++
    rejectedMessages.map (fun m => ("rejected", m))
  for (kind, xs, r) in kinds do
    for n in [(16 : UInt64), 256, 4096] do
      let p := messagePc xs r n
      let e := messagePlane xs
      let inputs := " ".intercalate ((xs ++ [r]).map fun x => toString x.toBits)
      let plane := [e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2].map interval
      IO.println s!"{kind} {inputs} {n} {interval p} {" ".intercalate plane}"

end TestSupport.Conjunction.Cases
