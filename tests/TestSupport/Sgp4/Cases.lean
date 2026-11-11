import Demos.Sgp4.Program
import TestSupport.Host

/-! Cases of the SGP4 module.  `cases` prints the module cases of `init`, `propagate`, and `sgp4`
for `tests/verified/run.sh`.  `states` reads lines of the bit patterns
`n e incl node argp m bstar t` and prints the status and the bit patterns of the state that
`sgp4` returns, for `tests/sgp4/reference.py`. -/

namespace TestSupport.Sgp4.Cases

open TestSupport.Host Demos.Sgp4

/-- Element sets as `n e incl node argp m bstar`: sets of the verification file of Vallado,
Crawford, Hujsak, and Kelso with a perigee above 220 km, below 220 km, below 156 km, and below
98 km, an eccentricity below `1e-4`, an inclination of 180 degrees, a deep-space set, and sets
outside the accepted ranges. -/
def elements : List (Float × Float × Float × Float × Float × Float × Float) :=
  [ (10.82419157, 0.1859667, 34.2682, 348.7242, 331.7664, 19.3264, 0.28098e-4),
    (15.56387291, 0.0030035, 58.0579, 54.0425, 139.1568, 221.1854, 0.12808e-3),
    (16.47856722, 0.0002297, 37.7696, 307.2061, 91.8041, 268.3045, 0.14802e-3),
    (16.46015938, 0.0007215, 96.4736, 123.7657, 8.7630, 351.3706, 0.14784e-3),
    (15.93343074, 0.0005270, 51.6230, 222.5750, 293.4627, 66.6020, 0.50112e-2),
    (14.35478080, 0.00005, 98.4283, 247.6961, 85.6398, 274.4891, 0.35940e-4),
    (14.5, 0.001, 180.0, 10.0, 20.0, 30.0, 0.1e-3),
    (2.00491383, 0.6877146, 64.1586, 279.0717, 264.7651, 20.2257, 0.21906e-4),
    (0.0, 0.1, 10.0, 20.0, 30.0, 40.0, 0.0),
    (15.0, 1.0, 10.0, 20.0, 30.0, 40.0, 0.0),
    (15.0, -0.1, 10.0, 20.0, 30.0, 40.0, 0.0),
    (nan, 0.1, 10.0, 20.0, 30.0, 40.0, 0.0),
    (15.0, 0.1, inf, 20.0, 30.0, 40.0, 0.0) ]

def times : List Float := [0.0, 120.0, -360.0, 1440.0, 14400.0, 1.0e7, nan]

def constsList (c : Consts) : List String :=
  [u c.status, u c.isimp] ++ ([c.no, c.ecco, c.inclo, c.nodeo, c.argpo, c.mo, c.bstar, c.sinio,
    c.cosio, c.con41, c.x1mth2, c.x7thm1, c.mdot, c.argpdot, c.nodedot, c.nodecf, c.cc1, c.cc4,
    c.cc5, c.t2cof, c.omgcof, c.eta, c.xmcof, c.delmo, c.sinmao, c.d2, c.d3, c.d4, c.t3cof,
    c.t4cof, c.t5cof, c.aycof, c.xlcof].map fl)

def stateText (s : State) : String :=
  s!"{s.status} {s.x.toBits} {s.y.toBits} {s.z.toBits} {s.vx.toBits} {s.vy.toBits} {s.vz.toBits}"

def stateKind : String := "list:i64,f64,f64,f64,f64,f64,f64"

def constsKind : String :=
  "list:i64,i64," ++ ",".intercalate (List.replicate 33 "f64")

def cases : IO Unit := do
  for (n, e, incl, node, argp, m, bstar) in elements do
    let args := [fl n, fl e, fl incl, fl node, fl argp, fl m, fl bstar]
    let c := init n e incl node argp m bstar
    let words := (constsList c).map fun s => (s.splitOn ":")[1]!
    line "sgp4" "init" constsKind args (" ".intercalate words)
    for t in times do
      line "sgp4" "propagate" stateKind (constsList c ++ [fl t]) (stateText (propagate c t))
      line "sgp4" "sgp4" stateKind (args ++ [fl t]) (stateText (sgp4 n e incl node argp m bstar t))

partial def states : IO Unit := do
  let stdin ← IO.getStdin
  let rec go : IO Unit := do
    let text ← stdin.getLine
    if text.isEmpty then return
    let words := (text.trim.splitOn " ").filterMap String.toNat?
    match words.map fun w => Float.ofBits (UInt64.ofNat w) with
    | [n, e, incl, node, argp, m, bstar, t] =>
      IO.println (stateText (sgp4 n e incl node argp m bstar t))
    | _ => throw (IO.userError s!"expected eight words: {text}")
    go
  go

end TestSupport.Sgp4.Cases
