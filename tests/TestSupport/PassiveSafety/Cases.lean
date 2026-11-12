import Demos.PassiveSafety.Program
import TestSupport.Host

/-! Cases of the passive-safety module.  `cases` prints the module cases of `check` for
`tests/verified/run.sh`, and `bits` prints, for each case, its name, its expected status and
scenario, the bit patterns of its input, its fuel, the bit pattern of its accuracy, and its
result, which `tests/passivesafety/reference.py` checks against numerical integration.  Lengths
are in meters, times in seconds, and velocities in meters per second.  The cases from `formation`
to `genericM` follow the review of the requirements, with the chief's mean motion 0.0011 rad/s.
The cases from `vbarLateBurn` to `hopShortCap` follow the review of the accuracy: plans that
detect wrong Taylor forms, and fuel about 10% above the panels that one search of the method
evaluates, which a costlier enclosure exceeds.
-/

namespace TestSupport.PassiveSafety.Cases

open TestSupport.Host Demos.PassiveSafety

def piF : Float := 3.141592653589793

/-- The mean motion of a chief in a circular orbit of period 5,554 s, about 400 km high. -/
def leo : Float := 0.0011313

/-- The mean motion of a geostationary chief. -/
def geo : Float := 7.2921e-5

/-- The mean motion of the review's cases, with period `orb` and half period `half`. -/
def nr : Float := 0.0011
def orb : Float := 2.0 * piF / nr
def half : Float := piF / nr

/-- The input of a plan: the header, the box `[c − e, c + e]` of initial states with the error
`ep` of the position and `ev` of the velocity, and the burns `(t, Δv)` with the error `ed` of each
velocity change. -/
def plan (n T dmin drc : Float) (c : List Float) (burns : List (Float × List Float))
    (ep ev ed : Float) : List Float :=
  let e := [ep, ep, ep, ev, ev, ev]
  [n, T, dmin, drc] ++ ((c.zip e).map fun (x, d) => [x - d, x + d]).flatten ++
    (burns.map fun (t, dv) => [t] ++ (dv.map fun v => [v - ed, v + ed]).flatten).flatten

/-- A safety ellipse: radial amplitude `a`, along-track amplitude `2a`, and cross-track amplitude
`a` in quadrature with the radial motion, so that the radial and cross-track distance is `a`. -/
def ellipse (n a : Float) : List Float := [a, 0.0, 0.0, 0.0, -2.0 * n * a, n * a]

/-- The speed of a tangential burn that moves the deputy by `d` along the track in one orbit. -/
def hopSpeed (n d : Float) : Float := d * n / (6.0 * piF)

/-- A tangential hop from `-200` m toward the chief by 100 m in one orbit, stopped by a second
burn one period later. -/
def hop (T : Float) : List Float :=
  let v := hopSpeed leo 100.0
  plan leo T 50.0 0.0 [0.0, -200.0, 0.0, 0.0, 0.0, 0.0]
    [(0.0, [0.0, -v, 0.0]), (2.0 * piF / leo, [0.0, v, 0.0])] 0.0 0.0 0.0

/-- A radial hop along the track from `-200` m to `-100` m in half an orbit, stopped by a second
radial burn, over `k` orbits with the error `ep` of the radial position. -/
def radialHop (k ep : Float) : List Float :=
  let v := leo * 100.0 / 4.0
  plan leo (k * 2.0 * piF / leo) 50.0 0.0 [0.0, -200.0, 0.0, 0.0, 0.0, 0.0]
    [(0.0, [-v, 0.0, 0.0]), (piF / leo, [-v, 0.0, 0.0])] ep 0.00001 0.00001

def drift : List Float := [-30.0, -1500.0, 0.0, 0.0, 0.0495, 0.0275]
def bounded : List Float := [-30.0, -1000.0, 0.0, 0.0, 0.066, 0.0275]
def kS : List Float := [48.8, 12.26, 49.27, -0.0257, -0.1163, -0.01866]
def kBurns : List (Float × List Float) :=
  [(1737.8, [-0.02707, 0.02995, 0.009142]), (2490.0, [-0.01593, -0.003903, 0.02845])]
def lS : List Float := [63.63, -86.08, 55.08, -0.000837, -0.1364, -0.07027]
def lBurns : List (Float × List Float) :=
  [(2158.0, [0.02278, -0.02615, 0.01075]), (3814.5, [0.02221, -0.01636, 0.02373])]
def mS : List Float := [-3.282, -146.2, 73.36, -0.01175, -0.002761, -0.01277]
def mBurns : List (Float × List Float) :=
  [(2374.6, [0.02542, -0.01036, 0.02933]), (6684.1, [-0.01874, 0.01940, -0.02056])]

/-- Plans of the review's random search, rounded to six digits: point states, two burns, and
thresholds just below the minima. -/
def random1 : List Float :=
  [0.0011313, 14487.3, 332.662, 172.871, -176.691, -176.691, 279.478, 279.478, -274.765,
    -274.765, 0.17554, 0.17554, 0.0470248, 0.0470248, -0.170778, -0.170778, 592.993, 0.0519049,
    0.0519049, 0.145329, 0.145329, 0.103949, 0.103949, 1543.46, -0.091259, -0.091259, -0.146867,
    -0.146867, -0.111671, -0.111671]
def random2 : List Float :=
  [0.0011, 14710.9, 111.981, 27.7956, -71.7072, -71.7072, 73.3923, 73.3923, 111.243, 111.243,
    0.256329, 0.256329, 0.037368, 0.037368, 0.0581982, 0.0581982, 3677.71, 0.169521, 0.169521,
    0.0141615, 0.0141615, 0.240531, 0.240531, 5516.73, -0.0298166, -0.0298166, -0.171608,
    -0.171608, -0.165379, -0.165379]
def random34 : List Float :=
  [0.0011313, 7883.23, 155.269, 0.951014, 9.09174, 9.09174, -160.901, -160.901, -9.47473,
    -9.47473, 0.292275, 0.292275, 0.143942, 0.143942, -0.24893, -0.24893, 5912.42, -0.071723,
    -0.071723, 0.067435, 0.067435, 0.0708969, 0.0708969, 7229.63, 0.0903422, 0.0903422,
    -0.0633822, -0.0633822, 0.182352, 0.182352]

/-- A valid input for the cases of statuses 1 and 2. -/
def base (T dmin drc : Float) : List Float :=
  plan leo T dmin drc (ellipse leo 100.0) [] 1.0 0.0 0.0

/-- Each case: its name, its input, its fuel, its accuracy, and its expected status and
scenario. -/
def all : List (String × List Float × UInt64 × Float × UInt64 × UInt64) :=
  [ ("ellipse", plan leo 86400.0 50.0 50.0 (ellipse leo 100.0) [] 1.0 0.0001 0.0, 100000, 0.1,
      0, 0),
    ("ellipseCoarse", plan leo 86400.0 50.0 50.0 (ellipse leo 100.0) [] 1.0 0.0001 0.0, 100000,
      1e300, 0, 0),
    ("ellipseFine", plan leo 86400.0 50.0 50.0 (ellipse leo 100.0) [] 1.0 0.0001 0.0, 100000,
      0.01, 0, 0),
    ("accZero", plan nr (2.0 * orb) 80.0 80.0 [100.0, 0.0, 0.0, 0.0, -0.22, 0.22] [] 1.0 1e-4 0.0,
      100000, 0.0, 5, 0),
    ("accNegative", base 100.0 0.0 0.0, 100, -1.0, 1, 0),
    ("accNan", base 100.0 0.0 0.0, 100, nan, 1, 0),
    ("accInf", base 100.0 0.0 0.0, 100, inf, 1, 0),
    ("ellipseRc", plan leo 86400.0 50.0 150.0 (ellipse leo 100.0) [] 1.0 0.0001 0.0, 100000, 0.1,
      4, 0),
    ("vbarHold", plan leo 86400.0 100.0 0.0 [0.0, -200.0, 0.0, 0.0, 0.0, 0.0] [] 0.0 0.0 0.0,
      100000, 0.1, 0, 0),
    ("hopShort", hop (1.5 * 2.0 * piF / leo), 100000, 0.1, 0, 0),
    ("hopLong", hop (3.0 * 2.0 * piF / leo), 100000, 0.1, 3, 2),
    ("radialHop", radialHop 2.0 0.1, 100000, 0.1, 0, 0),
    ("radialHopWide", radialHop 4.0 0.5, 100000, 0.1, 3, 0),
    ("geoEllipse", plan geo (2.0 * 86164.0) 500.0 500.0 (ellipse geo 1000.0) [] 10.0 0.0001 0.0,
      100000, 0.1, 0, 0),
    ("formation", plan nr (2.0 * orb) 80.0 80.0 [100.0, 0.0, 0.0, 0.0, -0.22, 0.22] [] 1.0 1e-4
      0.0, 100000, 0.1, 0, 0),
    ("nominalClose", plan nr 25000.0 50.0 20.0 [-30.0, -1000.0, 0.0, 0.0, 0.0495, 0.0275] [] 0.5
      2e-5 0.0, 100000, 0.1, 3, 0),
    ("missedDrift", plan nr 35000.0 45.0 15.0 drift [(half, [0.0, 0.0165, 0.0])] 0.1 1e-5 2e-5,
      100000, 0.1, 3, 1),
    ("freeDrift", plan nr 35000.0 45.0 15.0 drift
      [(half, [0.0, 0.0165, 0.0]), (3.0 * half, [0.0, 0.0165, 0.0])] 0.1 1e-5 2e-5, 100000, 0.1,
      3, 3),
    ("laterBurn", plan nr 30000.0 60.0 15.0 bounded
      [(orb, [0.0, 0.01, 0.0]), (1.5 * orb, [0.0, -0.02, 0.0])] 0.1 1e-5 2e-5, 100000, 0.1, 3, 1),
    ("driftRc", plan nr orb 30.0 30.0 [50.0, 0.0, 100.0, 0.055, -0.0825, 0.0] [] 0.1 1e-5 0.0,
      100000, 0.1, 4, 0),
    ("boxRc", plan nr orb 20.0 36.0 [40.0, 0.0, 0.0, 0.0, -0.088, 0.055] [] 0.0 0.004 0.0,
      100000, 0.1, 4, 0),
    ("lateBurn", plan nr 30000.0 45.0 20.0 [-30.0, -1000.0, 0.0, 0.0, 0.0495, 0.0275]
      [(25000.0, [0.0, -0.05, 0.0])] 0.5 2e-5 1e-4, 100000, 0.1, 3, 0),
    ("acceptBurns", plan nr (4.0 * orb) 60.0 15.0 bounded
      [(orb, [0.0, 0.01, 0.0]), (1.5 * orb, [0.0, -0.01, 0.0])] 0.1 1e-5 2e-5, 100000, 0.1, 0, 0),
    ("lastBurnRc", plan nr (2.0 * orb) 60.0 15.0 bounded [(orb, [0.0, -0.01, 0.0])] 0.1 1e-5
      2e-5, 100000, 0.1, 4, 0),
    ("genericK1", plan nr (2.0 * orb) 12.53 2.49 kS kBurns 0.05 5e-6 1e-5, 100000, 0.1, 3, 0),
    ("genericK2", plan nr (2.0 * orb) 3.58 8.71 kS kBurns 0.05 5e-6 1e-5, 100000, 0.1, 4, 2),
    ("genericK3", plan nr (2.0 * orb) 5.96 4.14 kS kBurns 0.05 5e-6 1e-5, 100000, 0.1, 0, 0),
    ("genericL", plan nr (2.0 * orb) 12.71 5.52 lS lBurns 0.05 5e-6 1e-5, 100000, 0.1, 4, 1),
    ("genericM", plan nr (2.0 * orb) 18.35 2.84 mS mBurns 0.05 5e-6 1e-5, 100000, 0.1, 3, 0),
    ("vbarLateBurn", plan leo 6000.0 50.0 0.0 [0.0, -200.0, 0.0, 0.0, 0.0, 0.0]
      [(5900.0, [0.0, 1.0, 0.0])] 0.0 0.0 0.0, 100000, 0.1, 0, 0),
    ("flyByTurn", plan geo 800.0 63.0 0.0 [50.0, -375.0, 0.0, 0.0, 1.0, 0.0]
      [(400.0, [1.0, -1.0, 0.0])] 0.0 0.0 0.0, 100000, 0.1, 3, 0),
    ("random1", random1, 100000, 0.1, 0, 0),
    ("random2", random2, 100000, 0.1, 0, 0),
    ("random34", random34, 100000, 0.1, 0, 0),
    ("ellipseCap", plan leo 86400.0 50.0 50.0 (ellipse leo 100.0) [] 1.0 0.0001 0.0, 1600,
      0.1, 0, 0),
    ("hopShortCap", hop (1.5 * 2.0 * piF / leo), 56, 0.1, 0, 0),
    ("fuel", plan nr (2.0 * orb) 80.0 80.0 [100.0, 0.0, 0.0, 0.0, -0.22, 0.22] [] 1.0 1e-4 0.0,
      1, 0.1, 5, 0),
    ("fuelRc", plan nr 100.0 80.0 80.0 [100.0, 1e5, 0.0, 0.0, -0.22, 0.22] [] 1.0 1e-4 0.0, 1,
      1e300, 6, 0),
    ("short", [leo, 1.0, 0.0, 0.0], 100, 0.1, 1, 0),
    ("size", base 100.0 0.0 0.0 ++ [0.0], 100, 0.1, 1, 0),
    ("tooMany", base 100.0 0.0 0.0 ++ ((List.range 17).map fun _ =>
      [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]).flatten, 100, 0.1, 1, 0),
    ("fuelZero", base 100.0 0.0 0.0, 0, 0.1, 1, 0),
    ("fuelLarge", base 100.0 0.0 0.0, 1048577, 0.1, 1, 0),
    ("nan", plan leo 100.0 nan 0.0 (ellipse leo 100.0) [] 1.0 0.0 0.0, 100, 0.1, 2, 0),
    ("inf", plan leo inf 0.0 0.0 (ellipse leo 100.0) [] 1.0 0.0 0.0, 100, 0.1, 2, 0),
    ("nZero", plan 0.0 100.0 0.0 0.0 (ellipse leo 100.0) [] 1.0 0.0 0.0, 100, 0.1, 2, 0),
    ("nNegative", plan (-leo) 100.0 0.0 0.0 (ellipse leo 100.0) [] 1.0 0.0 0.0, 100, 0.1, 2, 0),
    ("horizonZero", base 0.0 0.0 0.0, 100, 0.1, 2, 0),
    ("dminNegative", base 100.0 (-1.0) 0.0, 100, 0.1, 2, 0),
    ("drcNegative", base 100.0 0.0 (-1.0), 100, 0.1, 2, 0),
    ("boxOrder", plan leo 100.0 0.0 0.0 (ellipse leo 100.0) [] (-1.0) 0.0 0.0, 100, 0.1, 2, 0),
    ("burnBoxOrder", plan leo 100.0 0.0 0.0 (ellipse leo 100.0) [(50.0, [0.0, 0.0, 0.0])] 1.0 0.0
      (-1e-4), 100, 0.1, 2, 0),
    ("burnOrder", plan leo 100.0 0.0 0.0 (ellipse leo 100.0)
      [(50.0, [0.0, 0.0, 0.0]), (40.0, [0.0, 0.0, 0.0])] 1.0 0.0 0.0, 100, 0.1, 2, 0),
    ("burnLate", plan leo 100.0 0.0 0.0 (ellipse leo 100.0) [(150.0, [0.0, 0.0, 0.0])] 1.0 0.0
      0.0, 100, 0.1, 2, 0),
    ("burnEarly", plan leo 100.0 0.0 0.0 (ellipse leo 100.0) [(-1.0, [0.0, 0.0, 0.0])] 1.0 0.0
      0.0, 100, 0.1, 2, 0),
    ("thresholdOverflow", base 100.0 1e200 0.0, 100, 0.1, 7, 0),
    ("stateOverflow", plan leo 100.0 0.0 0.0 [1e300, 0.0, 0.0, 0.0, 0.0, 0.0] [] 0.0 0.0 0.0, 100,
      0.1, 7, 0) ]

def resultText (r : Result) : String :=
  s!"{r.status} {r.scenario} {r.stop.toBits} {r.sep.toBits} {r.rc.toBits}"

def cases : IO Unit := do
  for (_, xs, fuel, acc, _, _) in all do
    line "passivesafety" "check" "list:i64,i64,f64,f64,f64" [arrF xs, u fuel, fl acc]
      (resultText (check xs.toArray fuel acc))

def bits : IO Unit := do
  for (name, xs, fuel, acc, status, scenario) in all do
    let r := check xs.toArray fuel acc
    let words := " ".intercalate (xs.map fun x => toString x.toBits)
    IO.println
      s!"{name} {status} {scenario} {xs.length} {words} {fuel} {acc.toBits} {resultText r}"

/-- Whether a search has finished: it failed, or it covered `[0, e]`. -/
def finished (m : March) (e : Float) : Bool := m.status != 0 || e ≤ m.t

/-- The panels that a search evaluates: the least fuel up to `fuel` with which `run` finishes, or
`fuel` when it does not finish. -/
def used (run : UInt64 → March) (e : Float) (fuel : UInt64) : Nat := Id.run do
  if !finished (run fuel) e then return fuel.toNat
  let mut lo : UInt64 := 0
  let mut hi : UInt64 := fuel
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if finished (run mid) e then hi := mid else lo := mid
  return hi.toNat

/-- The panels that `check xs fuel acc` evaluates over all its searches, for an input that passes
the checks of the layout and the values: the scenario loop of `scanStep`, with the count of each
search from `used`. -/
def panels (xs : Array Float) (fuel : UInt64) (acc : Float) : Nat := Id.run do
  let N := (xs.size.toUInt64 - 16) / 7
  let d2 := (square (rd xs 2)).hi
  let r2 := (square (rd xs 3)).hi
  let e := rd xs 1
  let inv := Library.Numerics.Float64.Trig.invPi
  let half := Library.Numerics.Float64.Trig.halfPi
  let mut sepBest := maxFloat
  let mut rcBest := maxFloat
  let mut total := 0
  for jn in [0:2 * N.toNat + 1] do
    let j := jn.toUInt64
    let m := sepSearch inv half xs N j e d2 acc sepBest fuel
    total := total + used (fun f => sepSearch inv half xs N j e d2 acc sepBest f) e fuel
    if searchStatus m e 3 5 != 0 then return total
    let tL := lastTime xs N j
    let r := rcSearch inv half xs N j tL twoPiHi r2 acc rcBest fuel
    total := total + used (fun f => rcSearch inv half xs N j tL twoPiHi r2 acc rcBest f)
      twoPiHi fuel
    if searchStatus r twoPiHi 4 6 != 0 then return total
    sepBest := m.best
    rcBest := r.best
  return total

/-- The least fuel up to 1,048,576 with which `check` returns neither status 5 nor status 6, the
most panels that one of its searches evaluates. -/
def needed (xs : Array Float) (acc : Float) : Nat := Id.run do
  let unfinished (f : UInt64) : Bool :=
    let st := (check xs f acc).status
    st == 5 || st == 6
  let top : UInt64 := 1048576
  if unfinished top then return top.toNat
  let mut lo : UInt64 := 0
  let mut hi : UInt64 := top
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if unfinished mid then lo := mid else hi := mid
  return hi.toNat

/-- Prints, for each case with a status from 0 to 6, its name, accuracy, status, scenario, bounds,
the panels that its searches evaluate, and the least fuel that it needs. -/
def panelReport : IO Unit := do
  for (name, xs, fuel, acc, _, _) in all do
    let r := check xs.toArray fuel acc
    if r.status == 0 || (3 ≤ r.status && r.status ≤ 6) then
      IO.println (s!"{name} acc {acc} status {r.status} scenario {r.scenario} sep {r.sep} " ++
        s!"rc {r.rc} panels {panels xs.toArray fuel acc} " ++
        s!"needed {needed xs.toArray acc}")

end TestSupport.PassiveSafety.Cases
