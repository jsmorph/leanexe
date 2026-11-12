import Demos.Events.Program
import TestSupport.Host

/-! Cases of the event-window module for `tests/verified/run.sh --cases events`: the shadow of a
low orbit with the three cones and a padding, a geostationary orbit, an eccentric orbit, the
exclusion events of an inertial vector and of a vector in the orbit's frame, the caps, rejected
enclosures, invalid inputs, and orbits and events that a linear congruential generator draws. -/

namespace TestSupport.Events.Cases

open TestSupport.Host Demos.Events

/-- The input for an orbit of seven values, the day of minute 0, the window, the event, its angle,
the Earth's radius, the padding, the vector, and the levels and the cap. -/
def input (o : List Float) (d0 t0 t1 code ang r p b1 b2 b3 l c : Float) : List Float :=
  [1.0] ++ o ++ [398600.4418, d0, t0, t1, code, ang, r, p, b1, b2, b3, l, c]

def leo : List Float := [6878, 0.001, 0, 0, 0, 0, 0]

def fixed : List (List Float) :=
  [ input leo 9574.5 0 1440 1 0.269 6378.137 0 0 0 0 20 65536,
    input leo 9574.5 0 1440 1 (-0.264) 6378.137 0 0 0 0 20 65536,
    input leo 9574.5 0 1440 1 0 6378.137 5 0 0 0 16 65536,
    input [42164, 0.0002, 0.05, 0, 0, 0, 0] 9574.5 0 1440 1 0.269 6378.137 0 0 0 0 20 65536,
    input [26554, 0.72, 63.4, 40, 270, 10, 0] 9574.5 0 1440 1 0.269 6378.137 0 0 0 0 18 65536,
    input leo 9809.5 0 10080 2 1 0 0 (-0.75) (-0.6) (-0.26) 20 65536,
    input leo 9574.5 0 1440 3 30 0 0 0 1 0 20 65536,
    input leo 9574.5 0 1440 1 0.269 6378.137 0 0 0 0 0 65536,
    input leo 9574.5 0 1440 1 0.269 6378.137 0 0 0 0 20 1,
    input leo 9574.5 0 1440 1 0.269 6378.137 0 0 0 0 20 64,
    input [1e300, 0.1, 30, 0, 0, 0, 0] 9574.5 0 1440 1 0.269 6378.137 0 0 0 0 8 4096,
    input leo 9574.5 0 1440 4 0.269 6378.137 0 0 0 0 20 65536,
    input leo 9574.5 0 1440 3 30 0 0 0 0 0 20 65536,
    input leo 9574.5 0 1440 1 90 6378.137 0 0 0 0 20 65536,
    input [6878, 1, 0, 0, 0, 0, 0] 9574.5 0 1440 1 0.269 6378.137 0 0 0 0 20 65536,
    [1.0, 7000.0] ]

/-- The next state of the generator. -/
def step (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A float in `[lo, hi)` from the state. -/
def draw (s : UInt64) (lo hi : Float) : Float :=
  lo + (hi - lo) * ((s >>> 11).toFloat / 9007199254740992.0)

/-- An input with a low orbit and a shadow or a vector in the orbit's frame, and the next
state. -/
def drawn (s : UInt64) : List Float × UInt64 :=
  let s1 := step s
  let s2 := step s1
  let s3 := step s2
  let s4 := step s3
  let s5 := step s4
  let s6 := step s5
  let s7 := step s6
  let s8 := step s7
  let o := [draw s1 6700 7600, draw s2 0 0.02, draw s3 0 180, draw s4 0 360, draw s5 0 360,
    draw s6 0 360, 0]
  let shadow := (s7 >>> 63) == 0
  (input o (draw s8 7300 11000) 0 1440 (if shadow then 1 else 3)
    (if shadow then draw s7 (-0.3) 0.3 else draw s7 10 80) 6378.137 (draw s6 0 3)
    (draw s2 (-1) 1) (draw s3 (-1) 1) (draw s4 (-1) 1) 16 65536, s8)

def random (n : Nat) : List (List Float) :=
  ((List.range n).foldl (fun (acc : List (List Float) × UInt64) _ =>
    let (xs, s1) := drawn acc.2
    (acc.1 ++ [xs], s1)) ([], 20261111)).1

def cases : IO Unit := do
  for xs in fixed ++ random 12 do
    let ys := events xs.toArray
    let result := ", ".intercalate (ys.toList.map fun y => toString y.toBits)
    line "events" "events" "array-u64" [arrF xs] s!"[{result}]"

end TestSupport.Events.Cases
