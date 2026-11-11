import Demos.Screening.Program
import TestSupport.Host

/-! Cases of the screening module for `tests/verified/run.sh --cases screening`: two crossing
circular orbits, pairs that each filter excludes, a pair at the cap, invalid inputs, and pairs of
low orbits whose elements a linear congruential generator draws. -/

namespace TestSupport.Screening.Cases

open TestSupport.Host Demos.Screening

/-- The input for two element lists of seven values each and the window, the threshold, the
padding, the apogee–perigee flag, the orbit-path filter's levels and cap, and the isolation's
levels and cap. -/
def input (o1 o2 : List Float) (t0 t1 d p aps lp cp l c : Float) : List Float :=
  [1.0] ++ o1 ++ o2 ++ [398600.4418, t0, t1, d, p, aps, lp, cp, l, c]

def fixed : List (List Float) :=
  [ input [7000, 0, 0, 0, 0, 0, 100] [7001, 0, 90, 0, 0, 0, 100] 0 1440 5 0 1 20 4096 20 65536,
    input [7000, 0.001, 51.6, 30, 10, 0, 0] [42164, 0.0002, 0.1, 200, 50, 120, 0] 0 1440 5 0 1
      20 4096 20 65536,
    input [7000, 0, 0, 0, 0, 0, 0] [7000, 0.1, 90, 0, 90, 50, 0] 0 1440 5 0 1 20 65536 20 65536,
    input [7000, 0, 0, 0, 0, 0, 0] [7000, 0.1, 90, 0, 90, 50, 0] 0 1440 5 0 1 0 65536 20 65536,
    input [7000, 0.01, 40, 0, 0, 0, 0] [7100, 0.02, 80, 10, 0, 0, 0] 0 1440 5 2 0 0 1 8 16,
    input [26554, 0.72, 63.4, 40, 270, 10, 0] [7000, 0.001, 98, 0, 0, 0, 0] 0 1440 5 0 1 12
      4096 16 4096,
    input [7000, 1.0, 0, 0, 0, 0, 0] [7001, 0, 90, 0, 0, 0, 100] 0 1440 5 0 1 20 4096 20 65536,
    input [7000, 0, 0, 0, 0, 0, 100] [7001, 0, 90, 0, 0, 0, 100] 10 5 5 0 1 20 4096 20 65536,
    input [7000, 0, 0, 0, 0, 0, 100] [7001, 0, 90, 0, 0, 0, 100] 0 1440 5 0 1 20 4096 61 65536,
    input [7000, 0, 0, 0, 0, 0, 100] [7001, 0, nan, 0, 0, 0, 100] 0 1440 5 0 1 20 4096 20 65536,
    [1.0, 7000.0] ]

/-- The next state of the generator. -/
def step (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A float in `[lo, hi)` from the state. -/
def draw (s : UInt64) (lo hi : Float) : Float :=
  lo + (hi - lo) * ((s >>> 11).toFloat / 9007199254740992.0)

/-- The elements of a low orbit, and the next state. -/
def leo (s : UInt64) : List Float × UInt64 :=
  let s1 := step s
  let s2 := step s1
  let s3 := step s2
  let s4 := step s3
  let s5 := step s4
  let s6 := step s5
  ([draw s1 6700 7600, draw s2 0 0.02, draw s3 5 175, draw s4 0 360, draw s5 0 360,
    draw s6 0 360, 0], s6)

def random (n : Nat) : List (List Float) :=
  ((List.range n).foldl (fun (acc : List (List Float) × UInt64) _ =>
    let (o1, s1) := leo acc.2
    let (o2, s2) := leo s1
    (acc.1 ++ [input o1 o2 0 1440 5 0 1 16 4096 18 65536], s2)) ([], 20261111)).1

def cases : IO Unit := do
  for xs in fixed ++ random 12 do
    let ys := screen xs.toArray
    let result := ", ".intercalate (ys.toList.map fun y => toString y.toBits)
    line "screening" "screen" "array-u64" [arrF xs] s!"[{result}]"

end TestSupport.Screening.Cases
