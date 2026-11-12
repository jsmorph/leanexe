import Demos.Orbit.LambertBox
import TestSupport.Host

/-! Cases of the orbit-determination modules.  `cases` prints the module cases of `gibbsBounds`
and `lambertBounds` for `tests/verified/run.sh`.  `gibbs` reads lines of the bit patterns of the
twenty endpoints of `gibbsBounds` and prints the status and the bit patterns of the three
intervals, and `lambert` reads lines of the bit patterns of the nineteen arguments of
`lambertBounds` and prints the status and the bit patterns of the seven intervals, for
`tests/orbit/reference.py`. -/

namespace TestSupport.Orbit.Cases

open TestSupport.Host Demos.Orbit Library.Numerics.Interval

def interval (i : Interval) : String := s!"{i.status} {i.lo.toBits} {i.hi.toBits}"

def velocityText (v : Velocity) : String :=
  s!"{v.status} {interval v.vx} {interval v.vy} {interval v.vz}"

def transferText (t : Transfer) : String :=
  s!"{t.status} {interval t.x} {interval t.v1x} {interval t.v1y} {interval t.v1z} " ++
    s!"{interval t.v2x} {interval t.v2y} {interval t.v2z}"

def kind (n : Nat) : String := "list:i64," ++ ",".intercalate (List.replicate n "i64,f64,f64")

/-- Three positions in km of Curtis's Example 5.1, as boxes of half-width `w`. -/
def gibbsInputs : List (List Float) :=
  let r := [-294.32, 4265.1, 5986.7, -1365.5, 3637.6, 6346.8, -2940.3, 2473.7, 6555.8]
  let box (w : Float) : List Float :=
    (r.map fun c => [c - w, c + w]).flatten ++ [398600.0, 398600.0]
  [box 0.1, box 0.01, box 1.0, box 0.0,
    -- positions in the reverse order
    ([-2940.3, 2473.7, 6555.8, -1365.5, 3637.6, 6346.8, -294.32, 4265.1, 5986.7].map
      fun c => [c - 0.1, c + 0.1]).flatten ++ [398600.0, 398600.0],
    -- collinear positions
    ([1000.0, 0.0, 0.0, 2000.0, 0.0, 0.0, 3000.0, 0.0, 0.0].map fun c => [c, c]).flatten ++
      [398600.0, 398600.0],
    -- an interval with lo > hi, a nonfinite endpoint, and a negative μ
    [1.0, 0.0] ++ List.replicate 16 1.0 ++ [398600.0, 398600.0],
    List.replicate 17 1.0 ++ [1.0 / 0.0, 398600.0, 398600.0],
    List.replicate 18 1000.0 ++ [-1.0, 1.0]]

/-- Two positions in km, a time of flight in s, `μ`, and an axis: Curtis's Example 5.2 with
the two directions, a transfer angle near π, a hyperbolic transfer, and invalid inputs. -/
def lambertInputs : List (List Float) :=
  let ex (k : Float) : List Float :=
    [5000.0, 5000.0, 10000.0, 10000.0, 2100.0, 2100.0, -14600.0, -14600.0, 2500.0, 2500.0,
      7000.0, 7000.0, 3600.0, 3600.0, 398600.0, 398600.0, 0.0, 0.0, k]
  [ex 1.0, ex (-1.0),
    [7000.0, 7000.0, 0.0, 0.0, 0.0, 0.0, -7000.0, -7000.0, 10.0, 10.0, 0.0, 0.0, 2700.0, 2700.0,
      398600.0, 398600.0, 0.0, 0.0, 1.0],
    [7000.0, 7000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7500.0, 7500.0, 0.0, 0.0, 300.0, 300.0,
      398600.0, 398600.0, 0.0, 0.0, 1.0],
    [7000.0, 7001.0, 0.0, 1.0, 0.0, 1.0, 0.0, 1.0, 7500.0, 7501.0, 0.0, 1.0, 1000.0, 1001.0,
      398600.0, 398600.0, 0.0, 0.0, 1.0],
    -- transfer angle π, a plane that contains `k`, and a negative time
    [7000.0, 7000.0, 0.0, 0.0, 0.0, 0.0, -7000.0, -7000.0, 0.0, 0.0, 0.0, 0.0, 2700.0, 2700.0,
      398600.0, 398600.0, 0.0, 0.0, 1.0],
    [7000.0, 7000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7500.0, 7500.0, 0.0, 0.0, 2700.0, 2700.0,
      398600.0, 398600.0, 1.0, 0.0, 0.0],
    [7000.0, 7000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7500.0, 7500.0, 0.0, 0.0, -1.0, -1.0,
      398600.0, 398600.0, 0.0, 0.0, 1.0]]

def gibbsOf : List Float → Velocity
  | [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
      a20] =>
    gibbsBounds a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
  | _ => noVelocity 9

def lambertOf : List Float → Transfer
  | [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19] =>
    lambertBounds a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
  | _ => noTransfer 9

def cases : IO Unit := do
  for xs in gibbsInputs do
    line "gibbs" "gibbsBounds" (kind 3) (xs.map fl) (velocityText (gibbsOf xs))
  for xs in lambertInputs do
    line "lambert" "lambertBounds" (kind 7) (xs.map fl) (transferText (lambertOf xs))

/-- Reads lines of bit patterns and prints the result of `run` on their floats. -/
partial def serve (n : Nat) (run : List Float → String) : IO Unit := do
  let stdin ← IO.getStdin
  let rec go : IO Unit := do
    let text ← stdin.getLine
    if text.isEmpty then return
    let words := (text.trim.splitOn " ").filterMap String.toNat?
    if words.length != n then throw (IO.userError s!"expected {n} words: {text}")
    IO.println (run (words.map fun w => Float.ofBits (UInt64.ofNat w)))
    (← IO.getStdout).flush
    go
  go

def gibbs : IO Unit := serve 20 fun xs => velocityText (gibbsOf xs)

def lambert : IO Unit := serve 19 fun xs => transferText (lambertOf xs)

end TestSupport.Orbit.Cases
