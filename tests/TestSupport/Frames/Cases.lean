import Demos.Frames.Program
import TestSupport.Host

/-! Cases of the frames module.  `cases` prints the module cases for `tests/verified/run.sh`, and
`serve` reads the input lines of `tests/frames/oracle.py` and prints each line followed by the
status and the bit patterns of the result's endpoints. -/

namespace TestSupport.Frames.Cases

open TestSupport.Host Demos.Frames Library.Numerics.Interval

def interval (i : Interval) : String := s!"{i.status} {i.lo.toBits} {i.hi.toBits}"

def angleText (a : Angle) : String := s!"{a.status} {a.lo.toBits} {a.hi.toBits}"

def vecText (v : Vec) : String := s!"{v.status} {interval v.x} {interval v.y} {interval v.z}"

def geodText (g : Coords) : String :=
  s!"{g.status} {interval g.lat} {interval g.lon} {interval g.h}"

def angleKind : String := "list:i64,f64,f64"

def vecKind : String := "list:i64," ++ ",".intercalate (List.replicate 3 "i64,f64,f64")

def float (w : Nat) : Float := Float.ofBits (UInt64.ofNat w)

/-- The result of an input line, from its first numbers. -/
def respond (words : List String) : Option String :=
  let n := (words.drop 1).filterMap String.toNat?
  match words.head?, n with
  | some "gmst", d :: lo :: hi :: _ =>
    some (angleText (gmst (UInt64.ofNat d) (float lo) (float hi)))
  | some "teme", d :: a :: b :: c :: e :: g :: h :: i :: j :: k :: l :: m :: o :: _ =>
    some (vecText (temeToEcef (UInt64.ofNat d) (float a) (float b) (float c) (float e) (float g)
      (float h) (float i) (float j) (float k) (float l) (float m) (float o)))
  | some "cart", a :: b :: c :: e :: g :: h :: _ =>
    some (vecText (toCartesian (float a) (float b) (float c) (float e) (float g) (float h)))
  | some "geod", a :: b :: c :: e :: g :: h :: _ =>
    some (geodText (toGeodetic (float a) (float b) (float c) (float e) (float g) (float h)))
  | _, _ => none

partial def serve : IO Unit := do
  let stdin ← IO.getStdin
  let rec go : IO Unit := do
    let text ← stdin.getLine
    if text.isEmpty then return
    let line := text.trimRight
    match respond (line.splitOn " ") with
    | some r => IO.println s!"{line} {r}"
    | none => throw (IO.userError s!"cannot read the line: {line}")
    go
  go

def gmstInputs : List (UInt64 × Float × Float) :=
  [ (53736, 0, 0), (51544, 43200, 43200), (60000, 3600.5, 3600.5), (60000, 0, 1e-3),
    (41317, -3600, -3600), (60000, 90000, 90000), (15020, 12345.678, 12345.678),
    (88069, 86399.999, 86400), (4294967295, 0, 0), (4294967296, 0, 1), (60000, 1, 0),
    (60000, nan, 1), (60000, 0, inf), (60000, -1e300, 1e300) ]

def temeInputs : List (UInt64 × List Float) :=
  [ (60000, [0, 0, 0.1, 0.1, 0.3, 0.3, 7000, 7000, 0, 0, 0, 0]),
    (60000, [43200, 43200, -0.2, -0.2, 0.45, 0.45, 1200.5, 1200.5, -6500.25, -6500.25, 1800, 1800]),
    (59000, [100, 100.001, 0.05, 0.0501, 0.35, 0.3501, 42164, 42165, 10, 11, -5, -4]),
    (61000, [86000, 86000, 0, 0, 0, 0, -3000, -3000, 4000, 4000, -4500, -4500]),
    (60000, [nan, 0, 0.1, 0.1, 0.3, 0.3, 7000, 7000, 0, 0, 0, 0]),
    (60000, [0, 0, 0.1, inf, 0.3, 0.3, 7000, 7000, 0, 0, 0, 0]),
    (60000, [0, 0, 0.1, 0.1, 0.3, 0.3, 7001, 7000, 0, 0, 0, 0]),
    (4294967296, [0, 0, 0.1, 0.1, 0.3, 0.3, 7000, 7000, 0, 0, 0, 0]),
    (60000, [0, 0, 0.1, 0.1, 0.3, 0.3, -1e308, 1e308, 0, 0, 0, 0]) ]

/-- Latitudes, longitudes, and heights: a point at mid-latitude, the poles, a box, and inputs
that the program rejects. -/
def cartInputs : List (List Float) :=
  [ [0.7, 0.7, -1.2, -1.2, 0.35, 0.35], [1.5707963267948966, 1.5707963267948966, 0, 0, 0, 0],
    [-1.5707963267948966, -1.5707963267948966, 2, 2, 1, 1], [0.1, 0.1001, 3, 3.0001, 400, 401],
    [nan, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1.7976931348623157e308, 1.7976931348623157e308] ]

/-- Earth-fixed positions: SOFA's test point, an equatorial box across `z = 0`, a box across the
negative x-axis, a point near the north pole, a box below the equator near the south pole, and
inputs that the program rejects or that lie outside the domain. -/
def geodInputs : List (List Float) :=
  [ [2000, 2000, 3000, 3000, 5244, 5244], [6378, 6379, -1, 1, -1, 1],
    [-6379, -6378, -1, 1, 10, 11], [0.05, 0.05, 0.1, 0.1, 6356.75, 6356.75],
    [-1, 1, -2, -0.5, -6357, -6356], [30, 30, 0, 0, 10, 10], [0, 0, 0, 0, 6356, 6357],
    [nan, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [1e300, 1e300, 0, 0, 0, 0] ]

def cases : IO Unit := do
  for (d, lo, hi) in gmstInputs do
    line "frames" "gmst" angleKind [u d, fl lo, fl hi] (angleText (gmst d lo hi))
  for (d, xs) in temeInputs do
    match xs with
    | [a, b, c, e, g, h, i, j, k, l, m, o] =>
      line "frames" "temeToEcef" vecKind (u d :: xs.map fl)
        (vecText (temeToEcef d a b c e g h i j k l m o))
    | _ => throw (IO.userError "a TEME case needs twelve floats")
  for xs in cartInputs do
    match xs with
    | [a, b, c, e, g, h] =>
      line "frames" "toCartesian" vecKind (xs.map fl) (vecText (toCartesian a b c e g h))
    | _ => throw (IO.userError "a case of toCartesian needs six floats")
  for xs in geodInputs do
    match xs with
    | [a, b, c, e, g, h] =>
      line "frames" "toGeodetic" vecKind (xs.map fl) (geodText (toGeodetic a b c e g h))
    | _ => throw (IO.userError "a case of toGeodetic needs six floats")

end TestSupport.Frames.Cases
