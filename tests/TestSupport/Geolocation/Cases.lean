import Demos.Geolocation.Program
import TestSupport.Host

/-! Cases of the geolocation module for `tests/verified/run.sh --cases geolocation`: an emitter on
the ellipsoid seen by four receivers at medium altitude with time differences, frequency
differences, and both, receiver intervals, an emitter on an aircraft, the whole Earth as region,
a region without the emitter, the levels and the cap, invalid inputs, and emitters and receivers
that a linear congruential generator draws. -/

namespace TestSupport.Geolocation.Cases

open TestSupport.Host Demos.Geolocation

def pi : Float := 3.141592653589793

def rad (d : Float) : Float := d * pi / 180.0

/-- The WGS 84 position of a latitude, a longitude, and a height. -/
def position (φ lam h : Float) : Float × Float × Float :=
  let f := 1.0 / 298.257223563
  let e2 := f * (2.0 - f)
  let s := φ.sin
  let n := 6378.137 / (1.0 - e2 * s * s).sqrt
  ((n + h) * φ.cos * lam.cos, (n + h) * φ.cos * lam.sin, (n * (1.0 - e2) + h) * s)

/-- A receiver above the point at latitude `la` and longitude `lo` in degrees, at altitude `alt`
over a sphere of radius 6378.137 km, on a circular orbit with heading `hd` in degrees: its
Earth-fixed position and its velocity relative to the rotating Earth. -/
def receiver (la lo alt hd : Float) : (Float × Float × Float) × (Float × Float × Float) :=
  let φ := rad la
  let lam := rad lo
  let r := 6378.137 + alt
  let p := (r * φ.cos * lam.cos, r * φ.cos * lam.sin, r * φ.sin)
  let east := (-lam.sin, lam.cos, 0.0)
  let north := (-φ.sin * lam.cos, -φ.sin * lam.sin, φ.cos)
  let v := (398600.4418 / r).sqrt
  let a := rad hd
  let w := 7.2921158553e-5
  ((p.1, p.2.1, p.2.2),
    (v * (a.cos * north.1 + a.sin * east.1) + w * p.2.1,
      v * (a.cos * north.2.1 + a.sin * east.2.1) - w * p.1,
      v * (a.cos * north.2.2 + a.sin * east.2.2)))

def norm3 (a : Float × Float × Float) : Float := (a.1 * a.1 + a.2.1 * a.2.1 + a.2.2 * a.2.2).sqrt

def sub3 (a b : Float × Float × Float) : Float × Float × Float :=
  (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)

def dot3 (a b : Float × Float × Float) : Float := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- The time and frequency differences of receiver `i` less receiver `j` for the emitter `x`
and the carrier frequency `f`. -/
def differences (rs : List ((Float × Float × Float) × (Float × Float × Float))) (i j : Nat)
    (x : Float × Float × Float) (f : Float) : Float × Float :=
  let a := rs[i]!
  let b := rs[j]!
  let da := sub3 a.1 x
  let db := sub3 b.1 x
  ((norm3 da - norm3 db) / 299792.458,
    -f * (dot3 da a.2 / norm3 da - dot3 db b.2 / norm3 db) / 299792.458)

/-- The entries of a receiver with half-widths `dp` and `dv`. -/
def entries (r : (Float × Float × Float) × (Float × Float × Float)) (dp dv : Float) :
    List Float :=
  [0.0, 0.0, r.1.1 - dp, r.1.1 + dp, r.1.2.1 - dp, r.1.2.1 + dp, r.1.2.2 - dp, r.1.2.2 + dp,
    r.2.1 - dv, r.2.1 + dv, r.2.2.1 - dv, r.2.2.1 + dv, r.2.2.2 - dv, r.2.2.2 + dv]

/-- An input for receivers `rs` and an emitter at `(φ, lam, h)` in degrees and km, with the
measurements of kind 1, 2, or both (3) between receiver 0 and each other receiver, computed at
the emitter for the center of the frequency interval. -/
def input (rs : List ((Float × Float × Float) × (Float × Float × Float))) (φ lam h : Float)
    (kinds : Nat) (region : List Float) (res levels cap dp dv : Float) : List Float :=
  let x := position (rad φ) (rad lam) h
  let f := 406.05e6
  let pairs := (List.range (rs.length - 1)).map (· + 1)
  let t := pairs.map fun j => [1.0, 0.0, j.toFloat, (differences rs 0 j x f).1, 1e-6]
  let q := pairs.map fun j => [2.0, 0.0, j.toFloat, (differences rs 0 j x f).2, 0.5]
  let ms := (if kinds == 2 then [] else t) ++ (if kinds == 1 then [] else q)
  [1.0, 0.0, rs.length.toFloat, ms.length.toFloat, 0.0, 0.0, 0.0, 0.0, 0.0, 406.0e6, 406.1e6] ++
    region ++ [res, levels, cap] ++ (rs.map fun r => entries r dp dv).flatten ++ ms.flatten

def meo : List ((Float × Float × Float) × (Float × Float × Float)) :=
  [receiver 10 30 23222 20, receiver 55 10 23222 160, receiver 40 70 23222 300,
    receiver (-15) 50 23222 80]

def near (φ lam d h0 h1 : Float) : List Float :=
  [rad (φ - d), rad (φ + d), rad (lam - d), rad (lam + d), h0, h1]

def wholeEarth : List Float :=
  [-1.5707963267948968, 1.5707963267948968, -3.1415926535897936, 3.1415926535897936, 0.0, 0.0]

def fixed : List (List Float) :=
  let good := input meo 35 40 0 3 (near 35 40 2 0 0) 0.2 60 65536 0 0
  [ input meo 35 40 0 1 (near 35 40 2 0 0) 0.2 60 65536 0 0,
    input meo 35 40 0 2 (near 35 40 2 0 0) 0.2 60 65536 0 0,
    good,
    input meo 35 40 0 3 (near 35 40 2 0 0) 0.2 60 65536 0.01 1e-5,
    input meo 35 40 9 3 (near 35 40 1 0 12) 0.25 60 65536 0 0,
    input meo 35 40 0 3 wholeEarth 2.0 60 65536 0 0,
    input meo 35 40 0 3 (near 11 11 1 0 0) 0.2 60 65536 0 0,
    input meo 35 40 0 3 (near 35 40 2 0 0) 0.2 0 65536 0 0,
    input meo 35 40 0 3 (near 35 40 2 0 0) 0.2 10 65536 0 0,
    input meo 35 40 0 3 (near 35 40 2 0 0) 0.2 60 4 0 0,
    input meo 35 40 0 3 (near 35 40 2 0 0) 0.2 60 65536 1e300 0,
    good.set 1 1.0,
    good.set 2 1.0,
    good.set 9 0.0,
    good.set 12 (-2.0),
    good.set 17 0.0,
    good.set 19 65537.0,
    good.set 76 3.0,
    good.set 77 4.0,
    good.set 80 (-1.0),
    good.take 80,
    [] ]

/-- The next state of the generator. -/
def step (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- A float in `[lo, hi)` from the state. -/
def draw (s : UInt64) (lo hi : Float) : Float :=
  lo + (hi - lo) * ((s >>> 11).toFloat / 9007199254740992.0)

/-- An input with an emitter and three receivers at medium altitude drawn around it, and the
next state. -/
def drawn (s : UInt64) : List Float × UInt64 :=
  let s1 := step s
  let s2 := step s1
  let s3 := step s2
  let s4 := step s3
  let s5 := step s4
  let s6 := step s5
  let s7 := step s6
  let φ := draw s1 (-60) 60
  let lam := draw s2 (-180) 180
  let rs := [receiver (φ + draw s3 (-30) 30) (lam + draw s4 (-30) 30) 23222 (draw s5 0 360),
    receiver (φ + draw s4 (-30) 30) (lam + draw s5 (-30) 30) 23222 (draw s6 0 360),
    receiver (φ + draw s6 (-30) 30) (lam + draw s3 (-30) 30) 23222 (draw s7 0 360)]
  (input rs φ lam 0 3 (near φ lam 1 0 0) 0.5 40 4096 0.005 0, s7)

def random (n : Nat) : List (List Float) :=
  ((List.range n).foldl (fun (acc : List (List Float) × UInt64) _ =>
    let (xs, s1) := drawn acc.2
    (acc.1 ++ [xs], s1)) ([], 20261111)).1

def cases : IO Unit := do
  for xs in fixed ++ random 6 do
    let ys := locate xs.toArray
    let result := ", ".intercalate (ys.toList.map fun y => toString y.toBits)
    line "geolocation" "locate" "array-u64" [arrF xs] s!"[{result}]"

end TestSupport.Geolocation.Cases
