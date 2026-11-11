import Demos.Sgp4.Box
import Demos.Sgp4.Program

/-! The width of SGP4 boxes over intervals of time.  For three element sets of the verification
file of the Vallado code, `report` prints the widths of the coordinates of `sgp4Box` over
`[t₀, t₀ + h]` and the ranges of the coordinates over 401 samples of `sgp4` in that interval, and
`timing` times 2,000 boxes in the interpreter.  Run with
`tools/leanrun --timeout 25m lake env lean tests/screening/BoxWidth.lean`; the output is in
`Demos/Screening/requirements.md`. -/

open Demos.Sgp4 Library.Numerics.Interval

def sets : List (String × Float × Float × Float × Float × Float × Float × Float) :=
  [("06251", 15.56387291, 0.0030035, 58.0579, 54.0425, 139.1568, 221.1854, 0.12808e-3),
   ("28057", 14.35478080, 0.0000884, 98.4283, 247.6961, 88.1964, 271.9322, 0.35940e-4),
   ("00005", 10.82419157, 0.1859667, 34.2682, 348.7242, 331.7664, 19.3264, 0.28098e-4)]

def width (i : Interval) : Float := if i.status == 0 then i.hi - i.lo else -1.0

def sampled (n e incl node argp m bstar t0 h : Float) : Float × Float × Float :=
  Id.run do
    let mut lx := 1.0e30
    let mut hx := -1.0e30
    let mut ly := 1.0e30
    let mut hy := -1.0e30
    let mut lz := 1.0e30
    let mut hz := -1.0e30
    for k in [0:401] do
      let s := sgp4 n e incl node argp m bstar (t0 + h * (k.toFloat / 400.0))
      lx := min lx s.x
      hx := max hx s.x
      ly := min ly s.y
      hy := max hy s.y
      lz := min lz s.z
      hz := max hz s.z
    return (hx - lx, hy - ly, hz - lz)

def report : IO Unit := do
  for (name, n, e, incl, node, argp, m, bstar) in sets do
    for t0 in [360.0, 1440.0] do
      for h in [0.0001, 0.001, 0.01, 0.1, 1.0, 10.0, 100.0, 1440.0] do
        let b := sgp4Box (around n) (around e) (around incl) (around node) (around argp)
          (around m) (around bstar) (make t0 (t0 + h))
        let (rx, ry, rz) := sampled n e incl node argp m bstar t0 h
        IO.println (s!"{name} t0={t0} h={h} status={b.status} " ++
          s!"box=({width b.x}, {width b.y}, {width b.z}) sampled=({rx}, {ry}, {rz})")

#eval report

def timing : IO Unit := do
  let start ← IO.monoNanosNow
  let mut acc : Float := 0.0
  for k in [0:2000] do
    let t := 360.0 + k.toFloat * 0.01
    let b := sgp4Box (around 15.56387291) (around 0.0030035) (around 58.0579) (around 54.0425)
      (around 139.1568) (around 221.1854) (around 0.12808e-3) (make t (t + 0.01))
    acc := acc + b.x.hi
  let stop ← IO.monoNanosNow
  IO.println
    s!"2000 interval-time boxes in {(stop - start).toFloat / 1.0e6} ms (interpreted), {acc}"

#eval timing
