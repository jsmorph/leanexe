import Verified.Examples.Tgamma

/-!
The paths of `Tgamma.tgammaWith` as functions, and the equations that select them.  Each path
function repeats the code of its branch, so `tgamma_*` follows from the definition by `simp only`
with the branch conditions.  The tables are arbitrary arrays, which keeps the elaboration of the
equations independent of the table contents.  The conditions are the code's own tests on words and
floats.  `TgammaCases` turns them into conditions on the value of `x`.
-/

namespace Verified.Examples.TgammaBranches
open Verified.Examples.Tgamma

/-- `±∞` and NaN: `+∞` for `+∞`, `(-∞)/(-∞)` for `-∞`, and `x + x` for NaN. -/
def specialPath (x : Float) : Float :=
  if x.toBits <<< 1 == 0xFFE0000000000000 then (if x.toBits >>> 63 == 1 then x / x else x)
  else x + x

/-- Below `2 ^ -112` in magnitude: `1/x`, with an overflow at `2 ^ -1024`. -/
def tinyPath (x : Float) : Float :=
  if x.toBits == 0x0004000000000000 then
    Float.ofBits 0x7FEFFFFFFFFFFFFF + Float.ofBits 0x7C90000000000000
  else
    let r := 1.0 / x
    if x == 0.0 then r
    else if Fma.fma r x (-1.0) == 0.0 then r - 0.5 else r

/-- From `2 ^ -112` to `1/4` in magnitude: `1/x` plus a polynomial. -/
def smallPath (dbTab accTab smallTab : Array UInt64) (x : Float) : Float :=
  let x2 := x * x
  let x4 := x2 * x2
  let x8 := x4 * x4
  let c0 := entry smallTab 10 + x * entry smallTab 11 +
    x2 * (entry smallTab 12 + x * entry smallTab 13)
  let c4 := entry smallTab 14 + x * entry smallTab 15 +
    x2 * (entry smallTab 16 + x * entry smallTab 17)
  let c8 := entry smallTab 18 + x * entry smallTab 19 +
    x2 * (entry smallTab 20 + x * entry smallTab 21)
  let c12 := entry smallTab 22 + x * entry smallTab 23 +
    x2 * (entry smallTab 24 + x * entry smallTab 25)
  let c0 := c0 + x4 * c4
  let c8 := c8 + x4 * c12
  let (ch, cl) := polyDDD smallTab 0 5 x (x * (c0 + x8 * c8))
  let fh := 1.0 / x
  let (fh, fl) := fastSum fh (Fma.fma fh (-x) 1.0 * fh) ch cl
  let eps := fh * (Float.ofBits 0x3C19D35025BFF857 +  -- 3.5e-19
    (x2 * x4) * Float.ofBits 0x3CF203AF9EE75616)  -- 4e-15
  let ub := fh + (fl + eps)
  let lb := fh + (fl - eps)
  if ub != lb then accurate accTab dbTab x else ub

/-- The overflow above `0x1.573fae561f648p+7`. -/
def overflowPath : Float := Float.ofBits 0x7FEF000000000000 + Float.ofBits 0x7FEF000000000000

/-- The integers: `1/x` at zero, NaN below zero, and `(x - 1)!` above. -/
def intPath (x : Float) : Float :=
  let fx := floorF x
  if x == 0.0 then 1.0 / x
  else if x < 0.0 then 0.0 / 0.0
  else
    let (t0h, t0l, _) := LeanExe.loop (fx - 1.0).toUInt64
      ((1.0 : Float), (0.0 : Float), (1.0 : Float)) fun _ s =>
        let (t0h, t0l, x0) := s
        let (t0h, t0l) := mulDDD x0 t0h t0l
        (t0h, t0l, x0 + 1.0)
    t0h + t0l

/-- The underflow at or below `-184`, with the sign of `Γ x`. -/
def underflowPath (x : Float) : Float :=
  let fx := floorF x
  let tiny := Float.ofBits 0x0010000000000000
  tiny * (if (-fx).toUInt64 &&& 1 == 0 then tiny else -tiny)

/-- From `-184` to `-3`: the reflection. -/
def reflPath (dbTab accTab logTab sinTab expTab asymTab : Array UInt64) (x : Float) : Float :=
  let fx := floorF x
  let (lh, ll) := fastTwoSum (-x) 1.0
  let (lh, ll) := asLgammaAsym logTab asymTab lh ll
  let (lh, ll, e) := asExpd expTab lh ll
  let dx := x - fx
  let (sh, sl) := asSinpid sinTab dx
  let (lh, ll) := mulDD sh sl lh ll
  let pih := Float.ofBits 0x400921FB54442D18  -- 0x1.921fb54442d18p+1
  let pil := Float.ofBits 0x3CA1A62633145C07  -- 0x1.1a62633145c07p-53
  let rcp := 1.0 / lh
  let rh := rcp * pih
  let rl := rcp * (pil - ll * rh - Fma.fma rh lh (-pih))
  let odd := (-fx).toUInt64 &&& 1 == 1
  let rh := if odd then -rh else rh
  let rl := if odd then -rl else rl
  let eps := rh * (Float.ofBits 0x3BC48AD3CAEFE280 -  -- 8.7e-21
    x * Float.ofBits 0x3B661019F74442B7)  -- 1.46e-22
  if fx ≥ -170.0 then
    let ub := rh + (rl + eps)
    let lb := rh + (rl - eps)
    if ub != lb then accurate accTab dbTab x
    else Float.ofBits (ub.toBits - (e <<< 52))
  else
    let re := (rh.toBits >>> 52) &&& 0x7ff
    if nonPositive (re - e) then
      let th := (rh.toBits + ((e - re + 1) <<< 52)) &&& 0xFFF0000000000000
      let (rh, l) := fastTwoSum (Float.ofBits th) rh
      let rl := rl + l
      let ub := rh + (rl + eps)
      let lb := rh + (rl - eps)
      if ub != lb then accurate accTab dbTab x
      else Float.ofBits (ub.toBits &&& 0x800FFFFFFFFFFFFF)
    else
      let ub := rh + (rl + eps)
      let lb := rh + (rl - eps)
      if ub != lb then accurate accTab dbTab x
      else Float.ofBits (ub.toBits - (e <<< 52))

/-- From `4` to `0x1.573fae561f648p+7`: `exp (lgamma x)`. -/
def largePath (dbTab accTab logTab expTab asymTab : Array UInt64) (x : Float) : Float :=
  let (lh, ll) := asLgammaAsym logTab asymTab x 0.0
  let (lh, ll, e) := asExpd expTab lh ll
  let eps := lh * (Float.ofBits 0x3BA2E3B40A0E9B4F +  -- 2e-21
    x * Float.ofBits 0x3B6BCE27BCE24D11)  -- 1.84e-22
  let ub := lh + (ll + eps)
  let lb := lh + (ll - eps)
  if ub != lb then accurate accTab dbTab x
  else Float.ofBits (ub.toBits + (e <<< 52))

/-- From `-3` to `4`: a polynomial divided by the shifts. -/
def mainPath (dbTab accTab mainTab : Array UInt64) (x : Float) : Float :=
  let i := roundEven (x - 3.5)
  let d := x - (i + 3.5)
  let d2 := d * d
  let d4 := d2 * d2
  let fl := d * ((entry mainTab 46 + d * entry mainTab 47) +
    d2 * (entry mainTab 48 + d * entry mainTab 49) +
    d4 * ((entry mainTab 50 + d * entry mainTab 51) +
      d2 * (entry mainTab 52 + d * entry mainTab 53)))
  let (fh, fl) := polyDDD mainTab 0 10 d fl
  let jm := i.abs
  let (wh, wl, _, _) :=
    if jm > 0.0 then
      LeanExe.loop (jm - 1.0).toUInt64 (x, (0.0 : Float), x, (0.0 : Float)) fun _ s =>
        let (wh, wl, xph, xpl) := s
        let (xph, l) := if xph.abs > 1.0 then fastTwoSum xph 1.0 else fastTwoSum 1.0 xph
        let xpl := xpl + l
        let (wh, wl) := mulDD xph xpl wh wl
        (wh, wl, xph, xpl)
    else ((1.0 : Float), (0.0 : Float), x, (0.0 : Float))
  let rh := 1.0 / wh
  let (fh, fl) := mulDD rh ((Fma.fma rh (-wh) 1.0 - wl * rh) * rh) fh fl
  let eps := fh * Float.ofBits 0x3B92E3B40A0E9B4F  -- 1e-21
  let ub := fh + (fl + eps)
  let lb := fh + (fl - eps)
  if ub != lb then accurate accTab dbTab x else ub

section
variable (dbTab accTab smallTab mainTab logTab sinTab expTab asymTab : Array UInt64) (x : Float)

theorem tgamma_special (h1 : x.toBits <<< 1 ≥ 0xFFE0000000000000) :
    tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x =
      specialPath x := by
  simp only [tgammaWith, specialPath, h1, ite_true]

theorem tgamma_tiny (h1 : ¬ x.toBits <<< 1 ≥ 0xFFE0000000000000) (h2 : x.abs < 0.25)
    (h3 : x.toBits <<< 1 < 0x71E0000000000000) :
    tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x =
      tinyPath x := by
  simp only [tgammaWith, tinyPath, h1, h2, h3, ite_true, ite_false]

theorem tgamma_small (h1 : ¬ x.toBits <<< 1 ≥ 0xFFE0000000000000) (h2 : x.abs < 0.25)
    (h3 : ¬ x.toBits <<< 1 < 0x71E0000000000000) :
    tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x =
      smallPath dbTab accTab smallTab x := by
  simp only [tgammaWith, smallPath, h1, h2, h3, ite_true, ite_false]

theorem tgamma_overflow (h1 : ¬ x.toBits <<< 1 ≥ 0xFFE0000000000000) (h2 : ¬ x.abs < 0.25)
    (h4 : x ≥ Float.ofBits 0x406573FAE561F648) :
    tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x =
      overflowPath := by
  simp only [tgammaWith, overflowPath, h1, h2, h4, ite_true, ite_false]

theorem tgamma_int (h1 : ¬ x.toBits <<< 1 ≥ 0xFFE0000000000000) (h2 : ¬ x.abs < 0.25)
    (h4 : ¬ x ≥ Float.ofBits 0x406573FAE561F648) (h5 : (floorF x == x) = true) :
    tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x =
      intPath x := by
  simp only [tgammaWith, intPath, h1, h2, h4, h5, ite_true, ite_false]

theorem tgamma_underflow (h1 : ¬ x.toBits <<< 1 ≥ 0xFFE0000000000000) (h2 : ¬ x.abs < 0.25)
    (h4 : ¬ x ≥ Float.ofBits 0x406573FAE561F648) (h5 : (floorF x == x) = false)
    (h6 : x ≤ -184.0) :
    tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x =
      underflowPath x := by
  simp only [tgammaWith, underflowPath, h1, h2, h4, h5, h6, Bool.false_eq_true, ite_true,
    ite_false]

theorem tgamma_refl (h1 : ¬ x.toBits <<< 1 ≥ 0xFFE0000000000000) (h2 : ¬ x.abs < 0.25)
    (h4 : ¬ x ≥ Float.ofBits 0x406573FAE561F648) (h5 : (floorF x == x) = false)
    (h6 : ¬ x ≤ -184.0) (h7 : x < -3.0) :
    tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x =
      reflPath dbTab accTab logTab sinTab expTab asymTab x := by
  simp only [tgammaWith, reflPath, h1, h2, h4, h5, h6, h7, Bool.false_eq_true, ite_true,
    ite_false]

theorem tgamma_large (h1 : ¬ x.toBits <<< 1 ≥ 0xFFE0000000000000) (h2 : ¬ x.abs < 0.25)
    (h4 : ¬ x ≥ Float.ofBits 0x406573FAE561F648) (h5 : (floorF x == x) = false)
    (h6 : ¬ x ≤ -184.0) (h7 : ¬ x < -3.0) (h8 : x > 4.0) :
    tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x =
      largePath dbTab accTab logTab expTab asymTab x := by
  simp only [tgammaWith, largePath, h1, h2, h4, h5, h6, h7, h8, Bool.false_eq_true, ite_true,
    ite_false]

theorem tgamma_main (h1 : ¬ x.toBits <<< 1 ≥ 0xFFE0000000000000) (h2 : ¬ x.abs < 0.25)
    (h4 : ¬ x ≥ Float.ofBits 0x406573FAE561F648) (h5 : (floorF x == x) = false)
    (h6 : ¬ x ≤ -184.0) (h7 : ¬ x < -3.0) (h8 : ¬ x > 4.0) :
    tgammaWith dbTab accTab smallTab mainTab logTab sinTab expTab asymTab x =
      mainPath dbTab accTab mainTab x := by
  simp only [tgammaWith, mainPath, h1, h2, h4, h5, h6, h7, h8, Bool.false_eq_true, ite_false]

end

#print axioms tgamma_special
#print axioms tgamma_tiny
#print axioms tgamma_small
#print axioms tgamma_overflow
#print axioms tgamma_int
#print axioms tgamma_underflow
#print axioms tgamma_refl
#print axioms tgamma_large
#print axioms tgamma_main

end Verified.Examples.TgammaBranches
