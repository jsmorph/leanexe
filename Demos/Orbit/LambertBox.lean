import Demos.Orbit.GibbsBox
import Demos.Orbit.LambertRoot
import Library.Numerics.Float64.Asin.Program
import Library.Numerics.Float64.Log.Program
import LeanExe.Dialect.Loop

/-!
The interval program of Lambert's problem in Izzo's formulation.  `geometry` states `λ` and the
nondimensional time `T`, and `velocities` states Izzo's velocity formulas, each with
`enclosure_def`.  `tofI` encloses `tof lam m` at a binary64 point `m > -1` for every `λ` in an
interval, from the library's `acos` and `log`.  `lambertBox` checks the inputs, the direction of
motion, and the brackets `a0 = -1 + 2^-52` and `b0 = 1 + 4/T`, runs two bisections of at most
256 steps, one that raises a point where `tofI` shows `T(a) > T` and one that lowers a point where
it shows `T(b) < T`, and evaluates the velocities with `x` in `[a, b]`.

| Status | Meaning |
|---|---|
| 0 | The interval of `x` contains the root, and the six intervals contain Izzo's velocities. |
| 1 | An input interval is not accepted or not finite, has `lo > hi`, or `t`'s or `μ`'s does not lie above zero, or a component of `k` is not finite. |
| 2 | The interval of `(r1 × r2) · k` contains zero, or an interval operation rejected. |
| 3 | `tofI` does not show `T(a0) > T` and `T(b0) < T`. |
| 4 | A bisection reached 256 steps without finishing. |
-/

namespace Demos.Orbit

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-! ### The formulas -/

/-- `(r1 × r2) · k`. -/
enclosure_def direction (x1 y1 z1 x2 y2 z2 kx ky kz) :=
  (y1 * z2 - z1 * y2) * kx + (z1 * x2 - x1 * z2) * ky + (x1 * y2 - y1 * x2) * kz

/-- Izzo's `λ = ±√(1 - c/s)`, with the sign `sg`, and `T = √(2μ/s³) t`. -/
enclosure_def geometry (x1 y1 z1 x2 y2 z2 t mu sg) :=
  let n1 := lengthOf x1 y1 z1
  let n2 := lengthOf x2 y2 z2
  let c := lengthOf (x2 - x1) (y2 - y1) (z2 - z1)
  let s := (n1 + n2 + c) / 2
  (sg * √(max (1 - c / s) 0), √(2 * mu / (s * s * s)) * t)

/-- The radial components at `r1` and `r2` and `γ σ (y + λ x)`, from `n1`, `n2`, `c`, `s`, `μ`,
the sign `sg`, and `x`. -/
enclosure_def components (n1 n2 c s mu sg xx) :=
  let lam := sg * √(max (1 - c / s) 0)
  let y := √(max (1 - sqr lam * (1 - sqr xx)) 0)
  let gamma := √(mu * s / 2)
  let rho := (n1 - n2) / c
  let sigma := √(max (1 - sqr rho) 0)
  (gamma * ((lam * y - xx) - rho * (lam * y + xx)) / n1,
    -(gamma * ((lam * y - xx) + rho * (lam * y + xx))) / n2,
    gamma * sigma * (y + lam * xx))

/-- Izzo's velocities at `r1` and `r2` for the parameter `x`:
`v1 = vr1 r1/n1 + vt1 ĥ × r1/n1` and `v2 = vr2 r2/n2 + vt2 ĥ × r2/n2`, with
`ĥ = sg (r1 × r2)/|r1 × r2|`. -/
enclosure_def velocities (x1 y1 z1 x2 y2 z2 mu sg xx) :=
  let n1 := lengthOf x1 y1 z1
  let n2 := lengthOf x2 y2 z2
  let c := lengthOf (x2 - x1) (y2 - y1) (z2 - z1)
  let s := (n1 + n2 + c) / 2
  let (vr1, vr2, vt) := components n1 n2 c s mu sg xx
  let (wx, wy, wz) := crossOf x1 y1 z1 x2 y2 z2
  let wn := lengthOf wx wy wz
  let (px, py, pz) := crossOf wx wy wz x1 y1 z1
  let (qx, qy, qz) := crossOf wx wy wz x2 y2 z2
  let f1 := sg * vt / (n1 * n1 * wn)
  let f2 := sg * vt / (n2 * n2 * wn)
  let a1 := vr1 / n1
  let a2 := vr2 / n2
  (a1 * x1 + f1 * px, a1 * y1 + f1 * py, a1 * z1 + f1 * pz,
    a2 * x2 + f2 * qx, a2 * y2 + f2 * qy, a2 * z2 + f2 * qz)

/-! ### The time of flight on intervals -/

/-- The interval of the integer 1. -/
def oneI : Interval := ofInt 1

/-- An interval that contains `arccos z` for every `z` of `a` in `[-1, 1]`. -/
def acosI (a : Interval) : Interval :=
  let b := clamp a (-1.0) 1.0
  decreasing b (Asin.acos b.lo) (Asin.acos b.hi)

/-- An interval that contains `log z` for every `z` of an interval above zero. -/
def logI (tab tab2 : Array UInt64) (a : Interval) : Interval :=
  if 0 < a.lo then increasing a (Log.logWith tab tab2 a.lo) (Log.logWith tab tab2 a.hi)
  else rejected

/-- An interval that contains `arcosh z = log(z + √(z² - 1))` for every `z` of `a`. -/
def arcoshI (tab tab2 : Array UInt64) (a : Interval) : Interval :=
  logI tab tab2 (add a (sqrt (imax (sub (sq a) oneI) (ofInt 0))))

/-- An interval that contains `tof lam (value m)` for every `lam` of `l`, for `m > -1`. -/
def tofI (tab tab2 : Array UInt64) (l : Interval) (m : Float) : Interval :=
  let x := point m
  if m < 1.0 then
    let w := mul (sub oneI x) (add oneI x)
    let y := sqrt (imax (sub oneI (mul (sq l) w)) (ofInt 0))
    let psi := acosI (add (mul x y) (mul l w))
    div (add (sub (div psi (sqrt w)) x) (mul l y)) w
  else if 1.0 < m then
    let v := mul (sub x oneI) (add x oneI)
    let y := sqrt (add oneI (mul (sq l) v))
    let psi := arcoshI tab tab2 (sub (mul x y) (mul l v))
    div (add (sub (div psi (sqrt v)) x) (mul l y)) (neg v)
  else mul (ratio 2 3) (sub oneI (mul (sq l) l))

/-- `tofI` shows `T(m) > T` for every point of the intervals. -/
def above (tab tab2 : Array UInt64) (l tt : Interval) (m : Float) : Bool :=
  let v := tofI tab tab2 l m
  v.status == 0 && tt.hi < v.lo

/-- `tofI` shows `T(m) < T` for every point of the intervals. -/
def below (tab tab2 : Array UInt64) (l tt : Interval) (m : Float) : Bool :=
  let v := tofI tab tab2 l m
  v.status == 0 && v.hi < tt.lo

/-! ### The bisections -/

/-- The state of a bisection: the two points and whether the search has finished. -/
structure Search where
  a : Float
  b : Float
  done : Bool
  deriving Inhabited

/-- The midpoint of a search. -/
def midpoint (s : Search) : Float := s.a + (s.b - s.a) * 0.5

/-- `1 - 2^-20` and `1 + 2^-20`. -/
def belowOne : Float := Float.ofBits 0x3FEFFFFE00000000

def aboveOne : Float := Float.ofBits 0x3FF0000010000000

/-- The point that a step evaluates: the midpoint, or `1 - 2^-20` or `1 + 2^-20` when the
midpoint lies within `2^-20` of 1 and that point lies between the two points of the search.
Near 1 the closed forms of `T` lose their precision, and an evaluation there that decides
neither side would move the search away from the root. -/
def probe (s : Search) : Float :=
  let m := midpoint s
  if belowOne < m ∧ m < aboveOne then
    if s.a < belowOne then belowOne
    else if aboveOne < s.b then aboveOne
    else m
  else m

/-- A step of the bisection that raises `a`, the point where `T(a) > T` holds. -/
def raiseStep (tab tab2 : Array UInt64) (l tt : Interval) (s : Search) : Search :=
  if s.done then s
  else
    let m := probe s
    if finite m then
      if s.a < m ∧ m < s.b then
        if above tab tab2 l tt m then ⟨m, s.b, false⟩ else ⟨s.a, m, false⟩
      else ⟨s.a, s.b, true⟩
    else ⟨s.a, s.b, true⟩

/-- A step of the bisection that lowers `b`, the point where `T(b) < T` holds. -/
def lowerStep (tab tab2 : Array UInt64) (l tt : Interval) (s : Search) : Search :=
  if s.done then s
  else
    let m := probe s
    if finite m then
      if s.a < m ∧ m < s.b then
        if below tab tab2 l tt m then ⟨s.a, m, false⟩ else ⟨m, s.b, false⟩
      else ⟨s.a, s.b, true⟩
    else ⟨s.a, s.b, true⟩

def raise (tab tab2 : Array UInt64) (l tt : Interval) (a b : Float) : Search :=
  LeanExe.loop 256 ⟨a, b, false⟩ fun _ s => raiseStep tab tab2 l tt s

def lower (tab tab2 : Array UInt64) (l tt : Interval) (a b : Float) : Search :=
  LeanExe.loop 256 ⟨a, b, false⟩ fun _ s => lowerStep tab tab2 l tt s

/-! ### The program -/

/-- A status, the interval of `x`, and the intervals of the velocities at `r1` and `r2`. -/
structure Transfer where
  status : UInt64
  x : Interval
  v1x : Interval
  v1y : Interval
  v1z : Interval
  v2x : Interval
  v2y : Interval
  v2z : Interval
  deriving Inhabited

/-- A status without intervals. -/
def noTransfer (status : UInt64) : Transfer :=
  ⟨status, rejected, rejected, rejected, rejected, rejected, rejected, rejected⟩

/-- `-1 + 2^-52`. -/
def startLow : Float := Float.ofBits 0xBFEFFFFFFFFFFFFE

/-- The point interval of the sign of the direction of motion, from the interval of
`(r1 × r2) · k`. -/
def signOf (d : Interval) : Interval := if 0 < d.lo then oneI else neg oneI

/-- The search and the velocities, for the sign `sg`, `λ` in `l`, and `T` in `tt`. -/
def solve (tab tab2 : Array UInt64) (x1 y1 z1 x2 y2 z2 mu sg l tt : Interval) : Transfer :=
  let a0 := startLow
  let b0 := 1.0 + 4.0 / tt.lo
  if finite a0 && finite b0 then
    if -1.0 < a0 ∧ -1.0 < b0 then
      if above tab tab2 l tt a0 && below tab tab2 l tt b0 then
        let ra := raise tab tab2 l tt a0 b0
        let lb := lower tab tab2 l tt a0 b0
        if ra.done && lb.done then
          let xx := make ra.a lb.b
          let v := velocitiesI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 mu sg xx
          if xx.status == 0 && v.1.status == 0 && v.2.1.status == 0 &&
              v.2.2.1.status == 0 && v.2.2.2.1.status == 0 && v.2.2.2.2.1.status == 0 &&
              v.2.2.2.2.2.status == 0 then
            ⟨0, xx, v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩
          else noTransfer 2
        else noTransfer 4
      else noTransfer 3
    else noTransfer 3
  else noTransfer 3

/-- Lambert's problem on boxes of the two positions, intervals of the time of flight and `μ`,
and the axis `k` of the direction of motion. -/
def lambertBoxWith (tab tab2 : Array UInt64) (x1 y1 z1 x2 y2 z2 t mu : Interval)
    (kx ky kz : Float) : Transfer :=
  if valid x1 && valid y1 && valid z1 && valid x2 && valid y2 && valid z2 && valid t &&
      valid mu && finite kx && finite ky && finite kz then
    if 0 < t.lo ∧ 0 < mu.lo then
      let d := directionI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 (point kx)
        (point ky) (point kz)
      if d.status = 0 ∧ (0 < d.lo ∨ d.hi < 0) then
        let sg := signOf d
        let g := geometryI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 t mu sg
        if g.1.status == 0 && g.2.status == 0 then
          if 0 < g.2.lo then solve tab tab2 x1 y1 z1 x2 y2 z2 mu sg g.1 g.2
          else noTransfer 2
        else noTransfer 2
      else noTransfer 2
    else noTransfer 1
  else noTransfer 1

def lambertBox (x1 y1 z1 x2 y2 z2 t mu : Interval) (kx ky kz : Float) : Transfer :=
  lambertBoxWith Log.logTable Log.logTable2 x1 y1 z1 x2 y2 z2 t mu kx ky kz

def lambertBoundsWith (tab tab2 : Array UInt64) (x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo
    y2hi z2lo z2hi tlo thi mulo muhi kx ky kz : Float) : Transfer :=
  lambertBoxWith tab tab2 (make x1lo x1hi) (make y1lo y1hi) (make z1lo z1hi) (make x2lo x2hi)
    (make y2lo y2hi) (make z2lo z2hi) (make tlo thi) (make mulo muhi) kx ky kz

/-- `lambertBox` on the intervals between the given endpoints. -/
def lambertBounds (x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi mulo muhi
    kx ky kz : Float) : Transfer :=
  lambertBoundsWith Log.logTable Log.logTable2 x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi
    z2lo z2hi tlo thi mulo muhi kx ky kz

end Demos.Orbit
