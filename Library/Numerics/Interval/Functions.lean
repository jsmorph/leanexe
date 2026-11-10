import Library.Numerics.Interval.Program
import Library.Numerics.Float64.Trig.Program
import Library.Numerics.Float64.Pow.Program

/-!
Further interval operations: integer constants and their ratios, the maximum, a selection by the
sign of an interval, enclosures of `sin` and `cos` from one computed value and the Lipschitz
constant 1, and the powers `2/3`, `3/2`, and `7/2`.  `FunctionsProof.lean` proves that each result
contains the real result.
-/

namespace Library.Numerics.Interval

open Library.Numerics.Bounds Library.Numerics.Float64

/-- The interval of the integer `n`, which is exact for `|n| ≤ 2^53`. -/
def ofInt (n : Int64) : Interval := point n.toFloat

/-- An interval that contains `n / d`. -/
def ratio (n d : Int64) : Interval := div (ofInt n) (ofInt d)

/-- The doubles on each side of `π`. -/
abbrev piI : Interval := ⟨0, Float.ofBits 0x400921FB54442D18, Float.ofBits 0x400921FB54442D19⟩

/-- The squares of the points of an interval. -/
def sq (a : Interval) : Interval :=
  let b := abs a
  mul b b

/-- The maxima of the points of two intervals. -/
def imax (a b : Interval) : Interval :=
  if a.status == 0 && b.status == 0 then ⟨0, fmax a.lo b.lo, fmax a.hi b.hi⟩ else rejected

/-- `p` when `c` lies above zero and `q` when `c` lies at or below zero.  An interval `c` with
points on both sides is rejected. -/
def ifPos (c p q : Interval) : Interval :=
  if c.status == 0 then
    if 0 < c.lo then p
    else if c.hi ≤ 0 then q
    else rejected
  else rejected

/-- A float near the middle of an interval. -/
def mid (a : Interval) : Float := a.lo + (a.hi - a.lo) * 0.5

/-- An upper bound of the distance from `m` to each point of `a`. -/
def reach (a : Interval) (m : Float) : Checked :=
  let u := outSub true a.hi m
  let d := outSub true m a.lo
  if u.status == 0 && d.status == 0 then ⟨0, fmax u.value d.value⟩ else rejectedChecked

/-- The image of `a` under a function with the Lipschitz constant 1, from `fm`, a float within
one step of the nearest-even rounding of the function's value at `m`. -/
def lipschitz (a : Interval) (m fm : Float) : Interval :=
  let r := reach a m
  let l := outward2 false fm
  let h := outward2 true fm
  if r.status == 0 && l.status == 0 && h.status == 0 then
    join (a.status == 0) (outSub false l.value r.value) (outAdd true h.value r.value)
  else rejected

def sinI (inv half : Array UInt64) (a : Interval) : Interval :=
  let m := mid a
  clamp (lipschitz a m (Trig.sinWith inv half m)) (-1.0) 1.0

def cosI (inv half : Array UInt64) (a : Interval) : Interval :=
  let m := mid a
  clamp (lipschitz a m (Trig.cosWith inv half m)) (-1.0) 1.0

/-- The float four steps above `g` for `up`, and four steps below otherwise. -/
def outward4 (up : Bool) (g : Float) : Checked :=
  let e := outward2 up g
  if e.status == 0 then outward2 up e.value else rejectedChecked

/-- For `0 < g`, a float at or above `g³` for `up`, and at or below `g³` otherwise. -/
def cubeEnd (up : Bool) (g : Float) : Checked :=
  let s := outMul up g g
  if s.status == 0 then outMul up s.value g else rejectedChecked

/-- The powers `x^(2/3)` of the points of an interval above zero.  The endpoints are the values
of `pow` at the endpoints, moved four steps outward, and the operation accepts them only when
their cubes bracket the squares of the interval's endpoints, so the result does not depend on the
accuracy of `pow`. -/
def twoThirds (logTab expTab : Array UInt64) (a : Interval) : Interval :=
  if a.status == 0 then
    if 0 < a.lo then
      let gl := outward4 false (Pow.powWith logTab expTab a.lo (2.0 / 3.0))
      let gh := outward4 true (Pow.powWith logTab expTab a.hi (2.0 / 3.0))
      let cl := cubeEnd true gl.value
      let sl := outMul false a.lo a.lo
      let ch := cubeEnd false gh.value
      let sh := outMul true a.hi a.hi
      if gl.status == 0 && gh.status == 0 && cl.status == 0 && sl.status == 0 &&
          ch.status == 0 && sh.status == 0 then
        if 0 < gl.value then
          if 0 < gh.value then
            if cl.value ≤ sl.value then
              if sh.value ≤ ch.value then ⟨0, gl.value, gh.value⟩ else rejected
            else rejected
          else rejected
        else rejected
      else rejected
    else rejected
  else rejected

/-- The powers `x^(3/2)` of the points of an interval at or above zero. -/
def threeHalves (a : Interval) : Interval := mul a (sqrt a)

/-- The powers `x^(7/2)` of the points of an interval at or above zero. -/
def sevenHalves (a : Interval) : Interval := mul (mul (mul a a) a) (sqrt a)

end Library.Numerics.Interval
