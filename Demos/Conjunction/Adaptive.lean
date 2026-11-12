import Demos.Conjunction.Accuracy

/-!
The probability of the disk and the circular error with adaptive panels.  `march` covers `[-r, r]`
from the left with panels whose lengths follow the integrand: it accepts a panel whose interval is
at most a tolerance wide and otherwise shortens the panel, and it predicts the next length from
the width, which falls as the square of the length where the integrand is smooth.  Its last
permitted step covers the rest of `[-r, r]` with one panel.  `pcAdaptWith` runs a coarse march, a
second march at the tolerance that the first's widths predict for about `n/16` panels, and a third
at the tolerance that the second's widths predict for the remaining panels, and it returns the
part common to the second and third sums times the constant factor.  `circularErrorAdaptWith` is
the search of `circularErrorWith` with `pcAdaptWith` in place of `pcWith`.
-/

namespace Demos.Conjunction.Adaptive

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open Demos.Conjunction Demos.Conjunction.Accuracy

/-- The state of a march over `[-r, r]`.  `state` is 0 while the march runs, 1 once it covers
`[-r, r]`, and 2 after a rejected panel; `used` counts the panels evaluated; `root` adds the square
roots of the widths of the accepted panels; `sum` encloses the integral over the covered part
`[-r, t]`; and `h` is the length of the next panel. -/
structure March where
  state : UInt64
  used : UInt64
  root : Float
  t : Float
  h : Float
  sum : Interval
  deriving Inhabited

/-- `2^-40`, the ratio of the length below which a march accepts any panel to `r`. -/
abbrev minRatio : Float := Float.ofBits 0x3D70000000000000

/-- The end of the panel of length `h` from `t`: `t + h` when it is finite and below `r`, and `r`
otherwise. -/
def panelEnd (r t h : Float) : Float :=
  let s := t + h
  if finite s && s < r then s else r

/-- The ratio of the next length to the current one after a panel of width `w` for the tolerance
`tau`: `0.9 √(tau / w)` between 0.25 and 2, and 2 when `w` is not positive. -/
def stepRatio (tau w : Float) : Float :=
  if 0.0 < w then fmin 2.0 (fmax 0.25 (0.9 * Float.sqrt (tau / w))) else 2.0

/-- The state after the panel `e` from `m.t` to `b` is accepted, with the next length `h`. -/
def accept (r b h : Float) (m : March) (e : Interval) : March :=
  ⟨if b < r then 0 else 1, m.used + 1, m.root + Float.sqrt (e.hi - e.lo), b, h, add m.sum e⟩

/-- One step of a march with the tolerance `tau` and `fuel` steps.  The last step accepts the
panel from `m.t` to `r`.  Another step evaluates the panel of length `m.h`, accepts it when its
width is at most `tau` or its length at most `hmin`, shortens the next panel otherwise, and stops
the march at a rejected panel. -/
def marchStep (tab : Array UInt64) (st : Setup) (r tau hmin : Float) (fuel : UInt64)
    (m : March) : March :=
  if m.used + 1 < fuel then
    let b := panelEnd r m.t m.h
    let e := panel tab st m.t b
    if e.status == 0 && m.t ≤ b then
      let w := e.hi - e.lo
      if w ≤ tau then accept r b (m.h * stepRatio tau w) m e
      else if b - m.t ≤ hmin then accept r b m.h m e
      else ⟨0, m.used + 1, m.root, m.t, m.h * stepRatio tau w, m.sum⟩
    else ⟨2, m.used + 1, m.root, m.t, m.h, m.sum⟩
  else accept r r m.h m (panel tab st m.t r)

/-- A march over `[-r, r]` with the tolerance `tau` and at most `fuel` panels, from the length
`r/8`. -/
def march (tab : Array UInt64) (st : Setup) (r tau : Float) (fuel : UInt64) : March :=
  LeanExe.loop fuel ⟨0, 0, 0.0, -r, 0.125 * r, point 0.0⟩ fun _ m =>
    if m.state == 0 then marchStep tab st r tau (r * minRatio) fuel m else m

/-- The tolerance at which a march takes about `k` panels, from the square roots of the widths of
the accepted panels of the march `m`: a panel of width `w` at the tolerance `tau` splits into about
`√(w / tau)` panels. -/
def tolerance (m : March) (k : Float) : Float :=
  let q := m.root / fmax 1.0 k
  q * q

/-- The part common to two intervals, or one of them when the other is rejected. -/
def meet (a b : Interval) : Interval :=
  if a.status == 0 then
    if b.status == 0 then make (fmax a.lo b.lo) (fmin a.hi b.hi) else a
  else b

/-- An interval that contains the probability of the disk of radius `r` for the mean `(m1, m2)`
and the covariance `[[c11, c12], [c12, c22]]`, from at most `n` panels placed by three marches. -/
def pcAdaptWith (tab : Array UInt64) (m1 m2 c11 c12 c22 r : Float) (n : UInt64) : Interval :=
  if 0.0 < c11 then
    if 0.0 < r then
      if finite r then
        if 16 ≤ n then
          if n ≤ 1048576 then
            let st := setup m1 m2 c11 c12 c22 r
            let a := march tab st r (0.015625 * r) (n / 16)
            let b := march tab st r (tolerance a (n / 16).toFloat) (n / 2 - a.used)
            let left := n - a.used - b.used
            let c := march tab st r (tolerance b (0.8 * left.toFloat)) left
            let s := meet (if b.state == 1 then b.sum else rejected)
              (if c.state == 1 then c.sum else rejected)
            let p := mul (div (point 1.0) (mul (point 2.0) (sqrt (mul twoPi (point c11))))) s
            clamp p 0.0 p.hi
          else rejected
        else rejected
      else rejected
    else rejected
  else rejected

/-! ### The circular error -/

def adaptGrow (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n : UInt64) (s : Float) :
    Bracket :=
  LeanExe.loop 16 ⟨0, 0.0, s⟩ fun _ b =>
    if b.found == 1 then b else growStep p b (pcAdaptWith tab m1 m2 c11 c12 c22 b.hi n)

def adaptRaise (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) (b : Bracket) :
    Bracket :=
  LeanExe.loop k b fun _ e =>
    let mid := middle e
    raiseStep p e mid (pcAdaptWith tab m1 m2 c11 c12 c22 mid n)

def adaptLower (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) (b : Bracket) :
    Bracket :=
  LeanExe.loop k b fun _ e =>
    let mid := middle e
    lowerStep p e mid (pcAdaptWith tab m1 m2 c11 c12 c22 mid n)

/-- The search of `diskSearch` with the enclosure `pcAdaptWith`. -/
def adaptSearch (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) : Radius :=
  let g := adaptGrow tab m1 m2 c11 c12 c22 p n
    (Float.sqrt (c11 + c22) + Float.sqrt (m1 * m1 + m2 * m2))
  if g.found == 1 then
    ⟨0, (adaptRaise tab m1 m2 c11 c12 c22 p n k g).lo, (adaptLower tab m1 m2 c11 c12 c22 p n k g).hi⟩
  else ⟨2, 0.0, 0.0⟩

/-- An interval that contains the radius of the disk about the origin that holds probability `p`
for the normal distribution of mean `(m1, m2)` and covariance `[[c11, c12], [c12, c22]]`, from at
most `n` panels for each enclosure of the probability and `k` halvings for each bisection.  The
search integrates over the coordinate of larger variance. -/
def circularErrorAdaptWith (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) :
    Radius :=
  if finite m1 && finite m2 && finite c11 && finite c12 && finite c22 && finite p then
    if 0.0 < p ∧ p < 1.0 ∧ 0.0 < c11 ∧ 0.0 < c22 ∧ 16 ≤ n ∧ n ≤ 1048576 ∧ k ≤ 64 then
      if c22 ≤ c11 then
        if definite c11 c12 c22 then adaptSearch tab m1 m2 c11 c12 c22 p n k else ⟨1, 0.0, 0.0⟩
      else if definite c22 c12 c11 then adaptSearch tab m2 m1 c22 c12 c11 p n k
      else ⟨1, 0.0, 0.0⟩
    else ⟨1, 0.0, 0.0⟩
  else ⟨1, 0.0, 0.0⟩

def pcAdaptive (m1 m2 c11 c12 c22 r : Float) (n : UInt64) : Interval :=
  pcAdaptWith Exp.expTable m1 m2 c11 c12 c22 r n

def circularErrorAdaptive (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) : Radius :=
  circularErrorAdaptWith Exp.expTable m1 m2 c11 c12 c22 p n k

end Demos.Conjunction.Adaptive
