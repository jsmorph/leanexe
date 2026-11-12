import Library.Numerics.Interval.Program
import Library.Numerics.Float64.Erf.Program
import LeanExe.Dialect.Loop

/-!
The two-dimensional probability of collision as an interval.  `pcWith` splits `[-r, r]` into `n`
panels, encloses the integrand on each panel with the interval operations, and sums the panels'
contributions.  `assessWith` compares the interval with a threshold.  `pc` and `assess` pass the
table of Arm's `exp`, which the library's `erf` also uses.
-/

namespace Demos.Conjunction

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- The doubles on each side of `2π`. -/
abbrev twoPi : Interval :=
  ⟨0, Float.ofBits 0x401921FB54442D18, Float.ofBits 0x401921FB54442D19⟩

/-- The squares of the points of an interval. -/
def sq (a : Interval) : Interval :=
  let b := abs a
  mul b b

def expI (tab : Array UInt64) (a : Interval) : Interval :=
  increasing a (Exp.expWith tab a.lo) (Exp.expWith tab a.hi)

def erfI (tab : Array UInt64) (a : Interval) : Interval :=
  increasing a (Erf.erfWith tab a.lo) (Erf.erfWith tab a.hi)

/-- The quantities that every panel uses: the mean, twice the first variance, the slope of the
conditional mean, the scale of the error-function arguments, and the squared radius. -/
structure Setup where
  m1 : Interval
  m2 : Interval
  twoC11 : Interval
  rho : Interval
  k : Interval
  r2 : Interval
  deriving Inhabited

def setup (m1 m2 c11 c12 c22 r : Float) : Setup :=
  let c := point c11
  { m1 := point m1
    m2 := point m2
    twoC11 := mul (point 2.0) c
    rho := div (point c12) c
    k := mul (sqrt (sub (point c22) (div (sq (point c12)) c))) (sqrt (point 2.0))
    r2 := sq (point r) }

/-- The exponential factor `exp (-(x - m1)² / (2 c11))` for `x` in the interval. -/
def gaussI (tab : Array UInt64) (st : Setup) (x : Interval) : Interval :=
  clamp (expI tab (neg (div (sq (sub x st.m1)) st.twoC11))) 0.0 1.0

/-- The half-chord `√(r² - x²)` of the disk. -/
def chordI (st : Setup) (x : Interval) : Interval :=
  sqrt (clamp (sub st.r2 (sq x)) 0.0 st.r2.hi)

/-- The conditional mean of the second coordinate. -/
def meanI (st : Setup) (x : Interval) : Interval :=
  add st.m2 (mul st.rho (sub x st.m1))

/-- The sum of the two error-function values. -/
def erfSumI (tab : Array UInt64) (st : Setup) (x : Interval) : Interval :=
  let h := chordI st x
  let mu := meanI st x
  clamp (add (erfI tab (div (sub h mu) st.k)) (erfI tab (div (add h mu) st.k))) 0.0 2.0

/-- The integrand without its constant factor, for the first coordinate in `x`. -/
def panelCore (tab : Array UInt64) (st : Setup) (x : Interval) : Interval :=
  mul (gaussI tab st x) (erfSumI tab st x)

/-- The computed partition point `i` of `[-r, r]` into `n` panels. -/
def nodeRaw (r : Float) (n i : UInt64) : Float :=
  -r + (2.0 * r) * (i.toFloat / n.toFloat)

/-- Partition point `i` of `[-r, r]` into `n` panels: `-r` for `i = 0`, `r` from `i = n` on, and
the computed point between them when it is finite and lies in `[-r, r]`. -/
def node (r : Float) (n i : UInt64) : Float :=
  if i == 0 then -r
  else if n ≤ i then r
  else
    let t := nodeRaw r n i
    if finite t then
      if -r ≤ t then
        if t ≤ r then t else r
      else r
    else r

def panel (tab : Array UInt64) (st : Setup) (a b : Float) : Interval :=
  mul (sub (point b) (point a)) (panelCore tab st (make a b))

/-- The sum of the panels' contributions. -/
def panels (tab : Array UInt64) (st : Setup) (r : Float) (n : UInt64) : Interval :=
  LeanExe.loop n (point 0.0) fun i acc =>
    add acc (panel tab st (node r n i) (node r n (i + 1)))

/-- An interval that contains the probability of collision for the mean `(m1, m2)`, the
covariance `[[c11, c12], [c12, c22]]`, and the radius `r`, from `n` panels. -/
def pcWith (tab : Array UInt64) (m1 m2 c11 c12 c22 r : Float) (n : UInt64) : Interval :=
  if 0.0 < c11 then
    if 0.0 < r then
      if 1 ≤ n then
        if n ≤ 1048576 then
          let p := mul (div (point 1.0) (mul (point 2.0) (sqrt (mul twoPi (point c11)))))
            (panels tab (setup m1 m2 c11 c12 c22 r) r n)
          clamp p 0.0 1.0
        else rejected
      else rejected
    else rejected
  else rejected

/-- The interval of `pcWith` and its comparison with a threshold: verdict 1 when the interval
lies below `t`, 2 when it lies at or above `t`, and 0 otherwise. -/
structure Assessment where
  status : UInt64
  lo : Float
  hi : Float
  verdict : UInt64
  deriving Inhabited

def assessWith (tab : Array UInt64) (m1 m2 c11 c12 c22 r t : Float) (n : UInt64) : Assessment :=
  let p := pcWith tab m1 m2 c11 c12 c22 r n
  if p.status == 0 && finite t then
    if p.hi < t then ⟨0, p.lo, p.hi, 1⟩
    else if t ≤ p.lo then ⟨0, p.lo, p.hi, 2⟩
    else ⟨0, p.lo, p.hi, 0⟩
  else ⟨1, 0.0, 0.0, 0⟩

def pc (m1 m2 c11 c12 c22 r : Float) (n : UInt64) : Interval :=
  pcWith Exp.expTable m1 m2 c11 c12 c22 r n

def assess (m1 m2 c11 c12 c22 r t : Float) (n : UInt64) : Assessment :=
  assessWith Exp.expTable m1 m2 c11 c12 c22 r t n

end Demos.Conjunction
