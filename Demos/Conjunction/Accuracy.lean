import Demos.Conjunction.Program

/-!
The radius at a probability.  `circularError` returns an interval that contains the radius of the
disk about the origin that holds a normal error vector in the plane with probability `p`, and
`linearError` one that contains the half-width of the interval about the origin that holds a normal
error on a line with probability `p`.  Each search brackets the radius by doubling and narrows the
bracket by two bisections, one that keeps a lower end whose probability an enclosure shows below
`p` and one that keeps an upper end whose probability an enclosure shows at least `p`.  The
circular error encloses the probability with `pcWith`, and the linear error with two values of
`erf`.
-/

namespace Demos.Conjunction.Accuracy

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- The result of a search: status 0 with an interval `[lo, hi]` that contains the radius, status 1
for a rejected input, and status 2 for a search that found no upper end. -/
structure Radius where
  status : UInt64
  lo : Float
  hi : Float
  deriving Inhabited

/-- The ends of a search.  `found` is 1 when an enclosure has shown the probability at `hi` at
least `p`. -/
structure Bracket where
  found : UInt64
  lo : Float
  hi : Float
  deriving Inhabited

/-- One step of the bracketing from the enclosure `e` of the probability at the upper end of `b`:
the search ends when `e` lies at or above `p`, and otherwise the upper end grows by a factor of
1.25, and it becomes the lower end when `e` lies below `p`. -/
def growStep (p : Float) (b : Bracket) (e : Interval) : Bracket :=
  if e.status == 0 then
    if p ≤ e.lo then ⟨1, b.lo, b.hi⟩
    else if e.hi < p then ⟨0, b.hi, 1.25 * b.hi⟩
    else ⟨0, b.lo, 1.25 * b.hi⟩
  else ⟨0, b.lo, 1.25 * b.hi⟩

/-- One halving that moves the lower end to `mid` when the enclosure `e` of the probability at
`mid` lies below `p`, and the upper end otherwise. -/
def raiseStep (p : Float) (b : Bracket) (mid : Float) (e : Interval) : Bracket :=
  if e.status == 0 then
    if e.hi < p then ⟨b.found, mid, b.hi⟩ else ⟨b.found, b.lo, mid⟩
  else ⟨b.found, b.lo, mid⟩

/-- One halving that moves the upper end to `mid` when the enclosure `e` of the probability at
`mid` lies at or above `p`, and the lower end otherwise. -/
def lowerStep (p : Float) (b : Bracket) (mid : Float) (e : Interval) : Bracket :=
  if e.status == 0 then
    if p ≤ e.lo then ⟨b.found, b.lo, mid⟩ else ⟨b.found, mid, b.hi⟩
  else ⟨b.found, mid, b.hi⟩

def middle (b : Bracket) : Float := 0.5 * (b.lo + b.hi)

/-! ### The circular error -/

/-- Up to 16 steps of the bracketing from the upper end `s`, with the probability of the disk from
`pcWith`. -/
def diskGrow (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n : UInt64) (s : Float) :
    Bracket :=
  LeanExe.loop 16 ⟨0, 0.0, s⟩ fun _ b =>
    if b.found == 1 then b else growStep p b (pcWith tab m1 m2 c11 c12 c22 b.hi n)

def diskRaise (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) (b : Bracket) :
    Bracket :=
  LeanExe.loop k b fun _ e =>
    let mid := middle e
    raiseStep p e mid (pcWith tab m1 m2 c11 c12 c22 mid n)

def diskLower (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) (b : Bracket) :
    Bracket :=
  LeanExe.loop k b fun _ e =>
    let mid := middle e
    lowerStep p e mid (pcWith tab m1 m2 c11 c12 c22 mid n)

/-- The search for the radius of the disk that holds probability `p`, from the radius
`√(c11 + c22) + √(m1² + m2²)`. -/
def diskSearch (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) : Radius :=
  let g := diskGrow tab m1 m2 c11 c12 c22 p n (Float.sqrt (c11 + c22) + Float.sqrt (m1 * m1 + m2 * m2))
  if g.found == 1 then
    ⟨0, (diskRaise tab m1 m2 c11 c12 c22 p n k g).lo, (diskLower tab m1 m2 c11 c12 c22 p n k g).hi⟩
  else ⟨2, 0.0, 0.0⟩

/-- Whether the outward-rounded lower bound of the conditional variance `c22 - c12²/c11` is
positive. -/
def definite (c11 c12 c22 : Float) : Bool :=
  let s := sub (point c22) (div (sq (point c12)) (point c11))
  s.status == 0 && 0.0 < s.lo

/-- An interval that contains the radius of the disk about the origin that holds probability `p`
for the normal distribution of mean `(m1, m2)` and covariance `[[c11, c12], [c12, c22]]`, from `n`
panels for each enclosure of the probability and `k` halvings for each bisection.  The search
integrates over the coordinate of larger variance. -/
def circularErrorWith (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) :
    Radius :=
  if finite m1 && finite m2 && finite c11 && finite c12 && finite c22 && finite p then
    if 0.0 < p ∧ p < 1.0 ∧ 0.0 < c11 ∧ 0.0 < c22 ∧ 1 ≤ n ∧ n ≤ 1048576 ∧ k ≤ 64 then
      if c22 ≤ c11 then
        if definite c11 c12 c22 then diskSearch tab m1 m2 c11 c12 c22 p n k else ⟨1, 0.0, 0.0⟩
      else if definite c22 c12 c11 then diskSearch tab m2 m1 c22 c12 c11 p n k
      else ⟨1, 0.0, 0.0⟩
    else ⟨1, 0.0, 0.0⟩
  else ⟨1, 0.0, 0.0⟩

/-! ### The linear error -/

/-- The interval of `√v · √2`. -/
def lineScale (v : Float) : Interval := mul (sqrt (point v)) (sqrt (point 2.0))

/-- An interval that contains `½ [erf((L - b)/κ) + erf((L + b)/κ)]` for `κ` in `kap`, or a
rejection for a negative `L`. -/
def lineAt (tab : Array UInt64) (b : Float) (kap : Interval) (L : Float) : Interval :=
  if 0.0 ≤ L then
    mul (point 0.5) (add (erfI tab (div (sub (point L) (point b)) kap))
      (erfI tab (div (add (point L) (point b)) kap)))
  else rejected

def lineGrow (tab : Array UInt64) (b : Float) (kap : Interval) (p s : Float) : Bracket :=
  LeanExe.loop 16 ⟨0, 0.0, s⟩ fun _ g =>
    if g.found == 1 then g else growStep p g (lineAt tab b kap g.hi)

def lineRaise (tab : Array UInt64) (b : Float) (kap : Interval) (p : Float) (k : UInt64)
    (g : Bracket) : Bracket :=
  LeanExe.loop k g fun _ e =>
    let mid := middle e
    raiseStep p e mid (lineAt tab b kap mid)

def lineLower (tab : Array UInt64) (b : Float) (kap : Interval) (p : Float) (k : UInt64)
    (g : Bracket) : Bracket :=
  LeanExe.loop k g fun _ e =>
    let mid := middle e
    lowerStep p e mid (lineAt tab b kap mid)

/-- The search for the half-width that holds probability `p`, from the half-width `√v + |b|`. -/
def lineSearch (tab : Array UInt64) (b v : Float) (kap : Interval) (p : Float) (k : UInt64) :
    Radius :=
  let g := lineGrow tab b kap p (Float.sqrt v + Float.abs b)
  if g.found == 1 then
    ⟨0, (lineRaise tab b kap p k g).lo, (lineLower tab b kap p k g).hi⟩
  else ⟨2, 0.0, 0.0⟩

/-- An interval that contains the half-width of the interval about the origin that holds
probability `p` for the normal distribution of mean `b` and variance `v`, from `k` halvings for
each bisection. -/
def linearErrorWith (tab : Array UInt64) (b v p : Float) (k : UInt64) : Radius :=
  if finite b && finite v && finite p then
    if 0.0 < p ∧ p < 1.0 ∧ 0.0 < v ∧ k ≤ 64 then
      let kap := lineScale v
      if kap.status == 0 && 0.0 < kap.lo then lineSearch tab b v kap p k else ⟨1, 0.0, 0.0⟩
    else ⟨1, 0.0, 0.0⟩
  else ⟨1, 0.0, 0.0⟩

def circularError (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) : Radius :=
  circularErrorWith Exp.expTable m1 m2 c11 c12 c22 p n k

def linearError (b v p : Float) (k : UInt64) : Radius :=
  linearErrorWith Exp.expTable b v p k

end Demos.Conjunction.Accuracy
