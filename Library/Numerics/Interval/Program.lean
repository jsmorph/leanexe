import Library.Numerics.Bounds.Program

namespace Library.Numerics.Interval

open Library.Numerics.Bounds

/-- A closed interval of binary64 endpoints: status 0 with `lo` and `hi`, or status 1. -/
structure Interval where
  status : UInt64
  lo : Float
  hi : Float
  deriving Inhabited

abbrev rejected : Interval := ⟨1, 0, 0⟩

def fmin (a b : Float) : Float := if a ≤ b then a else b

def fmax (a b : Float) : Float := if a ≤ b then b else a

/-- The interval `[lo, hi]` for finite `lo ≤ hi`. -/
def make (lo hi : Float) : Interval :=
  if finite lo && finite hi then
    if lo ≤ hi then ⟨0, lo, hi⟩ else rejected
  else rejected

def point (x : Float) : Interval :=
  if finite x then ⟨0, x, x⟩ else rejected

/-- The interval of two checked endpoints, accepted when `ok` holds and both are accepted. -/
def join (ok : Bool) (l h : Checked) : Interval :=
  if ok && l.status == 0 && h.status == 0 then ⟨0, l.value, h.value⟩ else rejected

def add (a b : Interval) : Interval :=
  join (a.status == 0 && b.status == 0) (outAdd false a.lo b.lo) (outAdd true a.hi b.hi)

def sub (a b : Interval) : Interval :=
  join (a.status == 0 && b.status == 0) (outSub false a.lo b.hi) (outSub true a.hi b.lo)

def neg (a : Interval) : Interval :=
  if a.status == 0 then ⟨0, -a.hi, -a.lo⟩ else rejected

/-- The largest of four accepted values for `up`, and the smallest otherwise. -/
def extreme (up : Bool) (p q r s : Checked) : Checked :=
  if p.status == 0 && q.status == 0 && r.status == 0 && s.status == 0 then
    if up then ⟨0, fmax (fmax p.value q.value) (fmax r.value s.value)⟩
    else ⟨0, fmin (fmin p.value q.value) (fmin r.value s.value)⟩
  else rejectedChecked

def mulEnd (up : Bool) (a b : Interval) : Checked :=
  extreme up (outMul up a.lo b.lo) (outMul up a.lo b.hi) (outMul up a.hi b.lo)
    (outMul up a.hi b.hi)

def mul (a b : Interval) : Interval :=
  join (a.status == 0 && b.status == 0) (mulEnd false a b) (mulEnd true a b)

def divEnd (up : Bool) (a b : Interval) : Checked :=
  extreme up (outDiv up a.lo b.lo) (outDiv up a.lo b.hi) (outDiv up a.hi b.lo)
    (outDiv up a.hi b.hi)

def divCore (a b : Interval) : Interval :=
  join (a.status == 0 && b.status == 0) (divEnd false a b) (divEnd true a b)

/-- The quotient by an interval that lies above zero or below it. -/
def div (a b : Interval) : Interval :=
  if 0 < b.lo then divCore a b
  else if b.hi < 0 then divCore a b
  else rejected

def sqrt (a : Interval) : Interval :=
  join (a.status == 0) (outSqrt false a.lo) (outSqrt true a.hi)

def abs (a : Interval) : Interval :=
  if a.status == 0 then
    if 0 ≤ a.lo then a
    else if a.hi ≤ 0 then ⟨0, -a.hi, -a.lo⟩
    else ⟨0, 0, fmax (-a.lo) a.hi⟩
  else rejected

/-- The part of `a` between `lo` and `hi`. -/
def clamp (a : Interval) (lo hi : Float) : Interval :=
  if a.status == 0 && finite lo && finite hi then ⟨0, fmax a.lo lo, fmin a.hi hi⟩
  else rejected

/-- A value moved two steps up or down, when every step is finite. -/
def outward2 (up : Bool) (w : Float) : Checked :=
  let e := endpoint up w
  if e.status == 0 then endpoint up e.value else rejectedChecked

/-- The image of `a` under an increasing function from its computed values `flo` at `a.lo` and
`fhi` at `a.hi`, each within one step of the nearest-even rounding of the real value. -/
def increasing (a : Interval) (flo fhi : Float) : Interval :=
  join (a.status == 0) (outward2 false flo) (outward2 true fhi)

/-- The image of `a` under a decreasing function, with `flo` and `fhi` as for `increasing`. -/
def decreasing (a : Interval) (flo fhi : Float) : Interval :=
  join (a.status == 0) (outward2 false fhi) (outward2 true flo)

end Library.Numerics.Interval
