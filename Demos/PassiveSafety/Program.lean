import Demos.PassiveSafety.Closed
import LeanExe.Dialect.Loop
import LeanExe.Dialect.RepeatWhile

/-!
The passive-safety check of `requirements.md`.  `checkWith` validates the input, and for each
scenario of the plan it runs `sepSearch`, which covers the horizon with panels of time on which
the interval of the squared separation lies at or above the squared threshold, and `rcSearch`,
which covers one period after the scenario's last burn, by the phases `[0, 2π]`, with panels on
which the interval of the squared radial and cross-track distance does.  Both searches step by
`march`, which also refines a panel until the root of its lower end is at least the root of the
least lower end at a midpoint less the accuracy.  A panel's interval is the Taylor form of
`smoothSep` or `smoothRc`, or the natural form of `positionI` on a separation panel that contains
a burn time.  The interval functions of `Closed.lean` take the tables of `pow` as well as those
of `sin` and `cos`, use no power, and receive the tables of `sin` and `cos` in their place.
-/

namespace Demos.PassiveSafety

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- The result of a check: the status of `requirements.md`, the scenario and the panel's start at
which a search failed, and the bounds of the separation and of the radial and cross-track
distance. -/
structure Result where
  status : UInt64
  scenario : UInt64
  stop : Float
  sep : Float
  rc : Float
  deriving Inhabited

/-- The state of a search: 0 while it runs, 1 when a panel at the smallest step fails its test,
and 3 when an interval operation rejects; the covered part `[0, t]`, the step, the least lower
end of the accepted panels, and the least lower end of the midpoint intervals, `M` of
`requirements.md`. -/
structure March where
  status : UInt64
  t : Float
  h : Float
  low : Float
  best : Float
  deriving Inhabited

/-- The largest finite double. -/
abbrev maxFloat : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF

/-- The double just above `2π`, the end of the phases. -/
abbrev twoPiHi : Float := Float.ofBits 0x401921FB54442D19

/-- `2^-40`, the ratio of the smallest step of a search to its length. -/
abbrev minRatio : Float := Float.ofBits 0x3D70000000000000

/-- Value `i` of the input. -/
@[inline] def rd (xs : Array Float) (i : UInt64) : Float := xs[i.toNat]!

/-- The interval of values `i` and `i + 1` of the input. -/
def box (xs : Array Float) (i : UInt64) : Interval := make (rd xs i) (rd xs (i + 1))

/-- The position of the first value of burn `k`, counted from 0. -/
@[inline] def burnAt (k : UInt64) : UInt64 := 16 + 7 * k

/-- Whether burn `k`, counted from 0, executes in scenario `j` of a plan of `N` burns. -/
def runs (N j k : UInt64) : Bool :=
  if j == 0 then true else if j ≤ N then k + 1 != j else k + 1 < j - N

/-- The end of the panel that starts at `t` with step `h`: `t + h` when it is finite and at most
`e`, and `e` otherwise. -/
def panelEnd (t h e : Float) : Float :=
  let b := t + h
  if finite b && b ≤ e then b else e

/-- The record `best` lowered by the lower end of the midpoint interval `w`, when `w` is
accepted. -/
def record (best : Float) (w : Interval) : Float :=
  if w.status == 0 then fmin best w.lo else best

/-- Whether a search accepts the panel interval `v` at the step `h`: its lower end is at least
`d2`, and at least the target `(√best − acc)²` of the accuracy unless `h` is at most `hmin`. -/
def accepts (d2 hmin acc best : Float) (v : Interval) (h : Float) : Bool :=
  let r := best.sqrt - acc
  let target := if 0.0 < r then r * r else 0.0
  d2 ≤ v.lo && (target ≤ v.lo || h ≤ hmin)

/-- One step of a search of `[0, e]` against the bound `d2` and the accuracy `acc`, with `v` the
interval of the panel `[m.t, b]` and `w` the interval at its midpoint, which lowers the record
`best`.  A panel that `accepts` extends the covered part and doubles the step up to `e`, and
another panel halves the step or ends the search.  A rejected interval, or a panel end below its
start, ends the search with status 3. -/
def march (e d2 hmin acc : Float) (v w : Interval) (b : Float) (m : March) : March :=
  if v.status == 0 && m.t ≤ b then
    let best := record m.best w
    if accepts d2 hmin acc best v m.h then
      let h2 := m.h * 2.0
      ⟨0, b, if h2 ≤ e then h2 else e, fmin m.low v.lo, best⟩
    else if m.h ≤ hmin then ⟨1, m.t, m.h, m.low, best⟩
    else ⟨0, m.t, m.h * 0.5, m.low, best⟩
  else ⟨3, m.t, m.h, m.low, m.best⟩

/-- The part of `v` at or above 0, for an interval of a quantity that is never negative. -/
def nonneg (v : Interval) : Interval := clamp v 0.0 v.hi

/-- The position of every trajectory of scenario `j` from the boxes, at every time of `tI`. -/
def positionI (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (tI : Interval) :
    Interval × Interval × Interval :=
  let n := point (rd xs 0)
  let z := point 0.0
  let p0 := flowPositionI inv half inv half n tI (box xs 4) (box xs 6) (box xs 8) (box xs 10)
    (box xs 12) (box xs 14)
  LeanExe.loop N p0 fun k acc =>
    if runs N j k then
      let i := burnAt k
      let d := imax (sub tI (point (rd xs i))) z
      let q := flowPositionI inv half inv half n d z z z (box xs (i + 1)) (box xs (i + 3))
        (box xs (i + 5))
      (add acc.1 q.1, add acc.2.1 q.2.1, add acc.2.2 q.2.2)
    else acc

/-- The velocity of every trajectory of scenario `j` from the boxes at every time of `tI`, with
the terms of the burns of the scenario at or before `start`. -/
def velocityI (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (start : Float)
    (tI : Interval) : Interval × Interval × Interval :=
  let n := point (rd xs 0)
  let z := point 0.0
  let v0 := flowVelocityI inv half inv half n tI (box xs 4) (box xs 8) (box xs 10) (box xs 12)
    (box xs 14)
  LeanExe.loop N v0 fun k acc =>
    let i := burnAt k
    if runs N j k && rd xs i ≤ start then
      let q := flowVelocityI inv half inv half n (sub tI (point (rd xs i))) z z (box xs (i + 1))
        (box xs (i + 3)) (box xs (i + 5))
      (add acc.1 q.1, add acc.2.1 q.2.1, add acc.2.2 q.2.2)
    else acc

/-- Whether a burn of scenario `j` lies strictly between `a` and `b`. -/
def straddles (xs : Array Float) (N j : UInt64) (a b : Float) : Bool :=
  LeanExe.loop N false fun k acc =>
    let t := rd xs (burnAt k)
    acc || (runs N j k && a < t && t < b)

/-- The intersection of two intervals, or the accepted one of them. -/
def meet (u v : Interval) : Interval :=
  if u.status == 0 then
    if v.status == 0 then ⟨0, fmax u.lo v.lo, fmin u.hi v.hi⟩ else u
  else v

/-- The midpoint of `[a, b]` in binary64. -/
def midpoint (a b : Float) : Float := a + (b - a) * 0.5

/-- The bound of the squared radial and cross-track distance over a smooth panel: the
intersection of the Taylor form with the squares of the components over the panel. -/
def xzBound (inv half : Array UInt64) (n : Interval) (pm vm vT : Interval × Interval × Interval)
    (d px pz : Interval) : Interval :=
  meet (rcTaylorI inv half inv half n pm.1 pm.2.2 vm.1 vm.2.2 px pz vT.1 vT.2.1 vT.2.2 d)
    (rcSquareI inv half inv half px pz)

/-- The interval of the squared radial and cross-track distance of scenario `j` over the times
`tI` of a panel on which the trajectory is smooth, with the burns at or before `start`, the time
`tm` of its midpoint, and the position `pm` at `tm`. -/
def smoothRc (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (start : Float)
    (tI tm : Interval) (pm : Interval × Interval × Interval) : Interval :=
  let n := point (rd xs 0)
  let vm := velocityI inv half xs N j start tm
  let vT := velocityI inv half xs N j start tI
  let d := sub tI tm
  let px := add pm.1 (mul vT.1 d)
  let pz := add pm.2.2 (mul vT.2.2 d)
  xzBound inv half n pm vm vT d px pz

/-- The interval of the squared separation of scenario `j` over a smooth panel, with the
arguments of `smoothRc`: the intersection of the Taylor form with the bound of `x² + z²` plus the
square of the along-track component over the panel. -/
def smoothSep (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (start : Float)
    (tI tm : Interval) (pm : Interval × Interval × Interval) : Interval :=
  let n := point (rd xs 0)
  let vm := velocityI inv half xs N j start tm
  let vT := velocityI inv half xs N j start tI
  let d := sub tI tm
  let px := add pm.1 (mul vT.1 d)
  let py := add pm.2.1 (mul vT.2.1 d)
  let pz := add pm.2.2 (mul vT.2.2 d)
  meet (sepTaylorI inv half inv half n pm.1 pm.2.1 pm.2.2 vm.1 vm.2.1 vm.2.2 px py pz vT.1 vT.2.1
      vT.2.2 d)
    (add (xzBound inv half n pm vm vT d px pz) (sq py))

/-- The interval of the squared separation of scenario `j` over the panel `[a, b]` and the
interval at its midpoint. -/
def sepPanel (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (a b : Float) :
    Interval × Interval :=
  let m := midpoint a b
  if finite m && a ≤ m && m ≤ b then
    let tI := make a b
    let tm := point m
    let pm := positionI inv half xs N j tm
    let w := nonneg (sepSquareI inv half inv half pm.1 pm.2.1 pm.2.2)
    if straddles xs N j a b then
      let p := positionI inv half xs N j tI
      (nonneg (sepSquareI inv half inv half p.1 p.2.1 p.2.2), w)
    else (nonneg (smoothSep inv half xs N j a tI tm pm), w)
  else (rejected, rejected)

def sepStep (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (e d2 hmin acc : Float)
    (m : March) : March :=
  let b := panelEnd m.t m.h e
  let r := sepPanel inv half xs N j m.t b
  march e d2 hmin acc r.1 r.2 b m

/-- The separation search of scenario `j` over `[0, e]` against `d2`, with the accuracy `acc`
and the record `best` of the scenarios before it. -/
def sepSearch (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (e d2 acc best : Float)
    (fuel : UInt64) : March :=
  let hmin := e * minRatio
  LeanExe.repeatWhile fuel ⟨0, 0.0, e, maxFloat, best⟩ (fun m => m.status == 0 && m.t < e)
    (fun m => sepStep inv half xs N j e d2 hmin acc m)

/-- The time of the last burn of scenario `j`, or 0 when it executes none. -/
def lastTime (xs : Array Float) (N j : UInt64) : Float :=
  LeanExe.loop N 0.0 fun k m => if runs N j k then fmax m (rd xs (burnAt k)) else m

/-- The interval of the squared radial and cross-track distance of scenario `j` over the times
`tL + φ/n` for the phases `φ` of `[a, b]`, and the interval at its midpoint. -/
def rcPanel (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (tL a b : Float) :
    Interval × Interval :=
  let m := midpoint a b
  if finite m && a ≤ m && m ≤ b then
    let n := point (rd xs 0)
    let tI := add (point tL) (div (make a b) n)
    let tm := add (point tL) (div (point m) n)
    let pm := positionI inv half xs N j tm
    (nonneg (smoothRc inv half xs N j tL tI tm pm),
      nonneg (rcSquareI inv half inv half pm.1 pm.2.2))
  else (rejected, rejected)

def rcStep (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (tL e d2 hmin acc : Float)
    (m : March) : March :=
  let b := panelEnd m.t m.h e
  let r := rcPanel inv half xs N j tL m.t b
  march e d2 hmin acc r.1 r.2 b m

/-- The radial and cross-track search of scenario `j` over the phases `[0, e]` after the time
`tL`, against `d2`, with the accuracy `acc` and the record `best` of the scenarios before it. -/
def rcSearch (inv half : Array UInt64) (xs : Array Float) (N j : UInt64)
    (tL e d2 acc best : Float) (fuel : UInt64) : March :=
  let hmin := e * minRatio
  LeanExe.repeatWhile fuel ⟨0, 0.0, e, maxFloat, best⟩ (fun m => m.status == 0 && m.t < e)
    (fun m => rcStep inv half xs N j tL e d2 hmin acc m)

/-- The status of a finished search: 0 when it covered `[0, e]`, `notShown` when a panel at the
smallest step failed, `unfinished` when the fuel ran out, and 7 when an operation rejected. -/
def searchStatus (m : March) (e : Float) (notShown unfinished : UInt64) : UInt64 :=
  if m.status == 0 then (if e ≤ m.t then 0 else unfinished)
  else if m.status == 1 then notShown else 7

/-- The state of the loop over scenarios: the status, the scenario and the panel's start of a
failure, the least lower ends of the two kinds of search, and their records of the least lower
ends at midpoints. -/
structure Scan where
  status : UInt64
  scenario : UInt64
  stop : Float
  sepLow : Float
  rcLow : Float
  sepBest : Float
  rcBest : Float
  deriving Inhabited

/-- The two searches of scenario `j` against `d2` and `r2` with the accuracy `acc`, after the
scenarios before it succeeded. -/
def scanStep (inv half : Array UInt64) (xs : Array Float) (N fuel : UInt64) (d2 r2 acc : Float)
    (j : UInt64) (s : Scan) : Scan :=
  if s.status == 0 then
    let e := rd xs 1
    let m := sepSearch inv half xs N j e d2 acc s.sepBest fuel
    let st := searchStatus m e 3 5
    if st == 0 then
      let r := rcSearch inv half xs N j (lastTime xs N j) twoPiHi r2 acc s.rcBest fuel
      let st2 := searchStatus r twoPiHi 4 6
      if st2 == 0 then
        ⟨0, 0, 0.0, fmin s.sepLow m.low, fmin s.rcLow r.low, m.best, r.best⟩
      else ⟨st2, j, r.t, 0.0, 0.0, 0.0, 0.0⟩
    else ⟨st, j, m.t, 0.0, 0.0, 0.0, 0.0⟩
  else s

/-- Whether every value of the input is finite. -/
def finiteAll (xs : Array Float) : Bool :=
  LeanExe.loop xs.size.toUInt64 true fun i ok => ok && finite (rd xs i)

/-- Whether the values of a plan of `N` burns lie in their ranges and order. -/
def valuesOk (xs : Array Float) (N : UInt64) : Bool :=
  finiteAll xs && 0.0 < rd xs 0 && 0.0 < rd xs 1 && 0.0 ≤ rd xs 2 && 0.0 ≤ rd xs 3 &&
    (LeanExe.loop 6 true fun i ok => ok && rd xs (4 + 2 * i) ≤ rd xs (5 + 2 * i)) &&
    (LeanExe.loop N true fun k ok =>
      let i := burnAt k
      let prev := if k == 0 then 0.0 else rd xs (i - 7)
      ok && prev ≤ rd xs i && rd xs i ≤ rd xs 1 && rd xs (i + 1) ≤ rd xs (i + 2) &&
        rd xs (i + 3) ≤ rd xs (i + 4) && rd xs (i + 5) ≤ rd xs (i + 6))

/-- An interval whose upper end is at least `x²`, for `x ≥ 0`: `[0, 0]` for `x = 0`. -/
def square (x : Float) : Interval := if 0.0 < x then sq (point x) else point 0.0

/-- A double at most the square root of `x`, for `x ≥ 0`. -/
def sqrtDown (x : Float) : Float := fmax 0.0 (sqrt (point x)).lo

/-- The passive-safety check of a plan with the tables of `sin` and `cos`. -/
def checkWith (inv half : Array UInt64) (xs : Array Float) (fuel : UInt64) (acc : Float) :
    Result :=
  let size := xs.size.toUInt64
  if 16 ≤ size && (size - 16) % 7 == 0 && size ≤ 128 && 1 ≤ fuel && fuel ≤ 1048576 &&
      finite acc && 0.0 ≤ acc then
    let N := (size - 16) / 7
    if valuesOk xs N then
      let d2 := square (rd xs 2)
      let r2 := square (rd xs 3)
      if d2.status == 0 && r2.status == 0 then
        let s := LeanExe.loop (2 * N + 1) ⟨0, 0, 0.0, maxFloat, maxFloat, maxFloat, maxFloat⟩
          fun j s => scanStep inv half xs N fuel d2.hi r2.hi acc j s
        if s.status == 0 then
          ⟨0, 0, 0.0, fmax (rd xs 2) (sqrtDown s.sepLow), fmax (rd xs 3) (sqrtDown s.rcLow)⟩
        else ⟨s.status, s.scenario, s.stop, 0.0, 0.0⟩
      else ⟨7, 0, 0.0, 0.0, 0.0⟩
    else ⟨2, 0, 0.0, 0.0, 0.0⟩
  else ⟨1, 0, 0.0, 0.0, 0.0⟩

/-- The passive-safety check of `requirements.md`. -/
def check (xs : Array Float) (fuel : UInt64) (acc : Float) : Result :=
  checkWith Trig.invPi Trig.halfPi xs fuel acc

end Demos.PassiveSafety
