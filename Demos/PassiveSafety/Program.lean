import Demos.PassiveSafety.Closed
import LeanExe.Dialect.Loop
import LeanExe.Dialect.RepeatWhile

/-!
The passive-safety check of `requirements.md`.  `checkWith` validates the input, and for each
scenario of the plan it runs `sepSearch`, which covers the horizon with panels of time on which
the interval of the squared separation lies at or above the squared threshold, and `rcSearch`,
which covers one period after the scenario's last burn, by the phases `[0, 2π]`, with panels on
which the interval of the squared radial and cross-track distance does.  Both searches step by
`march` and enclose the position by `positionI`.  The interval functions of `Closed.lean` take the
tables of `pow` as well as those of `sin` and `cos`, use no power, and receive the tables of `sin`
and `cos` in their place.
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
and 3 when an interval operation rejects; the covered part `[0, t]`, the step, and the least
lower end of the accepted panels. -/
structure March where
  status : UInt64
  t : Float
  h : Float
  low : Float
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

/-- One step of a search of `[0, e]` against the bound `d2`, with `v` the interval of the panel
`[m.t, b]`: an accepted panel at or above `d2` extends the covered part and doubles the step up
to `e`, and another panel halves the step or ends the search.  A rejected interval, or a panel
end below its start, ends the search with status 3. -/
def march (e d2 hmin : Float) (v : Interval) (b : Float) (m : March) : March :=
  if v.status == 0 && m.t ≤ b then
    if d2 ≤ v.lo then
      let h2 := m.h * 2.0
      ⟨0, b, if h2 ≤ e then h2 else e, fmin m.low v.lo⟩
    else if m.h ≤ hmin then ⟨1, m.t, m.h, m.low⟩
    else ⟨0, m.t, m.h * 0.5, m.low⟩
  else ⟨3, m.t, m.h, m.low⟩

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

/-- The interval of the squared separation of scenario `j` over the panel `[a, b]`. -/
def sepPanel (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (a b : Float) :
    Interval :=
  let p := positionI inv half xs N j (make a b)
  nonneg (sepSquareI inv half inv half p.1 p.2.1 p.2.2)

def sepStep (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (e d2 hmin : Float)
    (m : March) : March :=
  let b := panelEnd m.t m.h e
  march e d2 hmin (sepPanel inv half xs N j m.t b) b m

/-- The separation search of scenario `j` over `[0, e]` against `d2`. -/
def sepSearch (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (e d2 : Float)
    (fuel : UInt64) : March :=
  let hmin := e * minRatio
  LeanExe.repeatWhile fuel ⟨0, 0.0, e, maxFloat⟩ (fun m => m.status == 0 && m.t < e)
    (fun m => sepStep inv half xs N j e d2 hmin m)

/-- The time of the last burn of scenario `j`, or 0 when it executes none. -/
def lastTime (xs : Array Float) (N j : UInt64) : Float :=
  LeanExe.loop N 0.0 fun k m => if runs N j k then fmax m (rd xs (burnAt k)) else m

/-- The interval of the squared radial and cross-track distance of scenario `j` over the times
`tL + φ/n` for the phases `φ` of `[a, b]`. -/
def rcPanel (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (tL a b : Float) :
    Interval :=
  let tI := add (point tL) (div (make a b) (point (rd xs 0)))
  let p := positionI inv half xs N j tI
  nonneg (rcSquareI inv half inv half p.1 p.2.2)

def rcStep (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (tL e d2 hmin : Float)
    (m : March) : March :=
  let b := panelEnd m.t m.h e
  march e d2 hmin (rcPanel inv half xs N j tL m.t b) b m

/-- The radial and cross-track search of scenario `j` over the phases `[0, e]` after the time
`tL`, against `d2`. -/
def rcSearch (inv half : Array UInt64) (xs : Array Float) (N j : UInt64) (tL e d2 : Float)
    (fuel : UInt64) : March :=
  let hmin := e * minRatio
  LeanExe.repeatWhile fuel ⟨0, 0.0, e, maxFloat⟩ (fun m => m.status == 0 && m.t < e)
    (fun m => rcStep inv half xs N j tL e d2 hmin m)

/-- The status of a finished search: 0 when it covered `[0, e]`, `notShown` when a panel at the
smallest step failed, `unfinished` when the fuel ran out, and 7 when an operation rejected. -/
def searchStatus (m : March) (e : Float) (notShown unfinished : UInt64) : UInt64 :=
  if m.status == 0 then (if e ≤ m.t then 0 else unfinished)
  else if m.status == 1 then notShown else 7

/-- The state of the loop over scenarios: the status, the scenario and the panel's start of a
failure, and the least lower ends of the two kinds of search. -/
structure Scan where
  status : UInt64
  scenario : UInt64
  stop : Float
  sepLow : Float
  rcLow : Float
  deriving Inhabited

/-- The two searches of scenario `j` against `d2` and `r2`, after the scenarios before it
succeeded. -/
def scanStep (inv half : Array UInt64) (xs : Array Float) (N fuel : UInt64) (d2 r2 : Float)
    (j : UInt64) (s : Scan) : Scan :=
  if s.status == 0 then
    let e := rd xs 1
    let m := sepSearch inv half xs N j e d2 fuel
    let st := searchStatus m e 3 5
    if st == 0 then
      let r := rcSearch inv half xs N j (lastTime xs N j) twoPiHi r2 fuel
      let st2 := searchStatus r twoPiHi 4 6
      if st2 == 0 then ⟨0, 0, 0.0, fmin s.sepLow m.low, fmin s.rcLow r.low⟩
      else ⟨st2, j, r.t, 0.0, 0.0⟩
    else ⟨st, j, m.t, 0.0, 0.0⟩
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
def checkWith (inv half : Array UInt64) (xs : Array Float) (fuel : UInt64) : Result :=
  let size := xs.size.toUInt64
  if 16 ≤ size && (size - 16) % 7 == 0 && size ≤ 128 && 1 ≤ fuel && fuel ≤ 1048576 then
    let N := (size - 16) / 7
    if valuesOk xs N then
      let d2 := square (rd xs 2)
      let r2 := square (rd xs 3)
      if d2.status == 0 && r2.status == 0 then
        let s := LeanExe.loop (2 * N + 1) ⟨0, 0, 0.0, maxFloat, maxFloat⟩
          fun j s => scanStep inv half xs N fuel d2.hi r2.hi j s
        if s.status == 0 then
          ⟨0, 0, 0.0, fmax (rd xs 2) (sqrtDown s.sepLow), fmax (rd xs 3) (sqrtDown s.rcLow)⟩
        else ⟨s.status, s.scenario, s.stop, 0.0, 0.0⟩
      else ⟨7, 0, 0.0, 0.0, 0.0⟩
    else ⟨2, 0, 0.0, 0.0, 0.0⟩
  else ⟨1, 0, 0.0, 0.0, 0.0⟩

/-- The passive-safety check of `requirements.md`. -/
def check (xs : Array Float) (fuel : UInt64) : Result :=
  checkWith Trig.invPi Trig.halfPi xs fuel

end Demos.PassiveSafety
