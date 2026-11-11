import Demos.Sgp4.Spec

/-!
The enclosing SGP4 program.  `initBox` computes intervals for the constants of an element set
given as intervals, and `propagateBox` computes a status and an interval for each coordinate of
the position and the velocity at a time.  `BoxSound.lean` proves that the intervals contain the
values of `Model.lean` and that a status other than 7 is the model's status.

| Status | Meaning |
|---|---|
| 0 | The intervals contain the model's position and velocity. |
| 1, 2, 4 | The model has that status. |
| 6 | The model has status 6, and the intervals contain its position and velocity. |
| 7 | The intervals do not decide a test of the model, an input interval was rejected, or an operation was rejected. |
| 8 | The model has status 8, the deep-space path. |
| 9 | The model has status 9: the intervals of the mean motion and the eccentricity lie outside `0 < n` and `0 ≤ e < 1`. |
-/

namespace Demos.Sgp4

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64

/-- A status and the intervals of the position in km and the velocity in km/s. -/
structure Box where
  status : UInt64
  x : Interval
  y : Interval
  z : Interval
  vx : Interval
  vy : Interval
  vz : Interval
  deriving Inhabited

/-- A status without intervals. -/
def noBox (status : UInt64) : Box :=
  ⟨status, rejected, rejected, rejected, rejected, rejected, rejected⟩

/-- The status of an element set from the intervals of the mean motion in revolutions per day,
the eccentricity, the period less 225 minutes, and the mean motion `no`. -/
def initStatus (n e deep no : Interval) : UInt64 :=
  if n.status == 0 && e.status == 0 then
    if 0 < n.lo ∧ 0 ≤ e.lo ∧ e.hi < 1.0 then
      if deep.status == 0 && no.status == 0 then
        if 0 ≤ deep.lo then 8
        else if deep.hi < 0 then
          if 0 < no.lo then 0
          else if no.hi ≤ 0 then 2
          else 7
        else 7
      else 7
    else if n.hi ≤ 0 ∨ e.hi < 0 ∨ 1.0 ≤ e.lo then 9
    else 7
  else 7

/-- The status at a time from the intervals of the mean eccentricity less 1, the mean
eccentricity plus 0.001, the semilatus rectum, and the radius less 1.  `ok` states that the
intervals of the position and the velocity are accepted. -/
def stateStatus (e1 e2 pl m6 : Interval) (ok : Bool) : UInt64 :=
  if e1.status == 0 && e2.status == 0 then
    if 0 ≤ e1.lo ∨ e2.hi < 0 then 1
    else if e1.hi < 0 ∧ 0 ≤ e2.lo then
      if pl.status == 0 then
        if pl.hi < 0 then 4
        else if 0 ≤ pl.lo then
          if m6.status == 0 && ok then
            if m6.hi < 0 then 6
            else if 0 ≤ m6.lo then 0
            else 7
          else 7
        else 7
      else 7
    else 7
  else 7

/-- The status and the constants of an element set. -/
def initBoxWith (inv half logTab expTab : Array UInt64) (n e incl node argp m bstar : Interval) :
    UInt64 × interval_tuple% 35 :=
  let c := Spec.wgs72I inv half logTab expTab n e incl node argp m bstar
  (initStatus n e (sub c.1 (ofInt 225)) c.2.1, c)

/-- The status and the intervals at `t` minutes from the epoch. -/
def propagateBoxWith (inv half logTab expTab : Array UInt64) (c : UInt64 × interval_tuple% 35)
    (t : Interval) : Box :=
  if c.1 == 0 then
    let s := Spec.wgs72StateI inv half logTab expTab t c.2
    let x := s.2.2.2.1
    let y := s.2.2.2.2.1
    let z := s.2.2.2.2.2.1
    let vx := s.2.2.2.2.2.2.1
    let vy := s.2.2.2.2.2.2.2.1
    let vz := s.2.2.2.2.2.2.2.2
    let ok := x.status == 0 && y.status == 0 && z.status == 0 && vx.status == 0 &&
      vy.status == 0 && vz.status == 0
    let status := stateStatus (sub s.1 (ofInt 1)) (add s.1 (ratio 1 1000)) s.2.1
      (sub s.2.2.1 (ofInt 1)) ok
    if status == 0 || status == 6 then ⟨status, x, y, z, vx, vy, vz⟩ else noBox status
  else noBox c.1

def sgp4BoxWith (inv half logTab expTab : Array UInt64) (n e incl node argp m bstar t : Interval) :
    Box :=
  propagateBoxWith inv half logTab expTab
    (initBoxWith inv half logTab expTab n e incl node argp m bstar) t

def initBox (n e incl node argp m bstar : Interval) : UInt64 × interval_tuple% 35 :=
  initBoxWith Trig.invPi Trig.halfPi Pow.powLogTable Exp.expTable n e incl node argp m bstar

def propagateBox (c : UInt64 × interval_tuple% 35) (t : Interval) : Box :=
  propagateBoxWith Trig.invPi Trig.halfPi Pow.powLogTable Exp.expTable c t

/-- The status and the intervals of an element set at `t` minutes from its epoch. -/
def sgp4Box (n e incl node argp m bstar t : Interval) : Box :=
  sgp4BoxWith Trig.invPi Trig.halfPi Pow.powLogTable Exp.expTable n e incl node argp m bstar t

/-- The interval from one step below `x` to one step above it, which contains every real number
that rounds to `x`. -/
def around (x : Float) : Interval := join true (endpoint false x) (endpoint true x)

def sgp4BoxAroundWith (inv half logTab expTab : Array UInt64)
    (n e incl node argp m bstar t : Float) : Box :=
  sgp4BoxWith inv half logTab expTab (around n) (around e) (around incl) (around node)
    (around argp) (around m) (around bstar) (around t)

/-- `sgp4Box` for the intervals around the binary64 values of an element set and a time. -/
def sgp4BoxAround (n e incl node argp m bstar t : Float) : Box :=
  sgp4BoxAroundWith Trig.invPi Trig.halfPi Pow.powLogTable Exp.expTable n e incl node argp m bstar
    t

end Demos.Sgp4
