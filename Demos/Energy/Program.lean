/-! The energy authorizer, in the verified compiler's dialect.

`authorizeWith site xs` decides whether a gateway may send the proposed power limits of the
snapshot `xs` for one window, under the profile table `site`.  Battery power stays within the
limits widened by the tolerance, and a held setpoint `s` is the limits `[s, s]`.  Energies are
in joules, powers in watts, times in seconds, and the efficiency bound in parts per million.  A
signed power `p` is the word `p + offset`.

| Profile word | Field |
|---|---|
| 0 | Layout version |
| 1, 2 | Energy floor and ceiling |
| 3, 4 | Largest charge and discharge limits |
| 5, 6 | Import and export caps |
| 7 | Efficiency bound |
| 8 | Largest auxiliary loss rate |
| 9 | Tolerance of battery power about the limits |
| 10, 11 | Fallback interval, offset |
| 12 | Transition time |
| 13 | Window length |
| 14 | Send deadline, which only the gateway uses |

| Input word | Field |
|---|---|
| 0 | Layout version, 1 |
| 1 | Snapshot time |
| 2, 3 | Energy interval |
| 4 | State in force: mode (0 command, 1 fallback) |
| 5, 6 | Limits in force, offset |
| 7, 8 | Load interval |
| 9, 10 | PV interval |
| 11, 12 | Proposed limits, offset |

The window's power interval `B` is the smallest interval that contains the interval of the state
in force, the proposed limits widened by the tolerance, and the fallback interval.  On a side
where `B` extends beyond the fallback interval, the authorizer tests that side's grid cap and
energy limit: the lower side tests the export cap and the energy floor, and the upper side the
import cap and the energy ceiling.  The fallback interval contains 0, so the lower end of `B` is
at most 0 and its upper end at least 0.  The lower energy bound discharges at the efficiency
bound and loses the largest loss rate, rounding up, and the upper energy bound charges at
efficiency 1 with no loss. -/

namespace Demos.Energy

/-- The decision's status: acceptance, or the first condition that fails. -/
inductive Status where
  | accepted
  | length
  | version
  | range
  | order
  | power
  | exportCap
  | floor
  | importCap
  | ceiling
  deriving Inhabited, DecidableEq, Repr

/-- The authorizer's result.  A rejection has limits and expiry 0. -/
structure Decision where
  status : Status
  low : UInt64
  high : UInt64
  expiry : UInt64
  deriving Inhabited, DecidableEq, Repr

/-- The word of signed power 0. -/
def offset : UInt64 := 4294967296

/-- Largest magnitude of a power, `2 ^ 20` W. -/
def powerBound : UInt64 := 1048576

/-- Largest energy, `2 ^ 42` J. -/
def energyBound : UInt64 := 4398046511104

/-- Bound of times, `2 ^ 40` s. -/
def timeBound : UInt64 := 1099511627776

def million : UInt64 := 1000000

@[inline] def word (xs : Array UInt64) (i : UInt64) : UInt64 := xs[i.toNat]!

/-- A signed power word within `powerBound` of zero. -/
@[inline] def powerOk (w : UInt64) : Bool := offset - powerBound ≤ w && w ≤ offset + powerBound

/-- Every input word lies in its range. -/
def rangeOk (xs : Array UInt64) : Bool :=
  word xs 1 < timeBound && word xs 2 ≤ energyBound && word xs 3 ≤ energyBound &&
    word xs 4 ≤ 1 && powerOk (word xs 5) && powerOk (word xs 6) &&
    word xs 7 ≤ powerBound && word xs 8 ≤ powerBound && word xs 9 ≤ powerBound &&
    word xs 10 ≤ powerBound && powerOk (word xs 11) && powerOk (word xs 12)

/-- Every interval and pair of limits of the input has its lower end at most its upper end. -/
def orderOk (xs : Array UInt64) : Bool :=
  word xs 2 ≤ word xs 3 && word xs 5 ≤ word xs 6 && word xs 7 ≤ word xs 8 &&
    word xs 9 ≤ word xs 10 && word xs 11 ≤ word xs 12

/-- The proposed limits lie between the largest discharge and the largest charge. -/
def limitOk (site xs : Array UInt64) : Bool :=
  offset - word site 4 ≤ word xs 11 && word xs 12 ≤ offset + word site 3

/-- Lower end of the interval of the state in force. -/
def inForceLow (site xs : Array UInt64) : UInt64 :=
  if word xs 4 == 1 then word site 10 else word xs 5 - word site 9

/-- Upper end of the interval of the state in force. -/
def inForceHigh (site xs : Array UInt64) : UInt64 :=
  if word xs 4 == 1 then word site 11 else word xs 6 + word site 9

/-- Lower end of the window's power interval. -/
def lowB (site xs : Array UInt64) : UInt64 :=
  min (min (inForceLow site xs) (word xs 11 - word site 9)) (word site 10)

/-- Upper end of the window's power interval. -/
def highB (site xs : Array UInt64) : UInt64 :=
  max (max (inForceHigh site xs) (word xs 12 + word site 9)) (word site 11)

/-- Energy that the lower bound drains over the window at the lower end `b` of the power
interval, which is at most `offset` because the fallback interval contains 0: discharging at the
efficiency bound, rounded up, and the largest loss. -/
def lowDrain (site : Array UInt64) (b : UInt64) : UInt64 :=
  ((offset - b) * word site 13 * million + word site 7 - 1) / word site 7 +
    word site 8 * word site 13

/-- Energy that the upper bound gains over the window at the upper end `b` of the power interval,
which is at least `offset`, at efficiency 1 and with no loss. -/
def highGain (site : Array UInt64) (b : UInt64) : UInt64 := (b - offset) * word site 13

/-- Grid export stays within the cap at the lower end `b`: `L⁻ + b + X ≥ S⁺`. -/
def exportOk (site xs : Array UInt64) (b : UInt64) : Bool :=
  word xs 10 + offset ≤ word xs 7 + b + word site 6

/-- Stored energy stays at or above the floor at the end of the window, and so at its start,
since the drain is at least 0. -/
def floorOk (site xs : Array UInt64) (b : UInt64) : Bool :=
  word site 1 + lowDrain site b ≤ word xs 2

/-- Grid import stays within the cap at the upper end `b`: `L⁺ + b ≤ I + S⁻`. -/
def importOk (site xs : Array UInt64) (b : UInt64) : Bool :=
  word xs 8 + b ≤ word site 5 + word xs 9 + offset

/-- Stored energy stays at or below the ceiling at the end of the window, and so at its start,
since the gain is at least 0. -/
def ceilingOk (site xs : Array UInt64) (b : UInt64) : Bool :=
  word xs 3 + highGain site b ≤ word site 2

def reject (s : Status) : Decision := { status := s, low := 0, high := 0, expiry := 0 }

/-- The decision for the snapshot `xs` under the profile table `site`. -/
def authorizeWith (site xs : Array UInt64) : Decision :=
  if xs.size.toUInt64 != 13 then reject .length
  else if word xs 0 != 1 then reject .version
  else if !rangeOk xs then reject .range
  else if !orderOk xs then reject .order
  else if !limitOk site xs then reject .power
  else
    let lo := lowB site xs
    let hi := highB site xs
    let lower : Bool := lo < word site 10
    let upper : Bool := word site 11 < hi
    if lower && !exportOk site xs lo then reject .exportCap
    else if lower && !floorOk site xs lo then reject .floor
    else if upper && !importOk site xs hi then reject .importCap
    else if upper && !ceilingOk site xs hi then reject .ceiling
    else { status := .accepted, low := word xs 11, high := word xs 12,
           expiry := word xs 1 + word site 13 - word site 12 }

end Demos.Energy
