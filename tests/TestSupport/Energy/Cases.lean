import Demos.Energy.Site
import Library.Random.SplitMix64.Program

/-! The cases of the module `energy`: `authorize` on the inputs of the plan's worked example, on
invalid inputs, on inputs at the boundary of each check, and on inputs that a generator builds
from SplitMix64 with a fixed seed, with native Lean's results.  Each case requires one retained
block, the host's input, because `authorize` borrows its input and returns four words: the
status, the two limits, and the expiry. -/

namespace TestSupport.Energy.Cases

open Demos.Energy

/-- The word of the signed power `p`. -/
def pw (p : Int) : UInt64 := (p + 4294967296).toNat.toUInt64

/-- An input at snapshot time 0 with the given energy interval, mode and limits in force, load and
PV intervals, and proposed limits. -/
def input (eLo eHi mode : UInt64) (inLo inHi : Int) (lLo lHi sLo sHi : UInt64) (lo hi : Int) :
    Array UInt64 :=
  #[1, 0, eLo, eHi, mode, pw inLo, pw inHi, lLo, lHi, sLo, sHi, pw lo, pw hi]

/-- An input whose state in force and proposal are held setpoints, the limits `[s, s]`. -/
def snap (eLo eHi mode : UInt64) (inForce : Int) (lLo lHi sLo sHi : UInt64) (s : Int) :
    Array UInt64 :=
  input eLo eHi mode inForce inForce lLo lHi sLo sHi s s

def base : Array UInt64 := snap 14400000 15120000 0 0 3000 4000 0 3000 (-1000)

def worked : List (Array UInt64) :=
  [base, snap 14400000 15120000 0 0 3000 4000 0 3000 (-3000),
    snap 11520000 15120000 0 0 3000 4000 0 3000 (-1000),
    snap 14400000 15120000 0 0 500 1000 3000 5000 3000,
    snap 11288000 12008000 0 (-1000) 3000 4000 0 3000 (-1000),
    input 14400000 15120000 0 0 0 3000 4000 0 3000 (-1000) 500,
    input 14400000 15120000 0 0 0 3000 4000 0 3000 (-1000) 1000]

/-- Inputs that the checks before the side tests reject: wrong lengths and versions; each word one
past its range, including the lower ends of the energy, load, and PV intervals, which the range
check rejects before the order check; reversed intervals and limits; limits beyond the largest
discharge and charge; and every word at `2 ^ 64 - 1`, with and without the right version. -/
def invalid : List (Array UInt64) :=
  [#[], base.pop, base.push 0, base.set! 0 2, base.set! 1 1099511627776,
    base.set! 2 4398046511105, base.set! 3 4398046511105, base.set! 4 2,
    base.set! 5 (pw (-1048577)), base.set! 6 (pw 1048577), base.set! 7 1048577,
    base.set! 8 1048577, base.set! 9 1048577, base.set! 10 1048577,
    base.set! 11 (pw (-1048577)), base.set! 12 (pw 1048577), base.set! 2 15120001,
    (base.set! 5 (pw 1)).set! 6 (pw 0), base.set! 7 4001, base.set! 9 3001,
    base.set! 11 (pw 0), base.set! 11 (pw (-5001)), base.set! 12 (pw 5001),
    Array.replicate 13 18446744073709551615,
    (Array.replicate 13 18446744073709551615).set! 0 1]

/-- Inputs on both sides of the floor test at `E⁻ = 11,868,000`, the export test at a setpoint of
-1,950 W, the import test at 950 W, and the ceiling test at `E⁺ = 29,655,000` for a charge of
5,000 W; the setpoints of ±5,000 W with no load or PV, which fail a grid test; the fallback mode
in force; a state in force and a setpoint of opposite directions, whose power interval extends
beyond fallback on both sides and which fail the export test; energies on and beyond the floor
and the ceiling, where the authorizer accepts setpoints that leave the site no further outside
the limit; the limits `[-1,000, 950]` and `[-1,000, 951]` on both sides of the import test; wide
limits in force with a held setpoint of 0, whose power interval extends beyond fallback on both
sides and which fail the export test; and words at the ends of their ranges: `E⁺ = 2 ^ 42`,
`L⁺ = 2 ^ 20`, and limits in force of `-2 ^ 20` and `2 ^ 20`. -/
def boundary : List (Array UInt64) :=
  [snap 11868000 15120000 0 0 3000 4000 0 3000 (-1000),
    snap 11867999 15120000 0 0 3000 4000 0 3000 (-1000),
    snap 14400000 15120000 0 0 3000 4000 0 3000 (-1950),
    snap 14400000 15120000 0 0 3000 4000 0 3000 (-1951),
    snap 14400000 15120000 0 0 3000 4000 0 3000 950,
    snap 14400000 15120000 0 0 3000 4000 0 3000 951,
    snap 14400000 29655000 0 0 0 0 5000 5000 5000,
    snap 14400000 29655001 0 0 0 0 5000 5000 5000,
    snap 14400000 15120000 0 0 0 0 0 0 5000,
    snap 14400000 15120000 0 0 0 0 0 0 (-5000),
    snap 14400000 15120000 1 0 3000 4000 0 3000 (-1000),
    snap 14400000 15120000 1 (-5000) 3000 4000 0 3000 0,
    snap 14400000 15120000 0 5000 3000 4000 0 3000 (-5000),
    snap 10800000 10800000 0 0 0 0 0 0 0,
    snap 10799999 10800000 0 0 0 0 0 0 1000,
    snap 34200000 34200000 0 0 0 0 0 0 0,
    snap 34200001 34200001 0 0 0 0 0 0 (-1000),
    input 14400000 15120000 0 0 0 3000 4000 0 3000 (-1000) 950,
    input 14400000 15120000 0 0 0 3000 4000 0 3000 (-1000) 951,
    input 14400000 15120000 0 (-2000) 2000 3000 4000 0 3000 0 0,
    base.set! 3 4398046511104, base.set! 8 1048576, base.set! 5 (pw (-1048576)),
    base.set! 6 (pw 1048576)]

abbrev Gen := StateM UInt64

def next : Gen UInt64 := modifyGet fun s =>
  let (s', v) := Library.Random.SplitMix64.splitMix s
  (v, s')

def below (n : UInt64) : Gen UInt64 := return (← next) % n

def signedBelow (n : UInt64) : Gen Int := return ((← below (2 * n + 1)).toNat : Int) - n.toNat

/-- Limits whose lower end lies within 5,000 W of 0, and whose upper end equals it or exceeds it
by less than 6,000 W. -/
def randomLimits : Gen (Int × Int) := do
  let lo ← signedBelow 5000
  let width ← below 6000
  return if (← below 2) == 0 then (lo, lo) else (lo, lo + width.toNat)

/-- A valid input, except that some proposed limits exceed the largest charge, with lower energies
below 40,000,000 J and energy intervals narrower than 2,000,000 J, loads up to 11,000 W, PV up to
9,000 W, and limits in force and proposed limits that are held setpoints or intervals. -/
def randomInput : Gen (Array UInt64) := do
  let time ← below 1000000
  let eLo ← below 40000000
  let eHi := eLo + (← below 2000000)
  let mode ← below 2
  let (inLo, inHi) ← randomLimits
  let lLo ← below 8000
  let lHi := lLo + (← below 3000)
  let sLo ← below 6000
  let sHi := sLo + (← below 3000)
  let (lo, hi) ← randomLimits
  return #[1, time, eLo, eHi, mode, pw inLo, pw inHi, lLo, lHi, sLo, sHi, pw lo, pw hi]

def random : List (Array UInt64) :=
  Id.run (((List.range 2000).mapM fun _ => randomInput).run' 7)

def classes : List (String × List (Array UInt64)) :=
  [("worked", worked), ("invalid", invalid), ("boundary", boundary), ("random", random)]

def line (xs : Array UInt64) : String :=
  let d := authorize xs
  let ws := ",".intercalate (xs.toList.map toString)
  s!"energy|authorize|list:i64,i64,i64,i64|array-u64:{ws}|{d.status.ctorIdx} {d.low} {d.high} \
    {d.expiry}|1"

/-- Prints the cases, or with `summary` the count of each class's statuses. -/
def run (summary : Bool) : IO Unit := do
  for (name, inputs) in classes do
    let mut counts : Array Nat := Array.replicate 10 0
    for xs in inputs do
      if !summary then IO.println (line xs)
      counts := counts.modify (authorize xs).status.ctorIdx (· + 1)
    if summary then
      IO.println s!"{name}: {inputs.length} inputs, statuses by constructor index: {counts}"

def cases : IO Unit := run false

end TestSupport.Energy.Cases
