import Demos.Energy.Site
import Library.Random.SplitMix64.Program

/-! The cases of the module `energy`: `authorize` on the inputs of the plan's worked example, on
invalid inputs, on inputs at the boundary of each check, and on inputs that a generator builds
from SplitMix64 with a fixed seed, with native Lean's results.  Each case requires one retained
block, the host's input, because `authorize` borrows its input and returns three words: the
status, the setpoint, and the expiry. -/

namespace TestSupport.Energy.Cases

open Demos.Energy

/-- The word of the signed power `p`. -/
def pw (p : Int) : UInt64 := (p + 4294967296).toNat.toUInt64

/-- An input at snapshot time 0 with the given energy interval, state in force, load and PV
intervals, and proposed setpoint. -/
def snap (eLo eHi mode : UInt64) (inForce : Int) (lLo lHi sLo sHi : UInt64) (s : Int) :
    Array UInt64 :=
  #[1, 0, eLo, eHi, mode, pw inForce, lLo, lHi, sLo, sHi, pw s]

def base : Array UInt64 := snap 14400000 15120000 0 0 3000 4000 0 3000 (-1000)

def worked : List (Array UInt64) :=
  [base, snap 14400000 15120000 0 0 3000 4000 0 3000 (-3000),
    snap 11520000 15120000 0 0 3000 4000 0 3000 (-1000),
    snap 14400000 15120000 0 0 500 1000 3000 5000 3000,
    snap 11288000 12008000 0 (-1000) 3000 4000 0 3000 (-1000)]

def invalid : List (Array UInt64) :=
  [#[], base.pop, base.push 0, base.set! 0 2, base.set! 1 1099511627776,
    base.set! 3 4398046511105, base.set! 4 2, base.set! 5 (pw 1048577), base.set! 7 1048577,
    base.set! 9 1048577, base.set! 10 (pw (-1048577)), base.set! 2 15120001, base.set! 6 4001,
    base.set! 8 3001, base.set! 10 (pw 5001), base.set! 10 (pw (-5001)),
    Array.replicate 11 18446744073709551615]

/-- Inputs on both sides of the floor test at `E⁻ = 11,868,000`, the export test at a setpoint of
-1,950 W, the import test at 950 W, and the ceiling test at `E⁺ = 29,655,000` for a charge of
5,000 W; the setpoints of ±5,000 W with no load or PV, which fail a grid test; the fallback mode
in force; a state in force and a setpoint of opposite directions, which the authorizer tests on
both sides; and energies on and beyond the floor and the ceiling, where it accepts setpoints that
leave the site no further outside the limit. -/
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
    snap 34200001 34200001 0 0 0 0 0 0 (-1000)]

abbrev Gen := StateM UInt64

def word : Gen UInt64 := modifyGet fun s =>
  let (s', v) := Library.Random.SplitMix64.splitMix s
  (v, s')

def below (n : UInt64) : Gen UInt64 := return (← word) % n

def signedBelow (n : UInt64) : Gen Int := return ((← below (2 * n + 1)).toNat : Int) - n.toNat

/-- A valid input with energies up to 40,000,000 J, loads up to 11,000 W, PV up to 9,000 W, and
powers within 5,000 W. -/
def randomInput : Gen (Array UInt64) := do
  let time ← below 1000000
  let eLo ← below 40000000
  let eHi := eLo + (← below 2000000)
  let mode ← below 2
  let inForce ← signedBelow 5000
  let lLo ← below 8000
  let lHi := lLo + (← below 3000)
  let sLo ← below 6000
  let sHi := sLo + (← below 3000)
  let s ← signedBelow 5000
  return #[1, time, eLo, eHi, mode, pw inForce, lLo, lHi, sLo, sHi, pw s]

def random : List (Array UInt64) :=
  Id.run (((List.range 2000).mapM fun _ => randomInput).run' 7)

def classes : List (String × List (Array UInt64)) :=
  [("worked", worked), ("invalid", invalid), ("boundary", boundary), ("random", random)]

def line (xs : Array UInt64) : String :=
  let d := authorize xs
  let ws := ",".intercalate (xs.toList.map toString)
  s!"energy|authorize|list:i64,i64,i64|array-u64:{ws}|{d.status.ctorIdx} {d.setpoint} {d.expiry}|1"

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
