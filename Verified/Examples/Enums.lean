import Verified.Reflect.Command

/-! The nineteenth program of the verified compiler: enumerations.  An enumeration with a `Flat`
instance is the word that the instance gives each constructor.  A `match` on one becomes a chain of
tests of that word, and `==`, `!=`, `decide`, and `if` compare words.  The programs use
enumerations as parameters, results, a structure field, a loop state's field, and array
elements, with one instance written with `ctorIdx` and one with `match`. -/

namespace Verified.Examples.Enums

open LeanExe.Pipeline

inductive Op where
  | add | sub | mul | neg
  deriving Inhabited, DecidableEq

instance : Flat Op UInt64 := ⟨fun op => op.ctorIdx.toUInt64⟩

inductive Phase where
  | solid | liquid | gas
  deriving Inhabited, DecidableEq

instance : Flat Phase UInt64 := ⟨fun | .solid => 0 | .liquid => 1 | .gas => 2⟩

structure Calc where
  value : UInt64
  steps : UInt64
  last : Op
  deriving Inhabited

instance : Flat Calc (UInt64 × UInt64 × Op) := ⟨fun c => (c.value, c.steps, c.last)⟩

def apply (op : Op) (a b : UInt64) : UInt64 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .neg => 0 - a

def phaseOf (t : Float) : Phase :=
  if t < 273.15 then .solid else if t < 373.15 then .liquid else .gas

def isGas (p : Phase) : Bool := p == .gas

/-- A heat capacity, with a wildcard that binds the phase and an `if` on its equality. -/
def heat (p : Phase) : Float :=
  match p with
  | .solid => 2.1
  | q => if q = .gas then 2.0 else 4.2

def ofWord (w : UInt64) : Op :=
  if w == 0 then .add else if w == 1 then .sub else if w == 2 then .mul else .neg

def step (c : Calc) (op : Op) (x : UInt64) : Calc :=
  { value := apply op c.value x, steps := c.steps + 1, last := op }

def same (a b : Op) : Bool := decide (a = b)

def differ (a b : Op) : Bool := a != b

/-- The calculator after the operations of `ops` with the operands of `xs`. -/
def run (ops : Array Op) (xs : Array UInt64) : Calc :=
  LeanExe.loop ops.size.toUInt64 ⟨0, 0, .add⟩ fun i c => step c ops[i.toNat]! xs[i.toNat]!

def phases (ts : Array Float) : Array Phase :=
  LeanExe.build ts.size.toUInt64 fun i => phaseOf ts[i.toNat]!

def countGas (ps : Array Phase) : UInt64 :=
  LeanExe.loop ps.size.toUInt64 0 fun i acc => if ps[i.toNat]! == .gas then acc + 1 else acc

/-- Element `i` melted, in place: a `match` on an array element. -/
def melt (ps : Array Phase) (i : UInt64) : Array Phase :=
  ps.set! i.toNat (match ps[i.toNat]! with
    | .solid => .liquid
    | p => p)

def lastOp (c : Calc) : Op := c.last

def notSame (a b : Op) : Bool := decide (a ≠ b)

def wordsDiffer (x y : UInt64) : Bool := decide (x ≠ y)

def ifDiffer (a b : Op) (x : UInt64) : UInt64 := if a ≠ b then x else 0

/-- A `let` of a loop over a literal count in an alternative whose result is an enumeration. -/
def cool (p : Phase) (k : UInt64) : Phase :=
  match p with
  | .solid =>
    let n := LeanExe.loop 30000 k fun _ a => a + 1
    if n < 5 then .liquid else .gas
  | q => q

/-- A match on a call. -/
def phaseHeat (t : Float) : Float :=
  match phaseOf t with
  | .gas => 2.0
  | _ => 4.0

/-- A match on a structure field. -/
def undo (c : Calc) : UInt64 :=
  match c.last with
  | .add => c.value - 1
  | .sub => c.value + 1
  | _ => c.value

/-- Nested matches. -/
def combine (a b : Op) : UInt64 :=
  match a with
  | .add =>
    match b with
    | .add => 1
    | _ => 2
  | _ => 3

inductive Only where
  | only
  deriving Inhabited, DecidableEq

instance : Flat Only UInt64 := ⟨fun _ => 0⟩

def onlyWord (u : Only) : UInt64 :=
  match u with
  | .only => 7

/-- An enumeration in a pair. -/
def tagged (a : Op) (x : UInt64) : Op × UInt64 := (a, x + 1)

/-- `Flat.flat` in the program. -/
def opCode (a : Op) : UInt64 := Flat.flat a + 100

/-- An enumeration whose words are not its constructor indices. -/
inductive Level where
  | low | high
  deriving Inhabited, DecidableEq

instance : Flat Level UInt64 := ⟨fun | .low => 0 | .high => 200⟩

def raise (l : Level) : Level :=
  match l with
  | .low => .high
  | .high => .high

def isHigh (l : Level) : Bool := l == .high

/-- The first phase, the default `solid` for an empty array. -/
def firstPhase (ps : Array Phase) : Phase := ps[(0 : UInt64).toNat]!

verified_compile compiled := [apply, phaseOf, isGas, heat, ofWord, step, same, differ, run, phases,
  countGas, melt, lastOp, notSame, wordsDiffer, ifDiffer, cool, phaseHeat, undo, combine, onlyWord,
  tagged, opCode, raise, isHigh, firstPhase]

end Verified.Examples.Enums
