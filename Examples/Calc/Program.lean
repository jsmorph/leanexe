import LeanExe.Loop

/-!
A calculator over an enumeration of operations and a structure of state: the first
programs with user-defined types.
-/

namespace Examples.Calc

/-- An arithmetic operation on words. -/
inductive Op
  | add | sub | mul | div

/-- A calculator's state: its value, the number of steps taken, and the last operation. -/
structure Calc where
  value : UInt64
  steps : UInt64
  last : Op

/-- `op` applied to `a` and `b`, with `UInt64` arithmetic. -/
def Op.apply (op : Op) (a b : UInt64) : UInt64 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b
  | .div => a / b

/-- The operation that the word `w` encodes: 0 is addition, 1 subtraction, 2
multiplication, and any other word division. -/
def Op.ofWord (w : UInt64) : Op :=
  if w = 0 then .add else if w = 1 then .sub else if w = 2 then .mul else .div

/-- Addition and subtraction undo each other; the other operations map to themselves. -/
def Op.inverse : Op → Op
  | .add => .sub
  | .sub => .add
  | op => op

/-- `c` after applying `op` with operand `x`. -/
def Calc.step (c : Calc) (op : Op) (x : UInt64) : Calc :=
  { c with value := op.apply c.value x, steps := c.steps + 1, last := op }

/-- `c` with a last addition or subtraction of `x` undone; other states are unchanged. -/
def Calc.undo (c : Calc) (x : UInt64) : Calc :=
  match c with
  | { value, steps, last := .add } => { value := value - x, steps, last := .add }
  | { value, steps, last := .sub } => { value := value + x, steps, last := .sub }
  | _ => c

/-- The calculator after the instructions in `words`, two words each: the operation and the
operand. -/
def calcRun (words : Array UInt64) : Calc :=
  LeanExe.loop (words.size.toUInt64 / 2) { value := 0, steps := 0, last := .add } fun i c =>
    c.step (Op.ofWord words[(2 * i).toNat]!) words[(2 * i + 1).toNat]!

end Examples.Calc
