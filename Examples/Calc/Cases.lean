import Examples.Calc.Program
import TestSupport.Host

/-! The module cases of `calculator`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Calc

open TestSupport.Host

/-- A calculator state as the host's three result words. -/
def calcWords (c : Calc) : String := s!"{c.value},{c.steps},{c.last.ctorIdx}"

/-- A calculator state as the host's three argument words. -/
def calcArgs (c : Calc) : List String := [u c.value, u c.steps, u c.last.ctorIdx.toUInt64]

/-- The operations, in the order of their constructors. -/
def ops : List Op := [.add, .sub, .mul, .div]

/-- The operand pairs of the cases of `apply`. -/
def operands : List (UInt64 × UInt64) :=
  [(0, 0), (7, 0), (0, 7), (17, 5), (5, 17), (maxU, 2), (maxU, maxU), (2 ^ 32, 2 ^ 32)] ++
    (List.range 8).map fun i => (rw i, rw (i + 50) % 1000)

/-- The words of the cases of `ofWord`. -/
def wordArgs : List UInt64 := [0, 1, 2, 3, 4, 7, maxU]

/-- The states of the cases of `step` and `undo`. -/
def states : List Calc :=
  ops.flatMap fun op => [⟨0, 0, op⟩, ⟨17, 3, op⟩, ⟨maxU, maxU, op⟩, ⟨rw 3, rw 4, op⟩]

/-- The operands of the cases of `step` and `undo`. -/
def operandArgs : List UInt64 := [0, 1, 5, maxU, rw 9]

/-- The instruction words of the cases of `calcRun`: for each count and seed, `count`
instructions of two words, and one word more for an odd seed. -/
def runArgs : List (List UInt64) :=
  [0, 1, 2, 5, 17].flatMap fun count => [0, 1, 2].map fun seed =>
    (List.range (2 * count + seed % 2)).map fun k =>
      if k % 2 = 0 then UInt64.ofNat ((seed + k) % 5) else rw (seed * 31 + k) % 100

def calculatorCases : IO Unit := do
  for op in ops do
    line "calculator" "inverse" "i64" [u op.ctorIdx.toUInt64] (toString op.inverse.ctorIdx)
    for (a, b) in operands do
      line "calculator" "apply" "i64" [u op.ctorIdx.toUInt64, u a, u b] (toString (op.apply a b))
  for w in wordArgs do
    line "calculator" "ofWord" "i64" [u w] (toString (Op.ofWord w).ctorIdx)
  for c in states do
    for x in operandArgs do
      line "calculator" "undo" "list:i64,i64,i64" (calcArgs c ++ [u x]) (calcWords (c.undo x))
      for op in ops do
        line "calculator" "step" "list:i64,i64,i64" (calcArgs c ++ [u op.ctorIdx.toUInt64, u x])
          (calcWords (c.step op x))
  for ws in runArgs do
    line "calculator" "calcRun" "list:i64,i64,i64" [arrU ws] (calcWords (calcRun ws.toArray))

def cases : IO Unit := do
  calculatorCases

end Examples.Calc
