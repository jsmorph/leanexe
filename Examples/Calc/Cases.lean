import Examples.Calc.Program
import Examples.Host

/-! The module cases of `calculator`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Calc

open Examples.Host

/-- A calculator state as the host's three result words. -/
def calcWords (c : Calc) : String := s!"{c.value},{c.steps},{c.last.ctorIdx}"

/-- A calculator state as the host's three argument words. -/
def calcArgs (c : Calc) : List String := [u c.value, u c.steps, u c.last.ctorIdx.toUInt64]

def calculatorCases : IO Unit := do
  let ops := [Op.add, .sub, .mul, .div]
  let operands : List (UInt64 × UInt64) :=
    [(0, 0), (7, 0), (0, 7), (17, 5), (5, 17), (maxU, 2), (maxU, maxU), (2 ^ 32, 2 ^ 32)] ++
      (List.range 8).map fun i => (rw i, rw (i + 50) % 1000)
  for op in ops do
    line "calculator" "inverse" "i64" [u op.ctorIdx.toUInt64] (toString op.inverse.ctorIdx)
    for (a, b) in operands do
      line "calculator" "apply" "i64" [u op.ctorIdx.toUInt64, u a, u b] (toString (op.apply a b))
  for w in [0, 1, 2, 3, 4, 7, maxU] do
    line "calculator" "ofWord" "i64" [u w] (toString (Op.ofWord w).ctorIdx)
  let states : List Calc :=
    ops.flatMap fun op => [⟨0, 0, op⟩, ⟨17, 3, op⟩, ⟨maxU, maxU, op⟩, ⟨rw 3, rw 4, op⟩]
  for c in states do
    for x in [0, 1, 5, maxU, rw 9] do
      line "calculator" "undo" "list:i64,i64,i64" (calcArgs c ++ [u x]) (calcWords (c.undo x))
      for op in ops do
        line "calculator" "step" "list:i64,i64,i64" (calcArgs c ++ [u op.ctorIdx.toUInt64, u x])
          (calcWords (c.step op x))
  for count in [0, 1, 2, 5, 17] do
    for seed in [0, 1, 2] do
      let ws := (List.range (2 * count + seed % 2)).map fun k =>
        if k % 2 = 0 then UInt64.ofNat ((seed + k) % 5) else rw (seed * 31 + k) % 100
      line "calculator" "calcRun" "list:i64,i64,i64" [arrU ws] (calcWords (calcRun ws.toArray))

def cases : IO Unit := do
  calculatorCases

end Examples.Calc
