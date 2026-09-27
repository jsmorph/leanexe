import LeanExe.Extract.ScalarFunc

namespace PropositionLetTest

def propositionLetNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if (let flag := f (x == 0); let word := x + flag.toUInt64; f (word != y)) ∧ x < y then x + y else x - y

def propositionLetWord (x y : UInt64) : UInt64 :=
  if (let word := x + y; word < x ∨ word = y) then x + 1 else y + 2

def propositionLetDecision (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let flag := decide ((let saved := f (x != 0); !saved) ∨ (let word := x + 1; word ≤ y))
  flag.toUInt64 + x

def propositionLetDependent (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if _h : (let saved := f (x == 0); saved) ∧ x < y then x + 3 else y + 7

def propositionLetUnused (x y : UInt64) : UInt64 :=
  if (let _saved := x == y; True) ∧ (let _word := x + y; False) then x else y + 1

def propositionLetHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let g := fun b : Bool => if (let saved := f b; !saved) ∧ x < y then f true else f false
  (g true).toUInt64 + (g false).toUInt64 + y

def rangePropositionLetStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != 0
    if (let saved := f (i.toUInt64 != seed); saved || f true) ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangePropositionLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n != seed
    if a = 0 ∨ (let flag := f i.toUInt64; !flag) then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangePropositionLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let mut a := if (let saved := f true; saved) ∧ count < seed then seed + 1 else seed
  for i in [:count.toNat] do
    if (let word := a + i.toUInt64; word < seed) then a := a + 2 else a := a + 1
  return a + (decide ((let saved := f true; saved) ∨ a = seed)).toUInt64

def rangePropositionLetHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if (let flag := f b; !flag) ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if (let flag := g (a == 0); flag) ∧ i.toUInt64 < a then break
    a := a + (f (g true)).toUInt64 + 1
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PropositionLetTest

run_elab do
  let some info := (← Lean.getEnv).find? `PropositionLetTest.propositionLetUnused | throwError "missing"
  let some value := info.value? | throwError "missing"
  Lean.logInfo m!"raw: {repr value}"
  let .lam _ _ (.lam _ _ branch _) _ := value | throwError "shape"
  let args := branch.getAppArgs
  Lean.logInfo m!"condition: {args[1]!}"
  Lean.logInfo m!"decision: {args[2]!}"
  Lean.logInfo m!"guard: {repr (LeanExe.Extract.Core.guardOperands? args[1]!)}"
  if let some guard := LeanExe.Extract.Core.guardOperands? args[1]! then
    Lean.logInfo m!"canonical: {guard.evidence}"
    Lean.logInfo m!"evidence matches: {LeanExe.Extract.Core.guardDecision? guard args[2]!}"
    for operand in guard.operands do
      Lean.logInfo m!"operand: {operand}"
