import Lean
open Lean

namespace ArithmeticMilestone

def constant : UInt64 := 18446744073709551615
def wrapping (x y : UInt64) : UInt64 := (x + 17) * (y - 3)
def quotient (x y : UInt64) : UInt64 := x / y
def remainder (x y : UInt64) : UInt64 := x % y
def shifts (x y : UInt64) : UInt64 := (x <<< y) ^^^ (x >>> y)
def nested (x y : UInt64) : UInt64 :=
  (((x + 7) * (y - 3)) / (x % (y + 1))) +
    (((x &&& y) ||| (x ^^^ y)) <<< ((x >>> y) + 64))
def order (x y : UInt64) : UInt64 := x - y

def bindings (x y : UInt64) : UInt64 :=
  let a := x + y
  let b := a * x
  (b - a) / (y + 1)
def shadowed (x y : UInt64) : UInt64 :=
  let x := x - y
  let y := x + y
  x ^^^ y
def nestedBindings (x y : UInt64) : UInt64 :=
  let a := (let b := x / y; b + (x % y))
  a * (let b := y - x; b + 1)
def unusedBinding (x y : UInt64) : UInt64 :=
  let _ignored := x / (y - y)
  x - y
def boundConstant : UInt64 :=
  let x : UInt64 := 18446744073709551615
  x + 2

def compareEq (x y : UInt64) : UInt64 := if x = y then x + 1 else y - 1
def compareLt (x y : UInt64) : UInt64 := if x < y then x / y else y / x
def compareLe (x y : UInt64) : UInt64 := if x ≤ y then x * 3 else y + 7
def compareBEq (x y : UInt64) : UInt64 := if x == y then x ^^^ 17 else y <<< x
def compareBNe (x y : UInt64) : UInt64 := if x != y then x - y else x + y
def nestedChoice (x y : UInt64) : UInt64 :=
  if x > y then (if x = 0 then 11 else x % y)
  else if x ≥ y then x + 19 else y >>> x
def choiceBindings (x y : UInt64) : UInt64 :=
  let a := if x = y then x + 7 else x - y
  if a != y then (let b := a * y; b + 1) else a / y
def choiceOperands (x y : UInt64) : UInt64 :=
  if (if x < y then x + 1 else y - 1) = (if y ≤ x then x - y else y - x)
  then x + y else x * y

def doReturn (x y : UInt64) : UInt64 := Id.run do
  return x + y

def doBind (x y : UInt64) : UInt64 := Id.run do
  let a := x + y
  let b ← pure (a * x)
  let c ← pure (b / y)
  return (c + a) % (x + 1)

def doUpdates (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  a := a + y
  a := a * x
  return a - y

def doEarly (x y : UInt64) : UInt64 := Id.run do
  if x < y then return x + 1
  if x = y then return x / y
  return y + 2

def doNested (x y : UInt64) : UInt64 := Id.run do
  let a ← (do
    let b := x / y
    return b + x)
  return (Id.run do return a + y) % y

def doBranches (x y : UInt64) : UInt64 := Id.run do
  if x ≥ y then
    let a ← pure (x - y)
    return a * x
  else
    let b ← pure (y - x)
    return b / y

def doConstant : UInt64 := Id.run do
  let mut value : UInt64 := 18446744073709551615
  value := value + 2
  return value

def localFunction (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 => (z + x) / y
  f x + f y

def capturedShadow (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 => z - x
  let x := y + 17
  f x + x

def chainedFunctions (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 => z + x
  let g := fun z : UInt64 => f (z * y)
  g x + f y

def nestedFunctions (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 =>
    let g := fun z : UInt64 => z * x + y
    g z + z
  f x ^^^ f y

def unusedFunction (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => (z + x) / (y - y)
  x - y

def doJoined (x y : UInt64) : UInt64 := Id.run do
  let a ← if x < y then pure (x + 1) else pure (y - 1)
  return a * x

def doBranchUpdates (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  if a ≤ y then a := a + y else a := a - y
  a := a * x
  if a != y then a := a / y
  return a + 7

def rangeIndexed (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeIndexFree (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    a := a + 3
  return a

def rangeBindings (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let index := UInt64.ofNat i
    let delta := (index + seed) / (index % 3)
    a := a + delta
    a := (a * 7) ^^^ index
  return a

def rangeChoice (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    a := if a < 7 then a + UInt64.ofNat i else (a * 3) ^^^ UInt64.ofNat i
  return a

def rangeBeforeAfter (n seed : UInt64) : UInt64 := Id.run do
  let offset := seed * 3
  let count ← pure (n % 17)
  let mut a := offset
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i * offset
  return a + offset

def rangeCaptured (n seed : UInt64) : UInt64 := Id.run do
  let oldSeed := seed + n
  let mut a := seed
  for i in [:n.toNat] do
    let seed := UInt64.ofNat i
    a := (let update := fun x : UInt64 => (x + oldSeed) ^^^ seed; update a)
  return a - oldSeed

def rangeConstant : UInt64 := Id.run do
  let count : UInt64 := 7
  let mut a : UInt64 := 18446744073709551615
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeLocalFunction (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let index := UInt64.ofNat i
    let f := fun x : UInt64 => (x + index) ^^^ seed
    a := f a
  return a

def rangeChainedFunctions (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let f := fun x : UInt64 => x + a
    let g := fun x : UInt64 => if x < 7 then f (x + UInt64.ofNat i) else f (x / seed)
    a := g a
    a := f a
  return a

def rangeUnusedFunction (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let _f := fun x : UInt64 => x / (a - a)
    a := a + UInt64.ofNat i
  return a

def rangeMonadic (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let index ← pure (UInt64.ofNat i)
    let delta ← pure (if a < 7 then a + index else seed / index)
    a := (a + delta) ^^^ index
  return a

def rangeNestedDo (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let f := fun x : UInt64 => x + UInt64.ofNat i
    let value ← (do
      let x ← pure (f a)
      let y := if x == 0 then seed else x / (seed - seed)
      return x + y)
    a := value * 3
  return a

def rangeUnusedBind (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let _ignored ← pure (a / (UInt64.ofNat i - UInt64.ofNat i))
    let delta ← pure (UInt64.ofNat i + 1)
    a := a + delta
  return a

def rangeMonadicJoined (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let index ← pure (UInt64.ofNat i)
    let delta ← if a < 7 then pure (a + index) else pure (seed / index)
    a := (a + delta) ^^^ index
  return a

def rangeBranchUpdates (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let index := UInt64.ofNat i
    if a ≤ seed then a := a + index else a := a - index
    a := a * 3
    if index != 0 then a := a / index
  return a

def rangeContinue (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let index := UInt64.ofNat i
    if index % 3 == 0 then continue
    let delta ← pure (a + index)
    a := (a ^^^ delta) + seed
  return a

def rangeNestedBranches (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let index := UInt64.ofNat i
    if a < 7 then
      if index == 0 then a := a + seed else a := a + index
    else
      let f := fun x : UInt64 => (x * 7) ^^^ index
      a := f a
    let delta ← if index < 3 then pure (a + 1) else pure (a % index)
    a := a + delta
  return a

def rangeBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if a % 7 == UInt64.ofNat i then break
    a := a + 3
  return a

def rangeBreakUpdated (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
    if a < 7 then break
    a := a * 3
  return a

def rangeBreakJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let index := UInt64.ofNat i
    let delta ← if a < seed then pure (a + index) else pure (seed / index)
    if delta == 0 then break
    a := a + delta
  return a

def rangeBreakBeforeAfter (count seed : UInt64) : UInt64 := Id.run do
  let offset := seed * 3 + 1
  let mut a := offset
  for i in [:count.toNat] do
    let add := fun x : UInt64 => x + offset + UInt64.ofNat i
    a := add a
    if a % 5 == 0 then break
  return a * 7 + seed

def rangeBreakBranchUpdates (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if a < 7 then a := a + UInt64.ofNat i else a := a / 3
    if a == seed then break
    a := a + 1
  return a

def rangeContinueBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if UInt64.ofNat i % 3 == 0 then continue
    a := a + UInt64.ofNat i
    if a % 5 == 0 then break
  return a + 1


def rangeDoneFunction (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish := fun x : UInt64 =>
      if x % 3 == 0 then pure (.done (x + seed)) else pure (.yield (x + UInt64.ofNat i))
    finish a

def rangeDoneUnitFunction (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish := fun (_ : Unit) (x : UInt64) =>
      if x % 3 == seed % 3 then pure (.done (x + 1)) else pure (.yield (x + UInt64.ofNat i))
    finish () (a + UInt64.ofNat i + 1)

def rangeUnusedDone (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:count.toNat] do
    let _finish : UInt64 → Id (ForInStep UInt64) := fun x => pure (.done x)
    a := a + 1
  return a

def rangeDirectSteps (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    if UInt64.ofNat i == seed % 7 then .done (a + 9)
    else .yield (a + UInt64.ofNat i + 1)

def rangeDirectFunction (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → ForInStep UInt64 := fun x =>
      if x % 5 == seed % 5 then .done (x + 7) else .yield (x + UInt64.ofNat i)
    finish (a + 1)

def rangeDirectUnitFunction (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : Unit → UInt64 → ForInStep UInt64 := fun _ x =>
      if x % 3 == seed % 3 then .done (x * 3) else .yield (x + UInt64.ofNat i)
    finish () (a + UInt64.ofNat i + 1)

def rangeNatEmpty (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:0] do
    a := a + UInt64.ofNat i + 1
  return a + n

def rangeNatOne (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:1] do
    a := a + n + UInt64.ofNat i
  return a

def rangeNatLiteral (limit seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:8] do
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == limit then break
  return a

def rangeNatDirect (limit seed : UInt64) : UInt64 :=
  forIn (m := Id) [:31] seed fun i a =>
    if UInt64.ofNat i == limit then .done (a + 9) else .yield (a * 3 + 1)

def rangeNatMax (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:18446744073709551615] seed fun _ a => .done (a + n)

def rangeInputs : List (UInt64 × UInt64) :=
  [0, 1, 2, 7, 16, 31].flatMap fun count =>
    [0, 1, 0x8000000000000000, 0xffffffffffffffff].map fun seed => (count, seed)

def rangeCases : List (String × (UInt64 → UInt64 → UInt64)) :=
  [("rangeIndexed", rangeIndexed), ("rangeIndexFree", rangeIndexFree),
   ("rangeBindings", rangeBindings), ("rangeChoice", rangeChoice),
   ("rangeBeforeAfter", rangeBeforeAfter), ("rangeCaptured", rangeCaptured),
   ("rangeLocalFunction", rangeLocalFunction), ("rangeChainedFunctions", rangeChainedFunctions),
   ("rangeUnusedFunction", rangeUnusedFunction), ("rangeMonadic", rangeMonadic),
   ("rangeNestedDo", rangeNestedDo), ("rangeUnusedBind", rangeUnusedBind),
   ("rangeMonadicJoined", rangeMonadicJoined), ("rangeBranchUpdates", rangeBranchUpdates),
   ("rangeContinue", rangeContinue), ("rangeNestedBranches", rangeNestedBranches),
   ("rangeBreak", rangeBreak),
   ("rangeBreakUpdated", rangeBreakUpdated),
   ("rangeBreakJoined", rangeBreakJoined),
   ("rangeBreakBeforeAfter", rangeBreakBeforeAfter),
   ("rangeBreakBranchUpdates", rangeBreakBranchUpdates),
   ("rangeContinueBreak", rangeContinueBreak),
   ("rangeDoneFunction", rangeDoneFunction),
   ("rangeDoneUnitFunction", rangeDoneUnitFunction),
   ("rangeUnusedDone", rangeUnusedDone),
   ("rangeDirectSteps", rangeDirectSteps),
   ("rangeDirectFunction", rangeDirectFunction),
   ("rangeDirectUnitFunction", rangeDirectUnitFunction),
   ("rangeNatEmpty", rangeNatEmpty),
   ("rangeNatOne", rangeNatOne),
   ("rangeNatLiteral", rangeNatLiteral),
   ("rangeNatDirect", rangeNatDirect),
   ("rangeNatMax", rangeNatMax)]

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

def cases : List (String × (UInt64 → UInt64 → UInt64)) :=
  [("wrapping", wrapping), ("quotient", quotient), ("remainder", remainder),
   ("shifts", shifts), ("nested", nested), ("order", order),
   ("bindings", bindings), ("shadowed", shadowed), ("nestedBindings", nestedBindings),
   ("unusedBinding", unusedBinding), ("compareEq", compareEq), ("compareLt", compareLt),
   ("compareLe", compareLe), ("compareBEq", compareBEq), ("compareBNe", compareBNe),
   ("nestedChoice", nestedChoice), ("choiceBindings", choiceBindings), ("choiceOperands", choiceOperands),
   ("doReturn", doReturn), ("doBind", doBind), ("doUpdates", doUpdates),
   ("doEarly", doEarly), ("doNested", doNested), ("doBranches", doBranches),
   ("localFunction", localFunction), ("capturedShadow", capturedShadow),
   ("chainedFunctions", chainedFunctions), ("nestedFunctions", nestedFunctions),
   ("unusedFunction", unusedFunction), ("doJoined", doJoined), ("doBranchUpdates", doBranchUpdates)]

end ArithmeticMilestone

def main : IO Unit := do
  IO.println (Json.compress (Json.mkObj [
    ("name", toJson "constant"), ("args", Json.arr #[]),
    ("expected", toJson (toString ArithmeticMilestone.constant))]))
  IO.println (Json.compress (Json.mkObj [
    ("name", toJson "boundConstant"), ("args", Json.arr #[]),
    ("expected", toJson (toString ArithmeticMilestone.boundConstant))]))
  IO.println (Json.compress (Json.mkObj [
    ("name", toJson "doConstant"), ("args", Json.arr #[]),
    ("expected", toJson (toString ArithmeticMilestone.doConstant))]))
  IO.println (Json.compress (Json.mkObj [
    ("name", toJson "rangeConstant"), ("args", Json.arr #[]),
    ("expected", toJson (toString ArithmeticMilestone.rangeConstant))]))
  for (name, source) in ArithmeticMilestone.cases do
    for (x, y) in ArithmeticMilestone.inputs do
      IO.println (Json.compress (Json.mkObj [
        ("name", toJson name), ("args", toJson [toString x, toString y]),
        ("expected", toJson (toString (source x y)))]))
  for (name, source) in ArithmeticMilestone.rangeCases do
    for (x, y) in ArithmeticMilestone.rangeInputs do
      IO.println (Json.compress (Json.mkObj [
        ("name", toJson name), ("args", toJson [toString x, toString y]),
        ("expected", toJson (toString (source x y)))]))
