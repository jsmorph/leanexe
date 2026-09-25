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

def rangeInputs : List (UInt64 × UInt64) :=
  [0, 1, 2, 7, 16, 31].flatMap fun count =>
    [0, 1, 0x8000000000000000, 0xffffffffffffffff].map fun seed => (count, seed)

def rangeCases : List (String × (UInt64 → UInt64 → UInt64)) :=
  [("rangeIndexed", rangeIndexed), ("rangeIndexFree", rangeIndexFree),
   ("rangeBindings", rangeBindings), ("rangeChoice", rangeChoice),
   ("rangeBeforeAfter", rangeBeforeAfter), ("rangeCaptured", rangeCaptured)]

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
