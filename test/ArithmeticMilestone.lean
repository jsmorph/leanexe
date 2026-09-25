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

def compareNe (x y : UInt64) : UInt64 := if x ≠ y then x - y else x + y

def negatedEq (x y : UInt64) : UInt64 := if ¬ (x = y) then x + 7 else y / x

def negatedLt (x y : UInt64) : UInt64 := if ¬ (x < y) then x * 3 else y - 1

def negatedLe (x y : UInt64) : UInt64 := if ¬ (x ≤ y) then x / y else y % x

def negatedGt (x y : UInt64) : UInt64 := if ¬ (x > y) then x ^^^ y else x + 9

def negatedGe (x y : UInt64) : UInt64 := if ¬ (x ≥ y) then x <<< y else y >>> x

def negatedBool (x y : UInt64) : UInt64 :=
  if ¬ (x == y) then (if ¬ (x != y) then x + 1 else y - x) else x * 7

def doubleNegation (x y : UInt64) : UInt64 :=
  if ¬ ¬ (x ≤ y) then (if ¬ (x ≠ y) then x + 1 else y + 3) else x - y

def negatedBindings (x y : UInt64) : UInt64 := Id.run do
  let f := fun z : UInt64 => if ¬ (z < y) then z + 1 else z * 3
  let result ← if f x ≠ f y then pure (x + y) else pure (x / y)
  return if ¬ (result == x) then result * 7 else result + 9

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

def rangeStepRun (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => Id.run do
    let x ← pure (a + UInt64.ofNat i)
    if x % 5 == seed % 5 then return .done (x + 7)
    return .yield (x * 3 + 1)

def rangeStepPure (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    pure (if UInt64.ofNat i == seed % 7 then .done (a + 9) else .yield (a + 1))

def rangeStepLet (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let result : ForInStep UInt64 :=
      if UInt64.ofNat i == seed % 3 then .done (a + 7) else .yield (a + UInt64.ofNat i)
    let alias := result
    pure alias

def rangeStepCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let result : ForInStep UInt64 :=
      if a % 5 == seed % 5 then .done (a + 3) else .yield (a + UInt64.ofNat i)
    let finish : UInt64 → Id (ForInStep UInt64) := fun x =>
      if x < 7 then pure result else pure (.yield (x + 1))
    finish (a + 1)

def rangeStepBind (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let result ← pure (if UInt64.ofNat i == seed % 7 then .done (a + 9) else .yield (a + 1))
    let alias ← pure result
    return alias

def rangeStepIdLet (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let result : Id (ForInStep UInt64) := do
      let x ← pure (a + UInt64.ofNat i)
      if x % 7 == seed % 7 then return .done (x + 1)
      return .yield (x * 3)
    result

def rangeStepUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let _ignored ← pure (ForInStep.done (a + 99))
    let result : ForInStep UInt64 := .yield (a + UInt64.ofNat i + 1)
    return result

def rangeStepWrappedBind (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let computation : Id (Id (ForInStep UInt64)) := Id.run do
      let x ← pure (a + UInt64.ofNat i)
      if x % 3 == seed % 3 then return .done (x + 11)
      return .yield (x + 1)
    @Bind.bind Id (@Monad.toBind Id Id.instMonad) (Id (Id (ForInStep UInt64))) (Id (Id (ForInStep UInt64)))
      computation (fun result => pure result)

def rangeStepJoined (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let result ← if UInt64.ofNat i == seed % 7 then pure (.done (a + 9)) else pure (.yield (a + 1))
    let alias ← pure result
    return alias

def rangeResultFunction (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : ForInStep UInt64 → Id (ForInStep UInt64) := fun result =>
      if a % 3 == 0 then pure (.done (a + seed)) else pure result
    finish (if UInt64.ofNat i == seed % 7 then .done (a + 9) else .yield (a + 1))

def rangeResultChained (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let first : ForInStep UInt64 → ForInStep UInt64 := fun result =>
      if a < 7 then result else .yield (a / 3)
    let second : ForInStep UInt64 → Id (ForInStep UInt64) := fun result =>
      let alias := first result
      if UInt64.ofNat i == 7 then pure (.done (a + 5)) else pure alias
    second (.yield (a * 7 + seed))

def rangeResultCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let captured : ForInStep UInt64 := .done (a + UInt64.ofNat i)
    let finish : ForInStep UInt64 → ForInStep UInt64 := fun result =>
      if a % 5 == seed % 5 then captured else result
    let a := a + 17
    finish (.yield a)

def rangeResultUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _unused : ForInStep UInt64 → Id (ForInStep UInt64) := fun result => pure result
    let ignore : ForInStep UInt64 → ForInStep UInt64 := fun _ => .yield (a + UInt64.ofNat i + 1)
    ignore (.done (a + 99))

def rangeResultWrapped (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : Id (Id (ForInStep UInt64)) → Id (Id (ForInStep UInt64)) := fun result =>
      Id.run do
        let x ← pure (a + UInt64.ofNat i)
        if x % 5 == seed % 5 then return .done (x + 1)
        return result
    finish (pure (.yield (a + 3)))

def rangeNegatedBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
    if ¬ (a % 5 ≠ seed % 5) then break
    a := a + 7
  return a

def rangeNegatedContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ (UInt64.ofNat i < seed % 7) then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeNegatedJoin (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let result ← if ¬ (UInt64.ofNat i < seed % 7) then pure (.done (a + 11)) else pure (.yield (a + 1))
    return result

def rangeFromOne (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat] do
    a := a * 3 + UInt64.ofNat i
  return a

def rangeIntervalLiteral (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [3:8] do
    a := a + UInt64.ofNat i + count
  return a

def rangeIntervalEmpty (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [8:3] seed fun i a => .yield (a + UInt64.ofNat i + count)

def rangeIntervalEqual (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [7:7] seed fun i a => .done (a + UInt64.ofNat i + count)

def rangeIntervalBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [5:count.toNat] do
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == 7 then break
    a := a * 3
  return a

def rangeIntervalContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat] do
    if UInt64.ofNat i % 3 == 0 then continue
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == 11 then break
  return a

def rangeIntervalCapture (count seed : UInt64) : UInt64 := Id.run do
  let delta := seed + 7
  let mut a := seed * 3
  for i in [2:(count + 1).toNat] do
    let f := fun x : UInt64 => x + delta + UInt64.ofNat i
    a := f a
  return a - delta

def rangeIntervalJoin (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [3:count.toNat] seed fun i a => do
    let result ← if UInt64.ofNat i == 7 then pure (.done (a + 11)) else pure (.yield (a + UInt64.ofNat i))
    return result

def rangeIntervalHigh (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [18446744073709551613:18446744073709551615] seed fun i a =>
    .yield (a + UInt64.ofNat i + count)

def rangeIntervalMaxEmpty (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [18446744073709551615:count.toNat] seed fun i a => .done (a + UInt64.ofNat i)

def rangeIntervalHugeBreak (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [2:18446744073709551615] seed fun i a => .done (a + UInt64.ofNat i + count)

def rangeDynamicStart (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(seed % 7).toNat:count.toNat] do
    a := a * 3 + UInt64.ofNat i
  return a

def rangeDynamicLiteral (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [count.toNat:8] seed fun i a => .yield (a + UInt64.ofNat i)

def rangeDynamicComputed (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(count / 2).toNat:(count + seed % 3).toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeDynamicCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [a.toNat:(a + count).toNat] do
    a := a + UInt64.ofNat i + 7
  return a

def rangeDynamicHigh (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(18446744073709551615 - count).toNat:18446744073709551615] seed fun i a =>
    .yield (a + UInt64.ofNat i)

def rangeDynamicEmpty (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(count + 1).toNat:count.toNat] seed fun i a => .yield (a + UInt64.ofNat i)

def rangeDynamicEqual (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed + count).toNat:(seed + count).toNat] seed fun i a => .done (a + UInt64.ofNat i)

def rangeDynamicHugeBreak (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed % 7).toNat:18446744073709551615] seed fun i a => .done (a + UInt64.ofNat i + count)

def rangeDynamicContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(seed % 5).toNat:count.toNat] do
    if UInt64.ofNat i % 3 == 0 then continue
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == 11 then break
  return a

def rangeDynamicJoin (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed % 5).toNat:count.toNat] seed fun i a => do
    let result ← if UInt64.ofNat i == 7 then pure (.done (a + 11)) else pure (.yield (a + UInt64.ofNat i))
    return result

def rangeDynamicChoice (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(if count < seed then count / 2 else 0).toNat:count.toNat] do
    let f := fun x : UInt64 => x + UInt64.ofNat i
    a := f a
  return a

def rangeStrideTwo (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [0:count.toNat:2] do
    a := a * 3 + UInt64.ofNat i
  return a

def rangeStrideLiteral (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [2:15:3] seed fun i a => .yield (a + UInt64.ofNat i + count)

def rangeStrideDynamic (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(seed % 5).toNat:count.toNat:3] do
    a := a + UInt64.ofNat i
  return a

def rangeStrideCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [a.toNat:(a + count).toNat:3] do
    a := a + UInt64.ofNat i + 7
  return a

def rangeStrideHigh (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(18446744073709551615 - count).toNat:18446744073709551615:2] seed fun i a =>
    .yield (a + UInt64.ofNat i)

def rangeStrideEmpty (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [8:3:7] seed fun i a => .yield (a + UInt64.ofNat i + count)

def rangeStrideHuge (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [0:count.toNat:18446744073709551615] seed fun i a => .yield (a + UInt64.ofNat i + 7)

def rangeStrideHugeTwo (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [0:18446744073709551615:18446744073709551614] seed fun i a => .yield (a + UInt64.ofNat i + count)

def rangeStrideHugeBreak (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [1:18446744073709551615:2] seed fun i a => .done (a + UInt64.ofNat i + count)

def rangeStrideContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:2] do
    if UInt64.ofNat i % 3 == 0 then continue
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == 11 then break
  return a

def rangeStrideJoin (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [2:count.toNat:3] seed fun i a => do
    let result ← if UInt64.ofNat i == 8 then pure (.done (a + 11)) else pure (.yield (a + UInt64.ofNat i))
    return result

def rangeStrideOne (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [2:count.toNat:1] seed fun i a => .yield (a + UInt64.ofNat i)

def binaryOrder (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a - b
  f x y

def binaryCapture (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b : UInt64 => captured + a * 3 - b
  let captured := y * 11
  f captured x

def binaryChained (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a / b + a % b
  let g := fun a b : UInt64 => f (a + b) (a - b)
  g x y

def binaryUnused (x y : UInt64) : UInt64 :=
  let _f := fun a b : UInt64 => (a + x) / (b - y)
  x + y

def binaryDo (x y : UInt64) : UInt64 := Id.run do
  let f : UInt64 → UInt64 → Id UInt64 := fun a b => do
    let c ← pure (a + b)
    return c * x
  let result ← f x y
  return result + x

def binaryNested (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 =>
    let g := fun c d : UInt64 => a * c + b * d
    g x y
  f y x

def binaryChoice (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => if a < b then a + 7 else b - a
  if f x y = x then f y x else f (x + y) (x - y)

def binaryArguments (x y : UInt64) : UInt64 :=
  let g := fun a : UInt64 => a * 3 + 1
  let f := fun a b : UInt64 => a ^^^ (b <<< a)
  f (g x) (g y)

def binaryWrapped (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => Id.run do
    let c ← if a < b then pure (a + 1) else pure (b + 7)
    return c - a
  f x y

def rangeBinaryLocal (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x * 3 + y + UInt64.ofNat i
    a := f a seed
  return a

def rangeBinaryCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:2] do
    let f := fun x y : UInt64 => a + x - y
    a := a + 7
    a := f a (UInt64.ofNat i)
  return a

def rangeBinaryNested (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(seed % 3).toNat:count.toNat] do
    let f := fun x y : UInt64 =>
      let g := fun p q : UInt64 => p * x + q * y + UInt64.ofNat i
      g a seed
    a := f seed a
  return a

def rangeBinaryDo (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : UInt64 → UInt64 → Id UInt64 := fun x y => do
      let c ← if x < y then pure (x + 7) else pure (y + seed)
      return c + UInt64.ofNat i
    let delta ← f a (UInt64.ofNat i)
    if delta % 5 == seed % 5 then break
    a := delta * 3 + 1
  return a

def rangeBinaryContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => if x < y then x + y else x - y
    if f (UInt64.ofNat i) seed % 3 == 0 then continue
    a := f a (UInt64.ofNat i)
    if UInt64.ofNat i == 11 then break
  return a

def rangeBinaryUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => (x + a) / (y - UInt64.ofNat i)
    a := a + UInt64.ofNat i + 1
  return a

def rangeBinaryStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if x == seed % 7 then .done (y + 9) else .yield (y + x + 1)
    finish (UInt64.ofNat i) a

def rangeBinaryStepOrder (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if x < y then .done (x - y) else .yield (y - x)
    finish (UInt64.ofNat i + 3) a

def rangeBinaryStepCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [1:count.toNat:2] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if x % 5 == a % 5 then .done (a + x - y)
      else .yield (y + a + UInt64.ofNat i)
    let a := a + 17
    finish a seed

def rangeBinaryStepChained (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let first : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if x % 7 == seed % 7 then .done (y + 13) else .yield (x + y)
    let second : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      first (x + UInt64.ofNat i) (y * 3)
    second a seed

def rangeBinaryStepNested (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed % 3).toNat:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      let inner : UInt64 → UInt64 → ForInStep UInt64 := fun p q =>
        if p < x then .done (q + y) else .yield (p + q + UInt64.ofNat i)
      inner y a
    finish (a + 1) seed

def rangeBinaryStepDo (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y => do
      let z ← if x < y then pure (x + 3) else pure (y + seed)
      if z % 7 == UInt64.ofNat i then return .done (z * 3)
      return .yield (x + z + 1)
    finish a (UInt64.ofNat i)

def rangeBinaryStepScalar (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let add := fun x y : UInt64 => x * 3 + y + seed
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      let z := add x y
      if z % 5 == 0 then .done (z + 11) else .yield z
    finish a (UInt64.ofNat i)

def rangeBinaryStepUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _unused : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if x == y then .done (a + 99) else .yield (x / y)
    .yield (a + UInt64.ofNat i + 1)

def rangeBinaryStepResult (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if x == seed % 7 then .done (y + 9) else .yield (x + y + 1)
    let use : ForInStep UInt64 → Id (ForInStep UInt64) := fun result => pure result
    let result := finish (UInt64.ofNat i) a
    use result

def rangeBinaryStepWrapped (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → Id (Id (ForInStep UInt64)) := fun x y => Id.run do
      let z ← pure (x + y + UInt64.ofNat i)
      if z % 5 == seed % 5 then return .done (z + 11)
      return .yield (z * 3)
    pure (finish a seed)

def boolNotEqual (x y : UInt64) : UInt64 :=
  if !(x == y) then x - y else x * 3 + 1

def boolNotUnequal (x y : UInt64) : UInt64 :=
  if !(x != y) then x + 7 else y / x

def boolNotTwice (x y : UInt64) : UInt64 :=
  if !(!(x == y)) then x / y else y % x

def boolNotThrice (x y : UInt64) : UInt64 :=
  if !(!(!(x != y))) then x <<< y else y >>> x

def boolNotNested (x y : UInt64) : UInt64 :=
  if !((if !(x == 0) then x + y else y) == (if !(y != 1) then x else y))
  then x ^^^ y else x + 11

def boolNotFunction (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => if !(a == b) then a * 3 + x else b - y
  if !(f x y != f y x) then f (x + y) x else f y (x - y)

def boolNotDo (x y : UInt64) : UInt64 := Id.run do
  let z ← if !(x == y) then pure (x + 7) else pure (y / x)
  let mut a := z
  if !(z != x) then a := a + y else a := a * 3
  return a + 1

def boolNotProposition (x y : UInt64) : UInt64 :=
  if ¬ (!(x == y)) then (if ¬ (!(!(x != y))) then x + 3 else y + 7) else x - y

def rangeBoolNotBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
    if !(a % 5 != seed % 5) then break
    a := a * 3 + 1
  return a

def rangeBoolNotContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:2] do
    if !(UInt64.ofNat i % 3 == seed % 3) then continue
    a := a + UInt64.ofNat i
    if !(!(a % 7 == 0)) then break
  return a

def rangeBoolNotJoin (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let result ← if !(UInt64.ofNat i != seed % 7) then pure (.done (a + 9)) else pure (.yield (a + 1))
    return result

def rangeBoolNotFunction (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed % 3).toNat:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y => do
      let z ← pure (x + y + UInt64.ofNat i)
      if !(!(!(z != seed))) then return .done (z + 17)
      return .yield (z * 3 + 1)
    finish a seed

def rangeOuterUnary (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x : UInt64 => x * 3 + seed
  let mut a := seed
  for i in [:count.toNat] do
    a := f a + UInt64.ofNat i
  return f a

def rangeOuterBinary (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y : UInt64 => x * 3 + y - seed
  let mut a := seed
  for i in [:count.toNat] do
    a := f a (UInt64.ofNat i)
    if a % 7 == 0 then break
  return f a count

def rangeOuterUnit (count seed : UInt64) : UInt64 := Id.run do
  let f := fun (_ : Unit) (x : UInt64) => x + seed + 1
  let mut a := f () seed
  for i in [1:count.toNat:2] do
    a := f () (a + UInt64.ofNat i)
  return f () a

def rangeOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  let f := fun x : UInt64 => x + a
  a := a + 17
  for i in [:count.toNat] do
    a := f a + UInt64.ofNat i
    if !(a % 5 != seed % 5) then break
  return f a

def rangeOuterBounds (count seed : UInt64) : UInt64 := Id.run do
  let endpoint := fun x y : UInt64 => (x + y) % 7
  let mut a := endpoint seed count
  for i in [(endpoint seed 1).toNat:(endpoint count seed + 16).toNat] do
    a := a + UInt64.ofNat i
  return endpoint a seed

def rangeOuterChained (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x : UInt64 => x + seed
  let g := fun x y : UInt64 => f (x * 3) + y
  let mut a := seed
  for i in [:count.toNat] do
    if UInt64.ofNat i % 3 == 0 then continue
    a := g a (UInt64.ofNat i)
  return g a count

def rangeOuterNested (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y : UInt64 =>
    let g := fun z : UInt64 => if !(z == x) then z + y else z * 3
    g seed + g x
  let mut a := f seed count
  for i in [:count.toNat] do
    a := f a (UInt64.ofNat i)
  return f a seed

def rangeOuterDo (count seed : UInt64) : UInt64 := Id.run do
  let f : UInt64 → Id UInt64 := fun x => do
    let z ← if x < seed then pure (x + 3) else pure (x / 3)
    return z + 1
  let mut a ← f seed
  for i in [:count.toNat] do
    let z ← f a
    a := z + UInt64.ofNat i
    if a % 5 == 0 then break
  let result ← f a
  return result

def rangeOuterUnused (count seed : UInt64) : UInt64 := Id.run do
  let _f := fun x y : UInt64 => x / y + seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
  return a

def rangeOuterStep (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y : UInt64 => x * 3 + y + seed
  let result ← forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y => do
      let z ← pure (f x y)
      if z % 5 == seed % 5 then return .done (z + 7)
      return .yield (z + UInt64.ofNat i)
    finish a seed
  return f result count

def rangeLetResult (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i + 1
    return a
  result * 3 + seed

def rangeLetDirect (count seed : UInt64) : UInt64 :=
  let result : UInt64 := forIn (m := Id) [:count.toNat] seed fun i a =>
    if UInt64.ofNat i == seed % 7 then .done (a + 9) else .yield (a * 3 + 1)
  result + count

def rangeLetCapture (count seed : UInt64) : UInt64 :=
  let captured := seed + 7
  let result := Id.run do
    let mut a := captured
    for i in [:count.toNat] do
      a := a + captured + UInt64.ofNat i
    return a
  let captured := result + 11
  result + captured

def rangeLetAliases (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for _ in [:count.toNat] do
      a := a * 3 + 1
    return a
  let alias := result
  let result := alias + 7
  result - alias / 3

def rangeLetUnused (count seed : UInt64) : UInt64 :=
  let _ignored := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i
      if a % 5 == 0 then break
    return a
  seed + count

def rangeLetStride (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [(seed % 3).toNat:count.toNat:2] do
      a := a + UInt64.ofNat i
      if a % 7 == seed % 7 then break
    return a
  if !(result == seed) then result + 11 else result * 3

def rangeLetContinue (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if UInt64.ofNat i % 3 == 0 then continue
      a := a + UInt64.ofNat i
    return a
  result ^^^ seed

def rangeLetMonadic (count seed : UInt64) : UInt64 := Id.run do
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      let x ← pure (a + UInt64.ofNat i)
      a := x * 3
    return a
  let z ← pure (result + 7)
  return z * 3 + seed

def rangeLetHelper (count seed : UInt64) : UInt64 :=
  let f := fun x y : UInt64 => x * 3 + y + seed
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i)
    return a
  let g := fun x : UInt64 => f x result
  g seed + g count

def rangeLetNested (count seed : UInt64) : UInt64 :=
  let outer :=
    let start := seed + 3
    let inner := Id.run do
      let mut a := start
      for i in [1:count.toNat] do
        a := a + UInt64.ofNat i
      return a
    inner * 3 + start
  outer + seed

def complementDirect (x y : UInt64) : UInt64 := UInt64.complement x + y

def complementOperator (x y : UInt64) : UInt64 := ~~~(x + y)

def complementTwice (x y : UInt64) : UInt64 := ~~~(~~~x) + UInt64.complement y

def complementMixed (x y : UInt64) : UInt64 :=
  ((~~~x) &&& y) ||| ((~~~y) ^^^ (x <<< y))

def complementChoice (x y : UInt64) : UInt64 :=
  if !(~~~x == y) then ~~~(x / y) else UInt64.complement (y % x)

def complementFunction (x y : UInt64) : UInt64 :=
  let captured := ~~~(x + 7)
  let f := fun a b : UInt64 => ~~~(a * 3 + b + captured)
  f x y - f y x

def complementDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := ~~~x
  let z ← if x < y then pure (~~~(a + y)) else pure (UInt64.complement y)
  a := a ^^^ z
  return ~~~a

def complementOperand (x y : UInt64) : UInt64 :=
  if (if x == 0 then UInt64.complement y else ~~~x) ≤ (~~~y)
  then (~~~x) <<< (~~~y) else ~~~(x ^^^ y) / (~~~y)

def rangeComplement (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := ~~~(a + UInt64.ofNat i)
    if a % 5 == seed % 5 then break
  return UInt64.complement a

def rangeComplementContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (~~~(UInt64.ofNat i)) % 3 == seed % 3 then continue
    a := a ^^^ (~~~(UInt64.ofNat i + seed))
  return a

def rangeComplementHelper (count seed : UInt64) : UInt64 :=
  let f := fun x y : UInt64 => ~~~(x * 3 + y + seed)
  let result := Id.run do
    let mut a := seed
    for i in [(~~~count).toNat:(~~~count + 3).toNat:2] do
      a := f a (UInt64.ofNat i)
    return a
  f result seed

def rangeComplementStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if UInt64.ofNat i == seed % 7 then .done (UInt64.complement x)
      else .yield (~~~(y + UInt64.ofNat i))
    finish (a + seed) a

def compoundAnd (x y : UInt64) : UInt64 :=
  if x % 2 = 1 ∧ y % 2 = 1 then 11 else 29

def compoundOr (x y : UInt64) : UInt64 :=
  if x % 2 = 1 ∨ y % 2 = 1 then 31 else 47

def compoundNested (x y : UInt64) : UInt64 :=
  if (x < y ∧ x + y ≠ 0) ∨ (x ≥ y ∧ y ≤ x * 3) then x + 13 else y - 17

def compoundNegatedLeaves (x y : UInt64) : UInt64 :=
  if (¬ x = y) ∧ (¬ x < y ∨ !(x == 0)) then ~~~x else ~~~y

def compoundZeroDivisor (x y : UInt64) : UInt64 :=
  if x = 0 ∨ (x / y = 3 ∧ y % x ≠ 0) then x / y + 1 else y % x + 7

def compoundFunction (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b : UInt64 =>
    if (a = b ∨ a < captured) ∧ (b ≠ 0 ∨ a = 0) then a + b else a - b
  f x y + f y x

def compoundDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  let z ← if x = 0 ∨ y = 0 then pure (x + y) else pure (x * y)
  if z ≥ a ∧ y ≠ 1 then a := a + z else a := a - z
  return a ^^^ y

def compoundOperand (x y : UInt64) : UInt64 :=
  if (if x < y ∧ x ≠ 0 then ~~~x else y) < (x + y) ∨ x = y
  then (if x = 0 ∧ y = 0 then 19 else x + y) else ~~~(x + y)

def rangeCompoundBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if UInt64.ofNat i ≥ seed % 5 ∧ a % 3 = 0 then break
  return a

def rangeCompoundContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if UInt64.ofNat i % 3 = 0 ∨ UInt64.ofNat i = seed % 7 then continue
    a := a + UInt64.ofNat i
  return a

def rangeCompoundJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let z ← if a = seed ∨ UInt64.ofNat i < 3 then pure (a + 5) else pure (a - 2)
    if (z > a ∧ a ≠ 0) ∨ (UInt64.ofNat i ≥ 3 ∧ seed = 0) then
      a := z
    else
      a := z + UInt64.ofNat i
    if a = 7 ∨ (a % 5 = 0 ∧ UInt64.ofNat i > 2) then break
  return a

def rangeCompoundHelper (count seed : UInt64) : UInt64 :=
  let f := fun x y : UInt64 =>
    if (x < y ∨ y = 0) ∧ (x + seed ≠ 0 ∨ y ≤ seed) then x + y + 1 else x - y
  let result := Id.run do
    let mut a := seed
    for i in [1:count.toNat:2] do
      a := f a (UInt64.ofNat i)
    return a
  f result seed

def rangeCompoundStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if (UInt64.ofNat i ≥ seed % 5 ∧ x % 3 = 0) ∨ y = 7
      then .done (x + 11) else .yield (y + UInt64.ofNat i + 1)
    finish (a + seed) a

def rangeCompoundResult (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => Id.run do
    let r : ForInStep UInt64 ←
      if (UInt64.ofNat i = seed % 7 ∨ a = 0) ∧ UInt64.ofNat i > 1
      then pure (.done (a + 3)) else pure (.yield (a + UInt64.ofNat i + 1))
    let keep : ForInStep UInt64 → ForInStep UInt64 := fun result => result
    return keep r

def compoundNotAnd (x y : UInt64) : UInt64 :=
  if ¬ (x % 2 = 1 ∧ y % 2 = 1) then 11 else 29

def compoundNotOr (x y : UInt64) : UInt64 :=
  if ¬ (x % 2 = 1 ∨ y % 2 = 1) then 31 else 47

def compoundNotTwice (x y : UInt64) : UInt64 :=
  if ¬ ¬ (x < y ∧ x + y ≠ 0) then x + 13 else y - 17

def compoundNotThrice (x y : UInt64) : UInt64 :=
  if ¬ ¬ ¬ (x ≥ y ∨ y ≤ x * 3) then ~~~x else ~~~y

def compoundNotNested (x y : UInt64) : UInt64 :=
  if ¬ ((¬ (x = 0 ∨ y = 0)) ∧ (x / y = 3 ∨ ¬ (y % x = 0 ∧ x ≠ y)))
  then x / y + 1 else y % x + 7

def compoundNotFunction (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b : UInt64 =>
    if (¬ (a = b ∨ a < captured)) ∨ (¬ (b ≠ 0 ∧ a = 0)) then a + b else a - b
  f x y + f y x

def compoundNotDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  let z ← if ¬ (x = 0 ∨ y = 0) then pure (x + y) else pure (x * y)
  if ¬ ¬ (z ≥ a ∧ y ≠ 1) then a := a + z else a := a - z
  return a ^^^ y

def compoundNotOperand (x y : UInt64) : UInt64 :=
  if (if ¬ (x < y ∧ x ≠ 0) then ~~~x else y) < (x + y) ∧ ¬ (x = y ∨ x = 0)
  then (if ¬ (x = 0 ∧ y = 0) then 19 else x + y) else ~~~(x + y)

def rangeCompoundNotBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if ¬ (UInt64.ofNat i < seed % 5 ∨ a % 3 ≠ 0) then break
  return a

def rangeCompoundNotContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ ¬ (UInt64.ofNat i % 3 = 0 ∨ ¬ (UInt64.ofNat i ≠ seed % 7 ∧ a ≠ 0)) then continue
    a := a + UInt64.ofNat i
  return a

def rangeCompoundNotJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let z ← if ¬ (a = seed ∧ UInt64.ofNat i < 3) then pure (a + 5) else pure (a - 2)
    if (¬ (z > a ∧ a ≠ 0)) ∨ (¬ (UInt64.ofNat i ≥ 3 ∨ seed = 0)) then
      a := z
    else
      a := z + UInt64.ofNat i
    if ¬ (a ≠ 7 ∧ ¬ (a % 5 = 0 ∧ UInt64.ofNat i > 2)) then break
  return a

def rangeCompoundNotStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => Id.run do
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if ¬ ¬ ¬ ((UInt64.ofNat i ≥ seed % 5 ∧ x % 3 = 0) ∨ y = 7)
      then .done (x + 11) else .yield (y + UInt64.ofNat i + 1)
    let r : ForInStep UInt64 ← pure (finish (a + seed) a)
    let keep : ForInStep UInt64 → ForInStep UInt64 := fun result => result
    return keep r

def boolAndTruth (x y : UInt64) : UInt64 :=
  if (x % 2 == 1 && y % 2 == 1) then 11 else 29

def boolOrTruth (x y : UInt64) : UInt64 :=
  if (x % 2 == 1 || y % 2 == 1) then 31 else 47

def boolCompoundNot (x y : UInt64) : UInt64 :=
  if !((x + y == 0) && (x != y)) then ~~~x else ~~~y

def boolCompoundTwice (x y : UInt64) : UInt64 :=
  if !!((x == 0) || !(y == x * 3)) then x + 13 else y - 17

def boolCompoundNested (x y : UInt64) : UInt64 :=
  if !((!(x == 0 || y == 0)) && (x / y == 3 || !(y % x == 0 && x != y)))
  then x / y + 1 else y % x + 7

def boolCompoundFunction (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b : UInt64 =>
    if (!(a == b || a == captured)) || (!(b != 0 && a == 0)) then a + b else a - b
  f x y + f y x

def boolCompoundDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  let z ← if !(x == 0 || y == 0) then pure (x + y) else pure (x * y)
  if !!(z == a && y != 1) then a := a + z else a := a - z
  return a ^^^ y

def boolCompoundOperand (x y : UInt64) : UInt64 :=
  if ((if !(x == y && x != 0) then ~~~x else y) == (x + y)) && !(x == y || x == 0)
  then (if !(x == 0 && y == 0) then 19 else x + y) else ~~~(x + y)

def rangeBoolCompoundBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if !(UInt64.ofNat i % 5 != seed % 5 || a % 3 != 0) then break
  return a

def rangeBoolCompoundContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if !!(UInt64.ofNat i % 3 == 0 || !(UInt64.ofNat i != seed % 7 && a != 0)) then continue
    a := a + UInt64.ofNat i
  return a

def rangeBoolCompoundJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let z ← if !(a == seed && UInt64.ofNat i % 3 == 0) then pure (a + 5) else pure (a - 2)
    if (!(z == a && a != 0)) || (!(UInt64.ofNat i % 3 == 0 || seed == 0)) then
      a := z
    else
      a := z + UInt64.ofNat i
    if !(a != 7 && !(a % 5 == 0 && UInt64.ofNat i != 2)) then break
  return a

def rangeBoolCompoundStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => Id.run do
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if !!!((UInt64.ofNat i % 5 == seed % 5 && x % 3 == 0) || y == 7)
      then .done (x + 11) else .yield (y + UInt64.ofNat i + 1)
    let r : ForInStep UInt64 ← pure (finish (a + seed) a)
    let keep : ForInStep UInt64 → ForInStep UInt64 := fun result => result
    return keep r

def mixedGuardAnd (x y : UInt64) : UInt64 :=
  if (x % 2 == 1 || y % 2 == 1) ∧ x ≠ y then 11 else 29

def mixedGuardOr (x y : UInt64) : UInt64 :=
  if (x % 2 == 1 && y % 2 == 1) ∨ x = y then 31 else 47

def mixedGuardNot (x y : UInt64) : UInt64 :=
  if ¬ (x + y == 0 || x != y) then ~~~x else ~~~y

def mixedGuardNegations (x y : UInt64) : UInt64 :=
  if ¬ ¬ !(x == 0 || !(y == x * 3 && x != y)) then x + 13 else y - 17

def mixedGuardNested (x y : UInt64) : UInt64 :=
  if ¬ ((x < y ∨ !(x == 0 && y == 0)) ∧ ((x + y == 0 || y / x == 3) ∨ ¬ x ≠ y))
  then x / y + 1 else y % x + 7

def mixedGuardFunction (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b : UInt64 =>
    if (¬ (a == b || a == captured)) ∨ (b ≤ captured ∧ !(b != 0 && a == 0)) then a + b else a - b
  f x y + f y x

def mixedGuardDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  let z ← if ¬ (x == 0 || y == 0) then pure (x + y) else pure (x * y)
  if ¬ ((z == a && y != 1) ∨ z < a) then a := a + z else a := a - z
  return a ^^^ y

def mixedGuardOperand (x y : UInt64) : UInt64 :=
  if ((if ¬ (x == y && x != 0) then ~~~x else y) == (x + y) || x != y) ∧ ¬ x < y
  then (if (x != 0 && y != 0) ∨ x ≥ y then 19 else x + y) else ~~~(x + y)

def rangeMixedGuardBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (UInt64.ofNat i % 5 == seed % 5 || a % 3 == 0) ∧ UInt64.ofNat i ≥ seed % 3 then break
  return a

def rangeMixedGuardContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (¬ (UInt64.ofNat i % 3 != 0 && a != 0)) ∨ UInt64.ofNat i = seed % 7 then continue
    a := a + UInt64.ofNat i
  return a

def rangeMixedGuardJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let z ← if ¬ (a == seed && UInt64.ofNat i % 3 == 0) then pure (a + 5) else pure (a - 2)
    if (!(z == a && a != 0)) ∧ (UInt64.ofNat i < 3 ∨ ¬ (seed == 0 || a == seed)) then
      a := z
    else
      a := z + UInt64.ofNat i
    if ¬ ((a != 7 && a % 5 != 0) ∨ UInt64.ofNat i ≤ 2) then break
  return a

def rangeMixedGuardStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => Id.run do
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if ¬ ¬ ((UInt64.ofNat i % 5 == seed % 5 && x % 3 == 0) ∨ ¬ (y == 7 || x == seed))
      then .done (x + 11) else .yield (y + UInt64.ofNat i + 1)
    let r : ForInStep UInt64 ← pure (finish (a + seed) a)
    let keep : ForInStep UInt64 → ForInStep UInt64 := fun result => result
    return keep r

def minimumOrder (x y : UInt64) : UInt64 := min x y

def maximumOrder (x y : UInt64) : UInt64 := max x y

def extremaNested (x y : UInt64) : UInt64 := max (min x y) (min (~~~x) (~~~y))

def extremaClamped (x y : UInt64) : UInt64 :=
  let lo := min x y
  let hi := max x y
  min hi (max lo (x + y))

def extremaFunction (x y : UInt64) : UInt64 :=
  let captured := max x 7
  let f := fun a b : UInt64 => min (max a captured) (b + 17)
  f x y + max (f y x) (min x y)

def extremaDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := min x y
  let z ← if x < y then pure (max a (x + y)) else pure (min a (x * y))
  a := max (a + 3) z
  return min a (x ^^^ y)

def extremaGuard (x y : UInt64) : UInt64 :=
  if (min x y == 0 || max x y == x) ∧ min (x + y) (~~~y) ≤ max x y
  then max (x / y) (y % x) else min (~~~x) (~~~y)

def extremaWrapped (x y : UInt64) : UInt64 :=
  min (x + 1) (y - 1) + max (x * 3) (y <<< x) - min (x >>> y) (~~~y)

def rangeExtremaCount (count seed : UInt64) : UInt64 := Id.run do
  let mut a := min seed 17
  for i in [:(max (count % 17) (seed % 7)).toNat] do
    a := max (a + 1) (UInt64.ofNat i + seed)
  return min a (seed + 31)

def rangeExtremaExit (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if min (UInt64.ofNat i % 3) (seed % 3) == 1 then continue
    a := min (max a (a + UInt64.ofNat i)) (seed + 17)
    if max a (UInt64.ofNat i) % 5 == seed % 5 then break
  return max a seed

def rangeExtremaBounds (count seed : UInt64) : UInt64 :=
  let first := min seed 18446744073709551613
  let result := Id.run do
    let mut a := seed
    for i in [first.toNat:(first + min count 2).toNat] do
      a := max (min a (UInt64.ofNat i)) (a + 1)
    return a
  min (max result seed) (result + count)

def rangeExtremaStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if min x y = seed ∨ (max x y == 0 && UInt64.ofNat i % 3 == 0)
      then .done (max x y) else .yield (min (x + UInt64.ofNat i) (y + 3))
    finish (a + 1) (a + seed)

def literalBoolTrue (x y : UInt64) : UInt64 := if true then x + 3 else y - 1

def literalBoolFalse (x y : UInt64) : UInt64 := if false then x / y else y % x

def literalPropTrue (x y : UInt64) : UInt64 := if True then x ^^^ y else x * y

def literalPropFalse (x y : UInt64) : UInt64 := if False then min x y else max x y

def literalNegations (x y : UInt64) : UInt64 :=
  if !(!(!false)) then
    if ¬¬True then x + y else ~~~x
  else if ¬(!(!true) : Bool) then y else x - y

def literalCompound (x y : UInt64) : UInt64 :=
  if ((true && (x == y || false)) ∧ (False ∨ x ≤ y)) ∨
      ((¬True) ∧ (!false || y == 0))
  then x + 7 else y - 3

def literalFunction (x y : UInt64) : UInt64 :=
  let bias := x + 7
  let f := fun a b : UInt64 =>
    if true && (a == b || !false) then a + bias else if False then b else b - bias
  f x y + f y x

def literalDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  if True then a := a + y else a := a - y
  let z ← if false then pure (a * y) else pure (a ^^^ y)
  if ¬False ∧ (true || x == y) then a := a + z
  return a

def rangeLiteralBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if true then break
    a := a + 99
  return a

def rangeLiteralContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if false then continue
    if True ∧ UInt64.ofNat i % 3 = 1 then continue
    a := a + UInt64.ofNat i
    if False then break
  return a

def rangeLiteralJoined (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      let z ← if !(false || UInt64.ofNat i % 2 == 0) then pure (a + 1) else pure (a + 3)
      a := z
      if ¬False ∧ (true && a % 7 == 0) then break
    return a
  if true then result + seed else result - count

def rangeLiteralStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if (False ∨ x = seed) ∨ (¬¬True ∧ (!(!true) && y % 5 == 0))
      then .done (max x y) else .yield (min (x + UInt64.ofNat i) (y + 3))
    finish (a + 1) (a + seed)

def punitExplicit (x y : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a => a * 3 + x
  f PUnit.unit y

def punitCapture (x y : UInt64) : UInt64 :=
  let bias := x + 7
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a => a + bias
  let bias := y + 11
  f PUnit.unit bias - f PUnit.unit x

def punitChain (x y : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a => a ^^^ x
  let g : Unit → UInt64 → UInt64 := fun _ a => f PUnit.unit (a + y)
  g () x + f () y

def punitUnused (x y : UInt64) : UInt64 :=
  let _f : PUnit.{1} → UInt64 → UInt64 := fun _ a => if a ≤ x then min a y else max a y
  x + y

def punitDo (x y : UInt64) : UInt64 := Id.run do
  let f : PUnit.{1} → UInt64 → Id UInt64 := fun _ a => do
    let mut z := a
    if z < x then z := z + y else z := z - y
    return z ^^^ x
  let z ← f PUnit.unit y
  let result ← f PUnit.unit (z + x)
  return result

def punitNested (x y : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a =>
    let g : PUnit.{1} → UInt64 → UInt64 := fun _ b => (a + b) ^^^ x
    if true && a == y then g PUnit.unit y else g PUnit.unit (a + y)
  f PUnit.unit x + f PUnit.unit y

def rangePUnitJoined (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if !(false || UInt64.ofNat i % 2 == 0) then a := a + 1 else a := a + 3
      if ¬False ∧ (true && a % 7 == 0) then break
    return a
  if true then result + seed else result - count

def rangePUnitStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : PUnit.{1} → UInt64 → Id (ForInStep UInt64) := fun _ x =>
      if x % 5 == seed % 5 then pure (.done (x + 7))
      else pure (.yield (x + UInt64.ofNat i))
    finish PUnit.unit (a + 1)

def rangePUnitScalar (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : PUnit.{1} → UInt64 → UInt64 := fun _ x => x + UInt64.ofNat i + seed
    if UInt64.ofNat i % 3 == 1 then continue
    a := f PUnit.unit a
    if a % 7 == 2 then break
  return a

def rangePUnitYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if UInt64.ofNat i % 2 == 0 then a := a + 3 else a := a + 1
    a := a ^^^ seed
  return a

def rangePUnitOuter (count seed : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ x => x + seed + 1
  let result := Id.run do
    let mut a := f PUnit.unit seed
    for i in [:(f PUnit.unit count % 17).toNat] do
      a := f PUnit.unit (a + UInt64.ofNat i)
      if a % 5 == 0 then break
    return a
  f PUnit.unit result

def rangePUnitStride (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:3] do
    if UInt64.ofNat i % 2 == 0 then a := a + 11 else a := a - 7
    if a % 3 == 0 then continue
    a := a + UInt64.ofNat i
    if a % 5 == 1 then break
  return a

def idReturnedHelper (x y : UInt64) : UInt64 := Id.run do
  let f : PUnit.{1} → UInt64 → Id UInt64 := fun _ a => do
    let mut z := a
    if z < x then z := z + y else z := z - y
    return z ^^^ x
  let z ← f PUnit.unit y
  return f PUnit.unit (z + x)

def idPureNested (x y : UInt64) : UInt64 :=
  @Id.run (Id (Id UInt64))
    (@Pure.pure Id _ (Id (Id UInt64)) (@Pure.pure Id _ (Id UInt64) (pure (x + y))))

def idRunNested (x y : UInt64) : UInt64 :=
  @Id.run (Id UInt64) (@Id.run (Id (Id UInt64)) (pure (pure (pure (x - y)))))

def idBindInput (x y : UInt64) : UInt64 :=
  @Bind.bind Id (@Monad.toBind Id Id.instMonad) (Id UInt64) (Id (Id UInt64))
    (pure (pure (x + y))) (fun value =>
      @Pure.pure Id _ (Id (Id UInt64)) (pure (pure (UInt64.mul value x))))

def idBindOutput (x y : UInt64) : UInt64 := Id.run do
  let f : UInt64 → Id (Id UInt64) := fun a => pure (pure (a + x))
  let z ← pure (x ^^^ y)
  return f (y + z)

def idConditional (x y : UInt64) : UInt64 :=
  @Id.run (Id UInt64) (if x < y then pure (pure (x + 7)) else pure (pure (y - 3)))

def idFunctions (x y : UInt64) : UInt64 :=
  let f : UInt64 → UInt64 → Id (Id UInt64) := fun a b => pure (pure (min (a + x) (b + y)))
  let g : PUnit.{1} → UInt64 → Id (Id UInt64) := fun _ a => f a y
  @Id.run (Id UInt64) (g PUnit.unit (x + y))

def idUnused (x y : UInt64) : UInt64 :=
  let _f : UInt64 → Id (Id UInt64) := fun a => pure (pure (a * x))
  y + 1

def rangeIdWrapped (count seed : UInt64) : UInt64 :=
  @Id.run (Id UInt64) (@Pure.pure Id _ (Id UInt64) (Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i + 1
    return a))

def rangeIdBindLeft (count seed : UInt64) : UInt64 :=
  @Bind.bind Id (@Monad.toBind Id Id.instMonad) UInt64 (Id UInt64)
    (Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + UInt64.ofNat i + 1
        if a % 5 == 0 then break
      return a)
    (fun result => @Pure.pure Id _ (Id UInt64) (pure (result + seed)))

def rangeIdBindRight (count seed : UInt64) : UInt64 :=
  @Bind.bind Id (@Monad.toBind Id Id.instMonad) (Id UInt64) UInt64
    (pure (pure (seed + 1))) (fun initial => Id.run do
      let mut a : UInt64 := initial
      for i in [:count.toNat] do
        a := a + UInt64.ofNat i
      return a)

def rangeIdStepHelper (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : UInt64 → Id (Id UInt64) := fun x => pure (pure (x + UInt64.ofNat i))
    let z : UInt64 := @Id.run (Id UInt64) (f a)
    if z % 3 == 1 then continue
    a := z + 1
    if a % 5 == 0 then break
  return a

def manyOrder (x y : UInt64) : UInt64 :=
  let f := fun a b c : UInt64 => (a - b) / c + a % c
  f x y (x ^^^ y)

def manyFour (x y : UInt64) : UInt64 :=
  let f := fun a b c d : UInt64 => ((a - b) <<< c) ^^^ (d >>> b)
  f x y (y + 1) (x + 7)

def manySix (x y : UInt64) : UInt64 :=
  let f := fun a b c d e g : UInt64 => a + b * 3 - c * 5 + d * 7 - e * 11 + g * 13 + x
  f x y 1 2 (x + y) (x - y)

def manyCapture (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b c : UInt64 =>
    let g := fun d e h : UInt64 => captured + a * d - b * e + c * h
    g y x (a + b)
  let captured := y + 11
  f captured x y

def manyChained (x y : UInt64) : UInt64 :=
  let f := fun a b c : UInt64 => a + b * c
  let g := fun a b c d e : UInt64 => f (a - b) (c + d) e
  g (f x y 3) (f y x 5) x y (x ^^^ y)

def manyDo (x y : UInt64) : UInt64 := Id.run do
  let f : UInt64 → UInt64 → UInt64 → Id UInt64 := fun a b c => do
    let mut z := a + c
    if z < b then z := z + x else z := z - y
    return z ^^^ c
  let z ← f x y (x + 1)
  return f y z (y + 7)

def manyId (x y : UInt64) : UInt64 :=
  let f : UInt64 → UInt64 → UInt64 → UInt64 → Id (Id UInt64) :=
    fun a b c d => pure (pure (if a < b ∧ c != d then min a d else max b c))
  @Id.run (Id UInt64) (f x y (x + y) (x - y))

def manyUnused (x y : UInt64) : UInt64 :=
  let _f := fun a b c d e : UInt64 => (a + x) / (b - y) + c * d - e
  x ^^^ y

def rangeManyStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y z : UInt64 => x + y * 3 - z + UInt64.ofNat i
    let z := f a seed (UInt64.ofNat i)
    if z % 3 == 1 then continue
    a := z + 1
    if a % 7 == 0 then break
  return a

def rangeManyOuter (count seed : UInt64) : UInt64 :=
  let bound := fun a b c : UInt64 => min a b + c
  let f := fun a b c d : UInt64 => a + b * c - d
  Id.run do
    let mut a := f seed count 2 1
    for i in [:(bound count 31 0).toNat] do
      a := f a (UInt64.ofNat i) 3 seed
      if a % 7 == 0 then break
    return f a seed count 11

def rangeManyYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y z : UInt64 => x + y * z
    a := f a (UInt64.ofNat i) (seed + 1)
  return a

def rangeManyStride (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:3] do
    let f := fun x y z u v : UInt64 => x + y * z - u + v + UInt64.ofNat i
    a := f a seed 3 7 11
    if a % 5 == 0 then continue
    a := a + 1
  return a

def rangeManyGuard (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y z : UInt64 => x ^^^ (y + z)
    if f a seed (UInt64.ofNat i) < 7 ∨ (f seed a 1 == 0 ∧ True) then continue
    a := f a (UInt64.ofNat i) 3
    if a % 11 == 0 then break
  return a

def rangeManyResult (count seed : UInt64) : UInt64 :=
  let f : UInt64 → UInt64 → UInt64 → UInt64 → Id UInt64 :=
    fun a b c d => pure (a * b + c - d)
  Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i + 1
      if a % 5 == 0 then break
    return f a seed count 7

def stepManyOrder (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      if (x - y) % 7 == z % 7 then .done (x - y * 3 + z) else .yield (x + y * 5 - z)
    f a seed (UInt64.ofNat i)

def stepManyFour (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z w =>
      if x < y ∨ z == w then .done (x * 3 - y + z * 7 - w) else .yield (x - y * 5 + z + w)
    f a (UInt64.ofNat i) seed count

def stepManySix (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) :=
      fun x y z u v w => do
        let result ← pure (x + y * 3 - z * 5 + u * 7 - v * 11 + w * 13)
        if result % 5 == 0 then return .done result
        return .yield (result + 1)
    f a (UInt64.ofNat i) seed 1 2 count

def stepManyCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let captured := a + UInt64.ofNat i
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      if x % 7 == y % 7 then .done (captured + z) else .yield (captured + x - y + z)
    let captured := seed + 11
    f captured a count

def stepManyChained (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      if x % 5 == 0 then .done (x + y - z) else .yield (x - y + z)
    let g : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) :=
      fun p q r s t => pure (f (p + q) r (s + t))
    g a seed (UInt64.ofNat i) count 1

def stepManyNested (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z w =>
      let g : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun p q r =>
        if p + x < q + y then .done (p + z - w) else .yield (r + x * y - z + w)
      g a seed (UInt64.ofNat i)
    f a seed count (UInt64.ofNat i)

def stepManyBind (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y z =>
      pure (if x % 7 == y % 7 then .done (x + z) else .yield (x - y + z))
    let result ← f a seed (UInt64.ofNat i)
    let alias ← pure result
    return alias

def stepManyScalarMix (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      let g := fun p q r s : UInt64 => p + q * r - s
      let value := g x y z seed
      if value % 11 == 0 then .done value else .yield (value + UInt64.ofNat i)
    f a (UInt64.ofNat i) count

def stepManyUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _f : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z u v =>
      if x < y then .done (a + z - u) else .yield (a + z / u + v)
    .yield (a + UInt64.ofNat i + 1)

def stepManyWrapped (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → UInt64 → Id (Id (ForInStep UInt64)) :=
      fun x y z w => pure (pure (if x % 3 == 0 then .done (x + y - z) else .yield (x - y + z + w)))
    @Id.run (Id (ForInStep UInt64)) (f a seed (UInt64.ofNat i) count)

def dependentCompare (x y : UInt64) : UInt64 :=
  if _h : x < y then x + y * 3 else x - y * 5

def dependentMixed (x y : UInt64) : UInt64 :=
  if _h : ¬ ((x == y || x == 0) ∧ (y ≤ x ∨ y != 0)) then ~~~x else ~~~y

def dependentLiteral (x y : UInt64) : UInt64 :=
  if _h : True ∧ (!false || x == y) then
    if _k : ¬False then x + y else x / y
  else y - x

def dependentNested (x y : UInt64) : UInt64 :=
  if _h : x < y then
    let z := x + y
    if _k : z ≥ y then z + x else z - x
  else if _k : x == y then x * 3 else y - x

def dependentCapture (x y : UInt64) : UInt64 :=
  let captured := x + 7
  if _h : x != y then
    let f := fun a b : UInt64 => if _k : a ≤ b then captured + a else captured - b
    let captured := y + 11
    f captured x
  else captured - y

def dependentDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  if _h : a < y then a := a + y else a := a - y
  let z ← if _k : a % 3 == 0 then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def dependentOperand (x y : UInt64) : UInt64 :=
  if (if _h : x ≤ y then x + 1 else y + 3) == (if _k : y == 0 then x else y)
  then (if _h : x != 0 then x / y else y % x) else ~~~(x + y)

def dependentMany (x y : UInt64) : UInt64 :=
  let f : UInt64 → UInt64 → UInt64 → Id (Id UInt64) := fun a b c =>
    pure (pure (if _h : a < b ∨ b == c then a + b * 3 - c else a - b * 5 + c))
  f x y (x + 7)

def rangeDependentYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if _h : UInt64.ofNat i % 2 = 0 then a := a + 3 else a := a + 7
  return a

def rangeDependentBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if _h : a % 7 == 0 ∨ UInt64.ofNat i ≥ 12 then break
  return a

def rangeDependentContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if _h : UInt64.ofNat i % 3 = 1 then continue
    a := a + UInt64.ofNat i
    if _h : a % 11 == 0 then break
  return a

def rangeDependentJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if _h : a < UInt64.ofNat i then a := a + 2 else a := a + 5
    let z ← if _h : a % 2 == 0 then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if _h : a % 13 == 0 then break
  return if _h : a < seed then a + count else a - count

def rangeDependentStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      if _h : x % 5 == y % 5 then
        let g := fun p q : UInt64 => if _k : p < q then p + z else q - z
        .done (g a seed)
      else .yield (x + y - z)
    f a (UInt64.ofNat i) count

def rangeDependentResult (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let result ← if _h : a % 7 == 0 then pure (ForInStep.done (a + 3))
      else pure (ForInStep.yield (a + UInt64.ofNat i))
    return result

def rangeDependentBounds (count seed : UInt64) : UInt64 := Id.run do
  let first : UInt64 := if _h : seed % 3 == 0 then 0 else 2
  let stop := if _h : count < 3 then count else count - 1
  let mut a := if _h : seed < 5 then seed + 7 else seed
  for i in [first.toNat:stop.toNat:2] do
    if _h : a % 7 == 0 then break
    a := a + UInt64.ofNat i
  return a

def rangeDependentOuter (count seed : UInt64) : UInt64 :=
  let f := fun x y z : UInt64 => if _h : x < y then x + z else y - z
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      if _h : a == 0 then break
    return a
  if _h : result != seed then f result seed count else result

def booleanLet (x y : UInt64) : UInt64 :=
  let equal := x == y
  if equal then x + y * 3 else x - y * 5

def booleanAlias (x y : UInt64) : UInt64 :=
  let equal := x == y
  let alias := equal
  let inverted := !!!alias
  if inverted then ~~~x else ~~~y

def booleanShadow (x y : UInt64) : UInt64 :=
  let flag := x != y
  let f := fun a b : UInt64 => if flag then a + b else a - b
  let flag := y == 0
  if flag then f x y else f y x

def booleanCompound (x y : UInt64) : UInt64 :=
  let equal := x == y
  let zero := x == 0 || y == 0
  let flag := !equal && !(zero || y == 1)
  if flag || (!zero && equal) then x + 13 else y - 17

def booleanNestedOperand (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let a := if flag then x + y else x - y
  let next := (if flag then a else y) == (if _h : x < y then x else a)
  if next && !flag then a + 7 else a - 3

def booleanUnused (x y : UInt64) : UInt64 :=
  let _flag := (x / 0 == y) && (y % 0 != x)
  let kept := true
  let alias := kept
  if alias then x + y else ~~~x

def booleanMany (x y : UInt64) : UInt64 :=
  let outer := x != y
  let f := fun a b c : UInt64 =>
    let inner := a == b || b == c
    if outer && !inner then a + b * 3 - c else a - b * 5 + c
  f x y (x + 7)

def booleanDo (x y : UInt64) : UInt64 := Id.run do
  let flag := x == y
  let mut a := x
  if flag then a := a + y else a := a - y
  let next := a % 3 == 0
  let z ← if next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def rangeBooleanYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := UInt64.ofNat i % 2 == 0
    if even then a := a + 3 else a := a + 7
  return a

def rangeBooleanBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop := a % 7 == 0 || UInt64.ofNat i == 12
    if stop then break
  return a

def rangeBooleanContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := UInt64.ofNat i % 3 == 1
    if skip then continue
    a := a + UInt64.ofNat i
    let stop := a % 11 == 0
    if stop && !skip then break
  return a

def rangeBooleanCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let captured := a % 5 == 0
    let f := fun x y : UInt64 => if captured then x + y else x - y
    a := a + UInt64.ofNat i + 1
    let captured := a % 7 == 0
    a := f a seed
    if captured then break
  return a

def rangeBooleanJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := a % 2 == 0
    if even then a := a + 2 else a := a + 5
    let z ← if !even then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    let stop := a % 13 == 0
    if stop then break
  let changed := a != seed
  return if changed then a + count else a - count

def rangeBooleanOuter (count seed : UInt64) : UInt64 :=
  let flag := seed % 3 == 0
  let f := fun x y z : UInt64 => if flag then x + y - z else x - y + z
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      let stop := a == 0
      if stop && flag then break
    return a
  if flag then result + seed else result - count

def rangeBooleanBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed % 3 == 0
  let first : UInt64 := if flag then 0 else 2
  let stop := if !flag && count != 0 then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish := a % 7 == 0
    if finish && flag then break
    a := a + UInt64.ofNat i
  return a

def rangeBooleanStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let captured := a % 5 == 0
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      let localFlag := x == y || y == z
      if captured && localFlag then .done (x + y - z)
      else .yield (x - y + z)
    f a (UInt64.ofNat i) count

def booleanDependentLet (x y : UInt64) : UInt64 :=
  let equal := x == y
  if _h : equal then x + y * 3 else x - y * 5

def booleanDependentAlias (x y : UInt64) : UInt64 :=
  let equal := x == y
  let alias := equal
  let inverted := !!!alias
  if _h : inverted then ~~~x else ~~~y

def booleanDependentShadow (x y : UInt64) : UInt64 :=
  let flag := x != y
  let f := fun a b : UInt64 => if _h : flag then a + b else a - b
  let flag := y == 0
  if _h : flag then f x y else f y x

def booleanDependentCompound (x y : UInt64) : UInt64 :=
  let equal := x == y
  let zero := x == 0 || y == 0
  let flag := !equal && !(zero || y == 1)
  if _h : flag || (!zero && equal) then x + 13 else y - 17

def booleanDependentNestedOperand (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let a := if _h : flag then x + y else x - y
  let next := (if _h : flag then a else y) == (if _h : x < y then x else a)
  if _h : next && !flag then a + 7 else a - 3

def booleanDependentUnused (x y : UInt64) : UInt64 :=
  let _flag := (x / 0 == y) && (y % 0 != x)
  let kept := true
  let alias := kept
  if _h : alias then x + y else ~~~x

def booleanDependentMany (x y : UInt64) : UInt64 :=
  let five : UInt64 := 5
  let outer := x != y
  let f := fun a b c : UInt64 =>
    let inner := a == b || b == c
    if _h : outer && !inner then a + b * 3 - c else a - b * five + c
  f x y (x + 7)

def booleanDependentDo (x y : UInt64) : UInt64 := Id.run do
  let flag := x == y
  let mut a := x
  if _h : flag then a := a + y else a := a - y
  let next := a % 3 == 0
  let z ← if _h : next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def rangeBooleanDependentYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := UInt64.ofNat i % 2 == 0
    if _h : even then a := a + 3 else a := a + 7
  return a

def rangeBooleanDependentBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop := a % 7 == 0 || UInt64.ofNat i == 12
    if _h : stop then break
  return a

def rangeBooleanDependentContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := UInt64.ofNat i % 3 == 1
    if _h : skip then continue
    a := a + UInt64.ofNat i
    let stop := a % 11 == 0
    if _h : stop && !skip then break
  return a

def rangeBooleanDependentCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let captured := a % 5 == 0
    let f := fun x y : UInt64 => if _h : captured then x + y else x - y
    a := a + UInt64.ofNat i + 1
    let captured := a % 7 == 0
    a := f a seed
    if _h : captured then break
  return a

def rangeBooleanDependentJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := a % 2 == 0
    if _h : even then a := a + 2 else a := a + 5
    let z ← if _h : !even then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    let stop := a % 13 == 0
    if _h : stop then break
  let changed := a != seed
  return if _h : changed then a + count else a - count

def rangeBooleanDependentOuter (count seed : UInt64) : UInt64 :=
  let flag := seed % 3 == 0
  let f := fun x y z : UInt64 => if _h : flag then x + y - z else x - y + z
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      let stop := a == 0
      if _h : stop && flag then break
    return a
  if _h : flag then result + seed else result - count

def rangeBooleanDependentBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed % 3 == 0
  let first : UInt64 := if _h : flag then 0 else 2
  let stop := if _h : !flag && count != 0 then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish := a % 7 == 0
    if _h : finish && flag then break
    a := a + UInt64.ofNat i
  return a

def rangeBooleanDependentStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let captured := a % 5 == 0
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      let localFlag := x == y || y == z
      if _h : captured && localFlag then .done (x + y - z)
      else .yield (x - y + z)
    f a (UInt64.ofNat i) count

def instanceDependentMany (x y : UInt64) : UInt64 :=
  let outer := x != y
  let f := fun a b c : UInt64 =>
    let inner := a == b || b == c
    if _h : outer && !inner then a + b * 3 - c else a - b * 5 + c
  f x y (x + 7)

def instanceLet (x y : UInt64) : UInt64 :=
  x + @OfNat.ofNat UInt64 (nat_lit 7) (let _unused := x + y; @UInt64.instOfNat (nat_lit 7)) - y

def instanceApplied (x y : UInt64) : UInt64 :=
  x * @OfNat.ofNat UInt64 (nat_lit 11) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 11)) (x + y)) - y

def instanceNested (x y : UInt64) : UInt64 :=
  let n := @OfNat.ofNat UInt64 (nat_lit 13)
    ((let _flag := x == y; fun (_ : UInt64) (_ : Unit) => @UInt64.instOfNat (nat_lit 13)) y ())
  n + x * y

def instanceShadow (x y : UInt64) : UInt64 :=
  let n := @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_x : UInt64) => @UInt64.instOfNat (nat_lit 5)) y)
  let f := fun x y z : UInt64 => x + n * y - z
  let n := x + y
  f y n x

def instanceProof (x y : UInt64) : UInt64 :=
  if h : x = y then x + @OfNat.ofNat UInt64 (nat_lit 17) ((fun (_ : x = y) => @UInt64.instOfNat (nat_lit 17)) h)
  else y - @OfNat.ofNat UInt64 (nat_lit 19) ((fun (_ : ¬x = y) => @UInt64.instOfNat (nat_lit 19)) h)

def instanceOverflow (x y : UInt64) : UInt64 :=
  x + @OfNat.ofNat UInt64 (nat_lit 18446744073709551621)
    ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 18446744073709551621)) y)

def instanceDo (x y : UInt64) : UInt64 := Id.run do
  let flag := x == y
  let mut a := x
  if h : flag then
    a := a + @OfNat.ofNat UInt64 (nat_lit 3) ((fun (_ : flag = true) => @UInt64.instOfNat (nat_lit 3)) h)
  else a := a - @OfNat.ofNat UInt64 (nat_lit 5) (let _unused := a; @UInt64.instOfNat (nat_lit 5))
  return a ^^^ y

def rangeInstanceStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if h : a < UInt64.ofNat i then
      a := a + @OfNat.ofNat UInt64 (nat_lit 3) ((fun (_ : a < UInt64.ofNat i) => @UInt64.instOfNat (nat_lit 3)) h)
    else a := a + @OfNat.ofNat UInt64 (nat_lit 5) (let _unused := a; @UInt64.instOfNat (nat_lit 5))
  return a

def rangeInstanceBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let increment := @OfNat.ofNat UInt64 (nat_lit 7) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 7)) a)
    a := a + increment + UInt64.ofNat i
    let stop := a % 11 == 0
    if _h : stop then break
  return a

def rangeInstanceBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := @OfNat.ofNat UInt64 (nat_lit 1) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 1)) count)
  let mut a := seed + @OfNat.ofNat UInt64 (nat_lit 13) (let _unused := count; @UInt64.instOfNat (nat_lit 13))
  for i in [first.toNat:count.toNat:2] do
    a := a + UInt64.ofNat i
    if a % 7 == 0 then continue
    a := a + @OfNat.ofNat UInt64 (nat_lit 3) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 3)) a)
  return a

def rangeInstanceOuter (count seed : UInt64) : UInt64 :=
  let f := fun x y z : UInt64 =>
    x + y * @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 5)) z)
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      if a % 7 == 0 then break
    return a
  f result seed count

def naturalConverted (x y : UInt64) : UInt64 := x + UInt64.ofNat 5 - y

def naturalConvertedOverflow (x y : UInt64) : UInt64 :=
  x + UInt64.ofNat 18446744073709551621 - y

def naturalExplicitLet (x y : UInt64) : UInt64 :=
  x + @OfNat.ofNat UInt64 7 (let _unused := x + y; @UInt64.instOfNat 7) - y

def naturalExplicitApplied (x y : UInt64) : UInt64 :=
  x * @OfNat.ofNat UInt64 11 ((fun (_ : UInt64) => @UInt64.instOfNat 11) (x + y)) - y

def naturalExplicitNested (x y : UInt64) : UInt64 :=
  let n := @OfNat.ofNat UInt64 13
    ((let _flag := x == y; fun (_ : UInt64) (_ : Unit) => @UInt64.instOfNat 13) y ())
  n + x * y

def naturalDependentMany (x y : UInt64) : UInt64 :=
  let outer := x != y
  let f := fun a b c : UInt64 =>
    let inner := a == b || b == c
    if _h : outer && !inner then a + b * 3 - c else a - b * UInt64.ofNat 5 + c
  f x y (x + 7)

def naturalDo (x y : UInt64) : UInt64 := Id.run do
  let flag := x == y
  let mut a := x
  if h : flag then
    a := a + @OfNat.ofNat UInt64 3 ((fun (_ : flag = true) => @UInt64.instOfNat 3) h)
  else a := a - @OfNat.ofNat UInt64 5 (let _unused := a; @UInt64.instOfNat 5)
  return a ^^^ y

def naturalOperand (x y : UInt64) : UInt64 :=
  let flag := UInt64.ofNat 7 == x
  if _h : flag then max (UInt64.ofNat 17) y else min (UInt64.ofNat 5 + y) x

def rangeNaturalStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if h : a < UInt64.ofNat i then
      a := a + @OfNat.ofNat UInt64 3 ((fun (_ : a < UInt64.ofNat i) => @UInt64.instOfNat 3) h)
    else a := a + @OfNat.ofNat UInt64 5 (let _unused := a; @UInt64.instOfNat 5)
  return a

def rangeNaturalBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := @OfNat.ofNat UInt64 1 ((fun (_ : UInt64) => @UInt64.instOfNat 1) count)
  let mut a := seed + @OfNat.ofNat UInt64 13 (let _unused := count; @UInt64.instOfNat 13)
  for i in [first.toNat:count.toNat:2] do
    a := a + UInt64.ofNat i
    if a % 7 == 0 then continue
    a := a + @OfNat.ofNat UInt64 3 ((fun (_ : UInt64) => @UInt64.instOfNat 3) a)
  return a

def rangeNaturalConversion (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat 17 + UInt64.ofNat i
    let stop := a % 11 == 0
    if _h : stop then break
  return a

def rangeNaturalOuter (count seed : UInt64) : UInt64 :=
  let f := fun x y z : UInt64 =>
    x + y * @OfNat.ofNat UInt64 5 ((fun (_ : UInt64) => @UInt64.instOfNat 5) z)
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      if a % 7 == 0 then break
    return a
  f result seed count

def boolBindLet (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x == y)
  return if flag then x + y * 3 else x - y * 5

def boolBindAlias (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x != y)
  let alias ← pure flag
  let inverted ← pure (!!!alias)
  return if inverted then ~~~x else ~~~y

def boolBindWrapped (x y : UInt64) : UInt64 := Id.run do
  let flag ← Id.run (pure (x == y))
  let alias ← pure (Id.run (pure flag))
  return if alias && !(x == 0) then x + 7 else y - 11

def boolBindShadow (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x != y)
  let f := fun a b : UInt64 => if flag then a + b else a - b
  let flag ← pure (y == 0)
  return if flag then f x y else f y x

def boolBindCapture (x y : UInt64) : UInt64 := Id.run do
  let outer ← pure (x == 0)
  let f : UInt64 → UInt64 → UInt64 → Id UInt64 := fun a b c => do
    let inner ← pure (a == b || b == c)
    return if outer || !inner then a + b * 3 - c else a - b + c
  f x y (x + 7)

def boolBindDependent (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x == y)
  if _h : flag then
    let next ← pure (x == 0)
    return if next then y + 3 else x - 5
  else
    let next ← pure (x != 0 && y != 0)
    return if _k : next then x / y else y % x

def boolBindDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x == y)
  let mut a := x
  if flag then a := a + y else a := a - y
  let next ← pure (a % 3 == 0)
  let z ← if next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def boolBindUnused (x y : UInt64) : UInt64 := Id.run do
  let _unused ← pure (true || x / 0 == y)
  let kept ← pure true
  return if kept then x + y else x - y

def rangeBoolBindYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (UInt64.ofNat i % 2 == 0)
    if even then a := a + 3 else a := a + 7
  return a

def rangeBoolBindBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop ← pure (a % 7 == 0 || UInt64.ofNat i == 12)
    if _h : stop then break
  return a

def rangeBoolBindContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip ← pure (UInt64.ofNat i % 3 == 1)
    if skip then continue
    a := a + UInt64.ofNat i
    let stop ← pure (a % 11 == 0)
    if stop && !skip then break
  return a

def rangeBoolBindJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (a % 2 == 0)
    if even then a := a + 2 else a := a + 5
    let next ← Id.run (pure (!even))
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    let stop ← pure (a % 13 == 0)
    if stop then break
  return a

def rangeBoolBindCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (seed % 3 == 0)
  let f := fun x y z : UInt64 => if flag then x + y - z else x - y + z
  let mut a := seed
  for i in [:count.toNat] do
    let inner ← pure (a % 5 == 0)
    a := f a (UInt64.ofNat i) count
    if inner && flag then break
  return a

def rangeBoolBindBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (seed % 3 == 0)
  let first : UInt64 := if flag then 0 else 2
  let stop := if !flag && count != 0 then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish ← pure (a % 7 == 0)
    if finish && flag then break
    a := a + UInt64.ofNat i
  return a

def rangeBoolBindStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let captured ← pure (a % 5 == 0)
    let f : UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y z => do
      let inner ← pure (x == y || y == z)
      if _h : captured && inner then return .done (x + y - z)
      else return .yield (x - y + z)
    f a (UInt64.ofNat i) count

def rangeBoolBindOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (seed == 0)
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop ← pure (a % 7 == 0)
    if stop && flag then break
  let changed ← pure (a != seed)
  return if changed then a + count else a - count

def boolChoiceLet (x y : UInt64) : UInt64 :=
  let flag := if x == y then x == 0 else y != 0
  if flag then x + y * 3 else x - y * 5

def boolChoiceNested (x y : UInt64) : UInt64 :=
  let flag := x == y
  let result := !!!(if (if flag then x == 0 else y == 0) then
    (if !flag then x != 0 else false) else (if flag then true else y != 0))
  if result then ~~~x else ~~~y

def boolChoiceClosed (x y : UInt64) : UInt64 :=
  if (if x == y then x != 0 else y == 0) then x + 7 else y - 11

def boolChoiceShadow (x y : UInt64) : UInt64 :=
  let flag := if x == y then true else x == 0
  let f := fun a b : UInt64 => if (if flag then a != b else b == 0) then a + b else a - b
  let flag := if y == 0 then false else !flag
  if flag then f x y else f y x

def boolChoiceCapture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun a b c : UInt64 =>
    let inner := if outer then a == b || b == c else a != c
    if inner then a + b * 3 - c else a - b + c
  f x y (x + 7)

def boolChoiceDependent (x y : UInt64) : UInt64 :=
  let flag := x == y
  if _h : (if flag then x != 0 else y == 0) then
    let next := if flag then y == 0 else x != 0
    if next then y + 3 else x - 5
  else
    let next := if !flag then x != 0 && y != 0 else true
    if _k : next then x / y else y % x

def boolChoiceDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (if x == y then x == 0 else y != 0)
  let mut a := x
  if flag then a := a + y else a := a - y
  let next := if a % 3 == 0 then !flag else a != 0
  let z ← if next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def boolChoiceUnused (x y : UInt64) : UInt64 :=
  let _unused := if true then false else x / 0 == y
  let kept := if false then false else true
  if kept then x + y else x - y

def rangeBoolChoiceYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := if UInt64.ofNat i % 2 == 0 then a != 0 else a == 0
    if even then a := a + 3 else a := a + 7
  return a

def rangeBoolChoiceBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if _h : (if a % 7 == 0 then true else UInt64.ofNat i == 12) then break
  return a

def rangeBoolChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := if UInt64.ofNat i % 3 == 1 then a != seed else false
    if skip then continue
    a := a + UInt64.ofNat i
    let stop := if !skip then a % 11 == 0 else false
    if stop then break
  return a

def rangeBoolChoiceJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (if a % 2 == 0 then true else false)
    if even then a := a + 2 else a := a + 5
    let next ← pure (if even then a % 3 == 0 else !even)
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if (if next then a % 13 == 0 else false) then break
  return a

def rangeBoolChoiceCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := if seed % 3 == 0 then count != 0 else false
  let f := fun x y z : UInt64 =>
    let inner := if flag then x != y else y == z
    if inner then x + y - z else x - y + z
  let mut a := seed
  for i in [:count.toNat] do
    let inner := if flag then a % 5 == 0 else a == seed
    a := f a (UInt64.ofNat i) count
    if inner && flag then break
  return a

def rangeBoolChoiceBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := if seed % 3 == 0 then true else count == 0
  let first : UInt64 := if flag then 0 else 2
  let stop := if (if flag then false else count != 0) then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish := if flag then a % 7 == 0 else false
    if finish then break
    a := a + UInt64.ofNat i
  return a

def rangeBoolChoiceStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let captured := if a % 5 == 0 then count != 0 else false
    let f : UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y z => do
      let inner := if captured then x == y || y == z else y != z
      if _h : inner then return .done (x + y - z)
      else return .yield (x - y + z)
    f a (UInt64.ofNat i) count

def rangeBoolChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := if seed == 0 then count != 0 else false
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop := if flag then a % 7 == 0 else false
    if stop then break
  let changed ← pure (if flag then a != seed else count == 0)
  return if changed then a + count else a - count

def propChoiceLet (x y : UInt64) : UInt64 :=
  let a := if x = y then true else false
  let b := if x ≠ y then true else false
  let c := if x < y then x != 0 else y == 0
  let d := if x ≤ y then a else b
  let e := if x > y then c else d
  let f := if x ≥ y then e else !c
  if (a || b) && f then x + y * 3 else x - y * 5

def propChoiceNested (x y : UInt64) : UInt64 :=
  let flag := x == y
  let result := !!!(if (if x ≤ y then (if flag then x == 0 else y == 0) else x != 0) then
    (if !flag then x != 0 else false) else (if flag then true else y != 0))
  if result then ~~~x else ~~~y

def propChoiceClosed (x y : UInt64) : UInt64 :=
  if (if x < y ∧ y ≠ 0 then x != 0 else y == 0) then x + 7 else y - 11

def propChoiceShadow (x y : UInt64) : UInt64 :=
  let flag := if x = y then true else x == 0
  let f := fun a b : UInt64 => if (if flag then a != b else b == 0) then a + b else a - b
  let flag := if y ≠ 0 then false else !flag
  if flag then f x y else f y x

def propChoiceCapture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun a b c : UInt64 =>
    let inner := if (a < b ∨ b ≥ c) ∧ ¬ (a = c) then outer || a == b else !outer && a != c
    if inner then a + b * 3 - c else a - b + c
  f x y (x + 7)

def propChoiceDependent (x y : UInt64) : UInt64 :=
  let flag := x == y
  if _h : (if x < y then flag else !flag) then
    let next := if x ≤ y then flag && y == 0 else x != 0
    if next then y + 3 else x - 5
  else
    let next := if ¬ (x = y) ∧ (x != 0) then !flag && y != 0 else true
    if _k : next then x / y else y % x

def propChoiceDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (if x = y then x == 0 else y != 0)
  let mut a := x
  if flag then a := a + y else a := a - y
  let next := if a % 3 ≤ 1 then !flag else a != 0
  let z ← if next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def propChoiceUnused (x y : UInt64) : UInt64 :=
  let _unused := if True ∧ ¬ False then false else x / 0 == y
  let kept := if False ∨ ¬ True then false else true
  if kept then x + y else x - y

def rangePropChoiceYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := if UInt64.ofNat i % 2 = 0 then a != 0 else a == 0
    if even then a := a + 3 else a := a + 7
  return a

def rangePropChoiceBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if _h : (if (a % 7 = 0 ∨ UInt64.ofNat i ≥ 12) ∧ count ≠ 0 then true else false) then break
  return a

def rangePropChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := if UInt64.ofNat i % 3 ≥ 1 then a != seed else false
    if skip then continue
    a := a + UInt64.ofNat i
    let stop := if !skip then a % 11 == 0 else false
    if stop then break
  return a

def rangePropChoiceJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (if a % 2 = 0 then true else false)
    if even then a := a + 2 else a := a + 5
    let next ← pure (if even then a % 3 == 0 else !even)
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if (if next then a % 13 == 0 else false) then break
  return a

def rangePropChoiceCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := if ¬ (seed % 3 = 0) then count != 0 else false
  let f := fun x y z : UInt64 =>
    let inner := if flag then x != y else y == z
    if inner then x + y - z else x - y + z
  let mut a := seed
  for i in [:count.toNat] do
    let inner := if a ≥ seed ∧ (a != 0) then flag && a % 5 == 0 else a == seed
    a := f a (UInt64.ofNat i) count
    if inner && flag then break
  return a

def rangePropChoiceBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := if ¬ (seed % 3 = 0) then true else count == 0
  let first : UInt64 := if flag then 0 else 2
  let stop := if (if flag then false else count != 0) then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish := if flag then a % 7 == 0 else false
    if finish then break
    a := a + UInt64.ofNat i
  return a

def rangePropChoiceStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let captured := if a % 5 ≤ 1 then count != 0 else false
    let f : UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y z => do
      let inner := if x < y ∨ y = z then captured || x == y else !captured && y != z
      if _h : inner then return .done (x + y - z)
      else return .yield (x - y + z)
    f a (UInt64.ofNat i) count

def rangePropChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := if seed ≤ 1 then count != 0 else false
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop := if flag then a % 7 == 0 else false
    if stop then break
  let changed ← pure (if flag then a != seed else count == 0)
  return if changed then a + count else a - count

def boolFnConditional (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x < y then pure (x == 0) else pure (y != 0)
  return if flag then x + y else x - y

def boolFnLocalGuard (x y : UInt64) : UInt64 := Id.run do
  let saved := x == y
  let flag ← if saved then pure (!saved) else pure (x != 0)
  return if flag then x + y else x - y

def boolFnNested (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x == y then Id.run (pure (x != 0)) else
    if x < y then pure (y == 0) else pure (x == 0)
  return if flag then x + y else x - y

def boolFnDirect (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => if flag then x * 3 + y else x - y * 5
  f true + f false + f (x == y) + f (if x < y then x != 0 else y == 0)

def boolFnShadow (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let f := fun flag : Bool =>
    let g := fun other : Bool => if flag && !other then x + y else x - y
    let flag := !flag
    g flag
  let flag := !flag
  f flag + f (x == y)

def boolFnCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let g := fun a b c : UInt64 => if flag || outer then a + b * c else a - b / c
    g x y (x + 1)
  let g := fun a b : UInt64 => f (a != b) + f (a == 0 && b != 0)
  g x y

def boolFnAnnotation (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id UInt64) := fun flag => pure (pure (if flag then x + y else x - y))
  let a : UInt64 ← f (x == 0)
  let flag ← if a < y then pure (a != 0) else pure (y == 0)
  return if flag then a + 7 else a - 11

def boolFnUnused (x y : UInt64) : UInt64 :=
  let _unused := fun flag : Bool => if flag then x / 0 else y % 0
  let f := fun flag : Bool => if _h : flag then x / y else y % x
  f (if x ≤ y then x != 0 else y == 0)

def rangeBoolFnYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← if UInt64.ofNat i % 2 = 0 then pure (a != 0) else pure (a == 0)
    a := if flag then a + 3 else a + 7
  return a

def rangeBoolFnBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let flag ← if a % 7 = 0 then pure true else pure (UInt64.ofNat i == 12)
    if flag then break
  return a

def rangeBoolFnContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip ← if UInt64.ofNat i % 3 = 1 then pure (a != seed) else pure false
    if skip then continue
    a := a + UInt64.ofNat i
    if a % 11 == 0 then break
  return a

def rangeBoolFnJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    if even then a := a + 2 else a := a + 5
    let next ← if even then pure (a % 3 == 0) else pure (!even)
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if next && a % 13 == 0 then break
  return a

def rangeBoolFnCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => if flag || outer then count + 3 else seed - 7
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => if flag then f outer + a else f (!outer) - a
    a := g (UInt64.ofNat i % 2 == 0)
    if a % 11 == 0 then break
  return f (a == 0) + a

def rangeBoolFnBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun flag : Bool => if flag then count else if count == 0 then 0 else count - 1
  let stop := f (seed % 2 == 0)
  let mut a := seed
  for i in [0:stop.toNat:2] do
    let flag ← if a < seed then pure (UInt64.ofNat i == 0) else pure (a % 7 == 0)
    if flag then break
    a := a + UInt64.ofNat i
  return a

def rangeBoolFnStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let g : Bool → ForInStep UInt64 := fun inner =>
        if flag && !inner then .done (a + UInt64.ofNat i) else .yield (a - count)
      return g (if a ≤ seed then outer else !outer)
    f (UInt64.ofNat i % 3 == 0)

def rangeBoolFnOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun flag : Bool => if flag then seed + 1 else seed - 1
  let mut a := f (count != 0)
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if a % 7 == 0 then break
  let changed ← if a = seed then pure (count != 0) else pure (a != 0)
  return if changed then a + count else a - count

def rangeResultFunctionBool (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun _ a =>
    let _bad : Bool → ForInStep UInt64 := fun _ => .done a
    .yield (a + 1)

def decideLet (x y : UInt64) : UInt64 :=
  let flag := decide (x < y)
  if flag then x + y else x - y

def decideImplicit (x y : UInt64) : UInt64 :=
  let flag : Bool := x ≤ y
  if flag then x + y else x - y

def decideCompound (x y : UInt64) : UInt64 :=
  let flag := decide ((x < y ∧ y ≠ 0) ∨ ¬ (x = y))
  if !flag then x + y else x - y

def decideBoolean (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => if flag then x + y else x - y
  f (decide ((x == y) = true))

def decideChoices (x y : UInt64) : UInt64 :=
  let a := decide (x = y)
  let b := decide (x ≠ y)
  let c := decide (x > y)
  let d := decide (x ≥ y)
  let flag := if x ≤ y then (a || b) && !c else d
  if _h : flag then x / y else y % x

def decideCapture (x y : UInt64) : UInt64 :=
  let outer := decide (x = 0)
  let f := fun flag : Bool =>
    let g := fun a b c : UInt64 =>
      let flag := flag && decide (a < b ∨ b ≥ c)
      if flag || outer then a + b * c else a - b + c
    g x y (x + 1)
  let outer := !outer
  f outer + f (decide (x ≤ y))

def decideDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x < y then pure (decide (x > 0)) else pure (decide (y = 0))
  let mut a := x
  if flag then a := a + y else a := a - y
  let next ← Id.run (pure (decide (a ≤ y ∧ ¬ (x = y))))
  return if !!!next then a * 7 else a + 11

def decideUnused (x y : UInt64) : UInt64 :=
  let _unused := decide (False ∧ x / 0 = y)
  let flag := decide (True ∨ ¬ False)
  if flag && !decide (((x == y) && (y != 0)) = true) then x + y else x - y

def rangeDecideYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := decide (UInt64.ofNat i % 2 = 0 ∧ a ≠ 0)
    a := if flag then a + 3 else a + 7
  return a

def rangeDecideBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let flag ← if a % 7 = 0 then pure true else pure (UInt64.ofNat i ≥ 12)
    if flag then break
  return a

def rangeDecideContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := decide (UInt64.ofNat i % 3 = 1 ∨ a = seed)
    if skip then continue
    a := a + UInt64.ofNat i
    if decide (a % 11 = 0) then break
  return a

def rangeDecideJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (decide (a % 2 = 0))
    if even then a := a + 2 else a := a + 5
    let next ← if even then pure (decide (a % 3 = 0)) else pure (!even)
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if next && decide (a % 13 = 0) then break
  return a

def rangeDecideCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := decide (seed ≠ 0)
  let f := fun flag : Bool => if flag || outer then count + 3 else seed - 7
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => if flag then f outer + a else f (!outer) - a
    a := g (decide (UInt64.ofNat i % 2 = 0))
    if decide (a % 11 = 0) then break
  return f (decide (a = 0)) + a

def rangeDecideBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag : Bool := seed % 3 ≤ 1
  let first : UInt64 := if flag then 0 else 2
  let stop := if !flag && decide (count > 0) then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    if decide (a % 7 = 0) then break
    a := a + UInt64.ofNat i
  return a

def rangeDecideStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let g : UInt64 → ForInStep UInt64 := fun x =>
        if flag && decide (x ≤ seed ∨ a = 0) then .done (a + x) else .yield (a - count)
      return g (UInt64.ofNat i)
    f (decide (UInt64.ofNat i % 3 = 0))

def rangeDecideOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (decide (count ≠ 0))
  let mut a := if flag then seed + 1 else seed - 1
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if decide (a % 7 = 0) then break
  let changed ← if a = seed then pure (decide (count ≠ 0)) else pure (decide (a > 0))
  return if changed then a + count else a - count

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
   ("rangeNatMax", rangeNatMax),
   ("rangeStepRun", rangeStepRun),
   ("rangeStepPure", rangeStepPure),
   ("rangeStepLet", rangeStepLet),
   ("rangeStepCapture", rangeStepCapture),
   ("rangeStepBind", rangeStepBind),
   ("rangeStepIdLet", rangeStepIdLet),
   ("rangeStepUnused", rangeStepUnused),
   ("rangeStepWrappedBind", rangeStepWrappedBind),
   ("rangeStepJoined", rangeStepJoined),
   ("rangeResultFunction", rangeResultFunction),
   ("rangeResultChained", rangeResultChained),
   ("rangeResultCapture", rangeResultCapture),
   ("rangeResultUnused", rangeResultUnused),
   ("rangeResultWrapped", rangeResultWrapped),
   ("rangeNegatedBreak", rangeNegatedBreak),
   ("rangeNegatedContinue", rangeNegatedContinue),
   ("rangeNegatedJoin", rangeNegatedJoin),
   ("rangeFromOne", rangeFromOne),
   ("rangeIntervalLiteral", rangeIntervalLiteral),
   ("rangeIntervalEmpty", rangeIntervalEmpty),
   ("rangeIntervalEqual", rangeIntervalEqual),
   ("rangeIntervalBreak", rangeIntervalBreak),
   ("rangeIntervalContinue", rangeIntervalContinue),
   ("rangeIntervalCapture", rangeIntervalCapture),
   ("rangeIntervalJoin", rangeIntervalJoin),
   ("rangeIntervalHigh", rangeIntervalHigh),
   ("rangeIntervalMaxEmpty", rangeIntervalMaxEmpty),
   ("rangeIntervalHugeBreak", rangeIntervalHugeBreak),
   ("rangeDynamicStart", rangeDynamicStart),
   ("rangeDynamicLiteral", rangeDynamicLiteral),
   ("rangeDynamicComputed", rangeDynamicComputed),
   ("rangeDynamicCapture", rangeDynamicCapture),
   ("rangeDynamicHigh", rangeDynamicHigh),
   ("rangeDynamicEmpty", rangeDynamicEmpty),
   ("rangeDynamicEqual", rangeDynamicEqual),
   ("rangeDynamicHugeBreak", rangeDynamicHugeBreak),
   ("rangeDynamicContinue", rangeDynamicContinue),
   ("rangeDynamicJoin", rangeDynamicJoin),
   ("rangeDynamicChoice", rangeDynamicChoice),
   ("rangeStrideTwo", rangeStrideTwo),
   ("rangeStrideLiteral", rangeStrideLiteral),
   ("rangeStrideDynamic", rangeStrideDynamic),
   ("rangeStrideCapture", rangeStrideCapture),
   ("rangeStrideHigh", rangeStrideHigh),
   ("rangeStrideEmpty", rangeStrideEmpty),
   ("rangeStrideHuge", rangeStrideHuge),
   ("rangeStrideHugeTwo", rangeStrideHugeTwo),
   ("rangeStrideHugeBreak", rangeStrideHugeBreak),
   ("rangeStrideContinue", rangeStrideContinue),
   ("rangeStrideJoin", rangeStrideJoin),
   ("rangeStrideOne", rangeStrideOne),
   ("rangeBinaryLocal", rangeBinaryLocal),
   ("rangeBinaryCapture", rangeBinaryCapture),
   ("rangeBinaryNested", rangeBinaryNested),
   ("rangeBinaryDo", rangeBinaryDo),
   ("rangeBinaryContinue", rangeBinaryContinue),
   ("rangeBinaryUnused", rangeBinaryUnused),
   ("rangeBinaryStep", rangeBinaryStep),
   ("rangeBinaryStepOrder", rangeBinaryStepOrder),
   ("rangeBinaryStepCapture", rangeBinaryStepCapture),
   ("rangeBinaryStepChained", rangeBinaryStepChained),
   ("rangeBinaryStepNested", rangeBinaryStepNested),
   ("rangeBinaryStepDo", rangeBinaryStepDo),
   ("rangeBinaryStepScalar", rangeBinaryStepScalar),
   ("rangeBinaryStepUnused", rangeBinaryStepUnused),
   ("rangeBinaryStepResult", rangeBinaryStepResult),
   ("rangeBinaryStepWrapped", rangeBinaryStepWrapped),
   ("rangeBoolNotBreak", rangeBoolNotBreak),
   ("rangeBoolNotContinue", rangeBoolNotContinue),
   ("rangeBoolNotJoin", rangeBoolNotJoin),
   ("rangeBoolNotFunction", rangeBoolNotFunction),
   ("rangeOuterUnary", rangeOuterUnary),
   ("rangeOuterBinary", rangeOuterBinary),
   ("rangeOuterUnit", rangeOuterUnit),
   ("rangeOuterCapture", rangeOuterCapture),
   ("rangeOuterBounds", rangeOuterBounds),
   ("rangeOuterChained", rangeOuterChained),
   ("rangeOuterNested", rangeOuterNested),
   ("rangeOuterDo", rangeOuterDo),
   ("rangeOuterUnused", rangeOuterUnused),
   ("rangeOuterStep", rangeOuterStep),
   ("rangeLetResult", rangeLetResult),
   ("rangeLetDirect", rangeLetDirect),
   ("rangeLetCapture", rangeLetCapture),
   ("rangeLetAliases", rangeLetAliases),
   ("rangeLetUnused", rangeLetUnused),
   ("rangeLetStride", rangeLetStride),
   ("rangeLetContinue", rangeLetContinue),
   ("rangeLetMonadic", rangeLetMonadic),
   ("rangeLetHelper", rangeLetHelper),
   ("rangeLetNested", rangeLetNested),
   ("rangeComplement", rangeComplement),
   ("rangeComplementContinue", rangeComplementContinue),
   ("rangeComplementHelper", rangeComplementHelper),
   ("rangeComplementStep", rangeComplementStep),
   ("rangeCompoundBreak", rangeCompoundBreak),
   ("rangeCompoundContinue", rangeCompoundContinue),
   ("rangeCompoundJoined", rangeCompoundJoined),
   ("rangeCompoundHelper", rangeCompoundHelper),
   ("rangeCompoundStep", rangeCompoundStep),
   ("rangeCompoundResult", rangeCompoundResult),
   ("rangeCompoundNotBreak", rangeCompoundNotBreak),
   ("rangeCompoundNotContinue", rangeCompoundNotContinue),
   ("rangeCompoundNotJoined", rangeCompoundNotJoined),
   ("rangeCompoundNotStep", rangeCompoundNotStep),
   ("rangeBoolCompoundBreak", rangeBoolCompoundBreak),
   ("rangeBoolCompoundContinue", rangeBoolCompoundContinue),
   ("rangeBoolCompoundJoined", rangeBoolCompoundJoined),
   ("rangeBoolCompoundStep", rangeBoolCompoundStep),
   ("rangeMixedGuardBreak", rangeMixedGuardBreak),
   ("rangeMixedGuardContinue", rangeMixedGuardContinue),
   ("rangeMixedGuardJoined", rangeMixedGuardJoined),
   ("rangeMixedGuardStep", rangeMixedGuardStep),
   ("rangeExtremaCount", rangeExtremaCount),
   ("rangeExtremaExit", rangeExtremaExit),
   ("rangeExtremaBounds", rangeExtremaBounds),
   ("rangeExtremaStep", rangeExtremaStep),
   ("rangeLiteralBreak", rangeLiteralBreak),
   ("rangeLiteralContinue", rangeLiteralContinue),
   ("rangeLiteralJoined", rangeLiteralJoined),
   ("rangeLiteralStep", rangeLiteralStep),
   ("rangePUnitJoined", rangePUnitJoined),
   ("rangePUnitStep", rangePUnitStep),
   ("rangePUnitScalar", rangePUnitScalar),
   ("rangePUnitYield", rangePUnitYield),
   ("rangePUnitOuter", rangePUnitOuter),
   ("rangePUnitStride", rangePUnitStride),
   ("rangeIdWrapped", rangeIdWrapped),
   ("rangeIdBindLeft", rangeIdBindLeft),
   ("rangeIdBindRight", rangeIdBindRight),
   ("rangeIdStepHelper", rangeIdStepHelper),
   ("rangeManyStep", rangeManyStep),
   ("rangeManyOuter", rangeManyOuter),
   ("rangeManyYield", rangeManyYield),
   ("rangeManyStride", rangeManyStride),
   ("rangeManyGuard", rangeManyGuard),
   ("rangeManyResult", rangeManyResult),
   ("stepManyOrder", stepManyOrder),
   ("stepManyFour", stepManyFour),
   ("stepManySix", stepManySix),
   ("stepManyCapture", stepManyCapture),
   ("stepManyChained", stepManyChained),
   ("stepManyNested", stepManyNested),
   ("stepManyBind", stepManyBind),
   ("stepManyScalarMix", stepManyScalarMix),
   ("stepManyUnused", stepManyUnused),
   ("stepManyWrapped", stepManyWrapped),
   ("rangeDependentYield", rangeDependentYield),
   ("rangeDependentBreak", rangeDependentBreak),
   ("rangeDependentContinue", rangeDependentContinue),
   ("rangeDependentJoined", rangeDependentJoined),
   ("rangeDependentStep", rangeDependentStep),
   ("rangeDependentResult", rangeDependentResult),
   ("rangeDependentBounds", rangeDependentBounds),
   ("rangeDependentOuter", rangeDependentOuter),
   ("rangeBooleanYield", rangeBooleanYield),
   ("rangeBooleanBreak", rangeBooleanBreak),
   ("rangeBooleanContinue", rangeBooleanContinue),
   ("rangeBooleanCapture", rangeBooleanCapture),
   ("rangeBooleanJoined", rangeBooleanJoined),
   ("rangeBooleanOuter", rangeBooleanOuter),
   ("rangeBooleanBounds", rangeBooleanBounds),
   ("rangeBooleanStep", rangeBooleanStep),
   ("rangeBooleanDependentYield", rangeBooleanDependentYield),
   ("rangeBooleanDependentBreak", rangeBooleanDependentBreak),
   ("rangeBooleanDependentContinue", rangeBooleanDependentContinue),
   ("rangeBooleanDependentCapture", rangeBooleanDependentCapture),
   ("rangeBooleanDependentJoined", rangeBooleanDependentJoined),
   ("rangeBooleanDependentOuter", rangeBooleanDependentOuter),
   ("rangeBooleanDependentBounds", rangeBooleanDependentBounds),
   ("rangeBooleanDependentStep", rangeBooleanDependentStep),
   ("rangeInstanceStep", rangeInstanceStep),
   ("rangeInstanceBreak", rangeInstanceBreak),
   ("rangeInstanceBounds", rangeInstanceBounds),
   ("rangeInstanceOuter", rangeInstanceOuter),
   ("rangeNaturalStep", rangeNaturalStep),
   ("rangeNaturalBounds", rangeNaturalBounds),
   ("rangeNaturalConversion", rangeNaturalConversion),
   ("rangeNaturalOuter", rangeNaturalOuter),
   ("rangeBoolBindYield", rangeBoolBindYield),
   ("rangeBoolBindBreak", rangeBoolBindBreak),
   ("rangeBoolBindContinue", rangeBoolBindContinue),
   ("rangeBoolBindJoined", rangeBoolBindJoined),
   ("rangeBoolBindCapture", rangeBoolBindCapture),
   ("rangeBoolBindBounds", rangeBoolBindBounds),
   ("rangeBoolBindStep", rangeBoolBindStep),
   ("rangeBoolBindOuter", rangeBoolBindOuter),
   ("rangeBoolChoiceYield", rangeBoolChoiceYield),
   ("rangeBoolChoiceBreak", rangeBoolChoiceBreak),
   ("rangeBoolChoiceContinue", rangeBoolChoiceContinue),
   ("rangeBoolChoiceJoined", rangeBoolChoiceJoined),
   ("rangeBoolChoiceCapture", rangeBoolChoiceCapture),
   ("rangeBoolChoiceBounds", rangeBoolChoiceBounds),
   ("rangeBoolChoiceStep", rangeBoolChoiceStep),
   ("rangeBoolChoiceOuter", rangeBoolChoiceOuter),
   ("rangePropChoiceYield", rangePropChoiceYield),
   ("rangePropChoiceBreak", rangePropChoiceBreak),
   ("rangePropChoiceContinue", rangePropChoiceContinue),
   ("rangePropChoiceJoined", rangePropChoiceJoined),
   ("rangePropChoiceCapture", rangePropChoiceCapture),
   ("rangePropChoiceBounds", rangePropChoiceBounds),
   ("rangePropChoiceStep", rangePropChoiceStep),
   ("rangePropChoiceOuter", rangePropChoiceOuter),
   ("rangeBoolFnYield", rangeBoolFnYield),
   ("rangeBoolFnBreak", rangeBoolFnBreak),
   ("rangeBoolFnContinue", rangeBoolFnContinue),
   ("rangeBoolFnJoined", rangeBoolFnJoined),
   ("rangeBoolFnCapture", rangeBoolFnCapture),
   ("rangeBoolFnBounds", rangeBoolFnBounds),
   ("rangeBoolFnStep", rangeBoolFnStep),
   ("rangeBoolFnOuter", rangeBoolFnOuter),
   ("rangeResultFunctionBool", rangeResultFunctionBool),
   ("rangeDecideYield", rangeDecideYield),
   ("rangeDecideBreak", rangeDecideBreak),
   ("rangeDecideContinue", rangeDecideContinue),
   ("rangeDecideJoined", rangeDecideJoined),
   ("rangeDecideCapture", rangeDecideCapture),
   ("rangeDecideBounds", rangeDecideBounds),
   ("rangeDecideStep", rangeDecideStep),
   ("rangeDecideOuter", rangeDecideOuter)]

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
   ("unusedFunction", unusedFunction), ("doJoined", doJoined), ("doBranchUpdates", doBranchUpdates),
   ("compareNe", compareNe),
   ("negatedEq", negatedEq),
   ("negatedLt", negatedLt),
   ("negatedLe", negatedLe),
   ("negatedGt", negatedGt),
   ("negatedGe", negatedGe),
   ("negatedBool", negatedBool),
   ("doubleNegation", doubleNegation),
   ("negatedBindings", negatedBindings),
   ("binaryOrder", binaryOrder),
   ("binaryCapture", binaryCapture),
   ("binaryChained", binaryChained),
   ("binaryUnused", binaryUnused),
   ("binaryDo", binaryDo),
   ("binaryNested", binaryNested),
   ("binaryChoice", binaryChoice),
   ("binaryArguments", binaryArguments),
   ("binaryWrapped", binaryWrapped),
   ("boolNotEqual", boolNotEqual),
   ("boolNotUnequal", boolNotUnequal),
   ("boolNotTwice", boolNotTwice),
   ("boolNotThrice", boolNotThrice),
   ("boolNotNested", boolNotNested),
   ("boolNotFunction", boolNotFunction),
   ("boolNotDo", boolNotDo),
   ("boolNotProposition", boolNotProposition),
   ("complementDirect", complementDirect),
   ("complementOperator", complementOperator),
   ("complementTwice", complementTwice),
   ("complementMixed", complementMixed),
   ("complementChoice", complementChoice),
   ("complementFunction", complementFunction),
   ("complementDo", complementDo),
   ("complementOperand", complementOperand),
   ("compoundAnd", compoundAnd),
   ("compoundOr", compoundOr),
   ("compoundNested", compoundNested),
   ("compoundNegatedLeaves", compoundNegatedLeaves),
   ("compoundZeroDivisor", compoundZeroDivisor),
   ("compoundFunction", compoundFunction),
   ("compoundDo", compoundDo),
   ("compoundOperand", compoundOperand),
   ("compoundNotAnd", compoundNotAnd),
   ("compoundNotOr", compoundNotOr),
   ("compoundNotTwice", compoundNotTwice),
   ("compoundNotThrice", compoundNotThrice),
   ("compoundNotNested", compoundNotNested),
   ("compoundNotFunction", compoundNotFunction),
   ("compoundNotDo", compoundNotDo),
   ("compoundNotOperand", compoundNotOperand),
   ("boolAndTruth", boolAndTruth),
   ("boolOrTruth", boolOrTruth),
   ("boolCompoundNot", boolCompoundNot),
   ("boolCompoundTwice", boolCompoundTwice),
   ("boolCompoundNested", boolCompoundNested),
   ("boolCompoundFunction", boolCompoundFunction),
   ("boolCompoundDo", boolCompoundDo),
   ("boolCompoundOperand", boolCompoundOperand),
   ("mixedGuardAnd", mixedGuardAnd),
   ("mixedGuardOr", mixedGuardOr),
   ("mixedGuardNot", mixedGuardNot),
   ("mixedGuardNegations", mixedGuardNegations),
   ("mixedGuardNested", mixedGuardNested),
   ("mixedGuardFunction", mixedGuardFunction),
   ("mixedGuardDo", mixedGuardDo),
   ("mixedGuardOperand", mixedGuardOperand),
   ("minimumOrder", minimumOrder),
   ("maximumOrder", maximumOrder),
   ("extremaNested", extremaNested),
   ("extremaClamped", extremaClamped),
   ("extremaFunction", extremaFunction),
   ("extremaDo", extremaDo),
   ("extremaGuard", extremaGuard),
   ("extremaWrapped", extremaWrapped),
   ("literalBoolTrue", literalBoolTrue),
   ("literalBoolFalse", literalBoolFalse),
   ("literalPropTrue", literalPropTrue),
   ("literalPropFalse", literalPropFalse),
   ("literalNegations", literalNegations),
   ("literalCompound", literalCompound),
   ("literalFunction", literalFunction),
   ("literalDo", literalDo),
   ("punitExplicit", punitExplicit),
   ("punitCapture", punitCapture),
   ("punitChain", punitChain),
   ("punitUnused", punitUnused),
   ("punitDo", punitDo),
   ("punitNested", punitNested),
   ("idReturnedHelper", idReturnedHelper),
   ("idPureNested", idPureNested),
   ("idRunNested", idRunNested),
   ("idBindInput", idBindInput),
   ("idBindOutput", idBindOutput),
   ("idConditional", idConditional),
   ("idFunctions", idFunctions),
   ("idUnused", idUnused),
   ("manyOrder", manyOrder),
   ("manyFour", manyFour),
   ("manySix", manySix),
   ("manyCapture", manyCapture),
   ("manyChained", manyChained),
   ("manyDo", manyDo),
   ("manyId", manyId),
   ("manyUnused", manyUnused),
   ("dependentCompare", dependentCompare),
   ("dependentMixed", dependentMixed),
   ("dependentLiteral", dependentLiteral),
   ("dependentNested", dependentNested),
   ("dependentCapture", dependentCapture),
   ("dependentDo", dependentDo),
   ("dependentOperand", dependentOperand),
   ("dependentMany", dependentMany),
   ("booleanLet", booleanLet),
   ("booleanAlias", booleanAlias),
   ("booleanShadow", booleanShadow),
   ("booleanCompound", booleanCompound),
   ("booleanNestedOperand", booleanNestedOperand),
   ("booleanUnused", booleanUnused),
   ("booleanMany", booleanMany),
   ("booleanDo", booleanDo),
   ("booleanDependentLet", booleanDependentLet),
   ("booleanDependentAlias", booleanDependentAlias),
   ("booleanDependentShadow", booleanDependentShadow),
   ("booleanDependentCompound", booleanDependentCompound),
   ("booleanDependentNestedOperand", booleanDependentNestedOperand),
   ("booleanDependentUnused", booleanDependentUnused),
   ("booleanDependentMany", booleanDependentMany),
   ("booleanDependentDo", booleanDependentDo),
   ("instanceDependentMany", instanceDependentMany),
   ("instanceLet", instanceLet),
   ("instanceApplied", instanceApplied),
   ("instanceNested", instanceNested),
   ("instanceShadow", instanceShadow),
   ("instanceProof", instanceProof),
   ("instanceOverflow", instanceOverflow),
   ("instanceDo", instanceDo),
   ("naturalConverted", naturalConverted),
   ("naturalConvertedOverflow", naturalConvertedOverflow),
   ("naturalExplicitLet", naturalExplicitLet),
   ("naturalExplicitApplied", naturalExplicitApplied),
   ("naturalExplicitNested", naturalExplicitNested),
   ("naturalDependentMany", naturalDependentMany),
   ("naturalDo", naturalDo),
   ("naturalOperand", naturalOperand),
   ("boolBindLet", boolBindLet),
   ("boolBindAlias", boolBindAlias),
   ("boolBindWrapped", boolBindWrapped),
   ("boolBindShadow", boolBindShadow),
   ("boolBindCapture", boolBindCapture),
   ("boolBindDependent", boolBindDependent),
   ("boolBindDo", boolBindDo),
   ("boolBindUnused", boolBindUnused),
   ("boolChoiceLet", boolChoiceLet),
   ("boolChoiceNested", boolChoiceNested),
   ("boolChoiceClosed", boolChoiceClosed),
   ("boolChoiceShadow", boolChoiceShadow),
   ("boolChoiceCapture", boolChoiceCapture),
   ("boolChoiceDependent", boolChoiceDependent),
   ("boolChoiceDo", boolChoiceDo),
   ("boolChoiceUnused", boolChoiceUnused),
   ("propChoiceLet", propChoiceLet),
   ("propChoiceNested", propChoiceNested),
   ("propChoiceClosed", propChoiceClosed),
   ("propChoiceShadow", propChoiceShadow),
   ("propChoiceCapture", propChoiceCapture),
   ("propChoiceDependent", propChoiceDependent),
   ("propChoiceDo", propChoiceDo),
   ("propChoiceUnused", propChoiceUnused),
   ("boolFnConditional", boolFnConditional),
   ("boolFnLocalGuard", boolFnLocalGuard),
   ("boolFnNested", boolFnNested),
   ("boolFnDirect", boolFnDirect),
   ("boolFnShadow", boolFnShadow),
   ("boolFnCapture", boolFnCapture),
   ("boolFnAnnotation", boolFnAnnotation),
   ("boolFnUnused", boolFnUnused),
   ("decideLet", decideLet),
   ("decideImplicit", decideImplicit),
   ("decideCompound", decideCompound),
   ("decideBoolean", decideBoolean),
   ("decideChoices", decideChoices),
   ("decideCapture", decideCapture),
   ("decideDo", decideDo),
   ("decideUnused", decideUnused)]

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
