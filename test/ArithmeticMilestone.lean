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

def boolWordDirect (x y : UInt64) : UInt64 := (x == y).toUInt64 + Bool.toUInt64 (decide (x < y))

def boolWordCaptured (x y : UInt64) : UInt64 :=
  let flag := x != 0
  let f := fun flag : Bool => flag.toUInt64 + x
  f (!flag) + flag.toUInt64 * y

def boolWordAction (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x = y then pure true else pure (decide (x > 0))
  return flag.toUInt64 + x

def boolWordLiterals (x y : UInt64) : UInt64 :=
  true.toUInt64 * x + false.toUInt64 * y + (!false).toUInt64

def boolWordChoice (x y : UInt64) : UInt64 :=
  let flag := x == y
  let value := (if flag then decide (x ≥ y) else x == 0).toUInt64
  value * 7 + (!!!(flag && decide (x < y))).toUInt64

def boolWordNested (x y : UInt64) : UInt64 :=
  let a := ((x == y).toUInt64 == (decide (x < y)).toUInt64).toUInt64
  let b := (decide (a < (x != 0).toUInt64 + y)).toUInt64
  a * 7 + b * 13

def boolWordDependent (x y : UInt64) : UInt64 :=
  let flag := x != 0
  if _h : flag then
    let f := fun other : Bool => (flag && other).toUInt64 + x
    f (decide (x ≤ y))
  else
    (if y < x then !flag else y != 0).toUInt64 + y

def boolWordUnused (x y : UInt64) : UInt64 :=
  let _unused := (false && (x / 0 == y)).toUInt64
  let f := fun a b c : UInt64 => (decide (a < b ∨ b ≥ c)).toUInt64
  f x y (x + 1) + (x == 0).toUInt64

def rangeBoolWordYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (decide (UInt64.ofNat i % 2 = 0)).toUInt64
    if a % 7 == 0 then break
  return a

def rangeBoolWordBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := decide (a < seed ∨ UInt64.ofNat i ≥ 12)
    a := a + flag.toUInt64 + 1
    if flag.toUInt64 == 1 then break
  return a

def rangeBoolWordContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := UInt64.ofNat i % 3 == 1
    if skip.toUInt64 != 0 then continue
    a := a + skip.toUInt64 + UInt64.ofNat i
    if a % 11 == 0 then break
  return a

def rangeBoolWordJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    if even then a := a + even.toUInt64 else a := a + (!even).toUInt64
    let next ← if even then pure (a % 3 == 0) else pure (!even)
    a := a + next.toUInt64 + UInt64.ofNat i
    if next && a % 13 == 0 then break
  return a

def rangeBoolWordCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (flag || outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f flag + a + outer.toUInt64
    a := g (UInt64.ofNat i % 2 == 0)
    if a % 11 == 0 then break
  return a + f (a == 0)

def rangeBoolWordBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := flag.toUInt64
  let stop := count + (!flag).toUInt64
  let mut a := seed + flag.toUInt64
  for i in [first.toNat:stop.toNat:2] do
    a := a + Bool.toUInt64 (UInt64.ofNat i < count)
    if a % 7 == 0 then break
  return a

def rangeBoolWordStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let value := flag.toUInt64 + a
      if flag then return .done value else return .yield (value + count)
    f (decide (UInt64.ofNat i ≥ 7))

def rangeBoolWordOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + flag.toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if a % 7 == 0 then break
  let changed ← if a = seed then pure (count != 0) else pure (a != 0)
  return a + (changed && flag).toUInt64

def boolEqDirect (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  (a == b).toUInt64 + (a != b).toUInt64 * 3

def boolEqCalls (x y : UInt64) : UInt64 :=
  let a := x == y
  let b := decide (x < y)
  (BEq.beq a b).toUInt64 + (bne a b).toUInt64

def boolEqConditional (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y != 0
  if a == b then x + y else x - y

def boolEqCapture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun flag : Bool => if flag != outer then x + y else x - y
  f (y == 0)

def boolEqLiterals (x y : UInt64) : UInt64 :=
  (true == true).toUInt64 + (false == false).toUInt64 * 3 +
    (true == false).toUInt64 * x + (false != true).toUInt64 * y

def boolEqChoices (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let flag := (if x < y then a else !b) == (if a then decide (x ≤ y) else b)
  if _h : !!!(flag != a) then x / y else y % x

def boolEqNested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let left := (a == b) != (!a == !b)
  let right := (a != !b) == (a == b)
  (left == right).toUInt64 + ((a && b) != (a || b)).toUInt64 * 7

def boolEqDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let same ← if a then pure (a == b) else pure (a != b)
  let mut z := x
  if same then z := z + y else z := z - y
  return z + (same == a).toUInt64

def rangeBoolEqYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    a := a + (first == second).toUInt64
    if first != second then break
  return a

def rangeBoolEqBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let flag := (a % 7 == 0) == (UInt64.ofNat i < 12 : Bool)
    if flag then break
  return a

def rangeBoolEqContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := (UInt64.ofNat i % 3 == 1) != (a == seed)
    if skip then continue
    a := a + UInt64.ofNat i
    if (a % 11 == 0) == true then break
  return a

def rangeBoolEqJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    if even == (UInt64.ofNat i % 2 == 0) then a := a + 2 else a := a + 5
    let next ← if even then pure (even == (a % 3 == 0)) else pure (!even)
    a := a + next.toUInt64 + UInt64.ofNat i
    if next != (a % 13 != 0) then break
  return a

def rangeBoolEqCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (flag == outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (flag != outer) + a
    a := g (UInt64.ofNat i % 2 == 0)
    if (a % 11 == 0) != outer then break
  return a + f (a == 0)

def rangeBoolEqBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := (flag == (count != 0)).toUInt64
  let stop := count + (flag != true).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    a := a + (even == flag).toUInt64
    if (a % 7 == 0) == flag then break
  return a

def rangeBoolEqStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let equal := flag == outer
      if _h : equal != false then return .done (a + UInt64.ofNat i)
      else return .yield (a - count)
    f (decide (UInt64.ofNat i ≥ 7))

def rangeBoolEqOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + flag.toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (a % 7 == 0) != flag then break
  let changed ← if a = seed then pure (flag == (count != 0)) else pure (flag != (a == 0))
  return a + (changed == flag).toUInt64

def boolPropEqual (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  if a = b then x + y else x - y

def boolPropUnequal (x y : UInt64) : UInt64 :=
  let a := x == y
  let b := decide (x < y)
  if a ≠ b then x + 7 else y - 11

def boolPropLiterals (x y : UInt64) : UInt64 :=
  let flag := x != 0
  if flag = false then x + y else if true ≠ flag then x - y else y

def boolPropDependent (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun flag : Bool =>
    if _h : flag = outer then
      let g := fun other : Bool => if other ≠ flag then x + y else x - y
      g (y == 0)
    else (flag != outer).toUInt64 + x
  f (y != 0)

def boolPropTruth (x y : UInt64) : UInt64 :=
  let flag := x == 0
  if flag = true then
    if false = false then x / y else x % y
  else if _h : false ≠ true then y / x else y % x

def boolPropChoices (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  if (if a then b else !b) = (if x < y then a else !a) then
    if _h : (a && b) ≠ (a || b) then x + y else x - y
  else if _h : (!(a == b)) = (!!(a != b)) then x / y else y % x

def boolPropDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let mut z := x
  if a = b then z := z + y else z := z - y
  if _h : a ≠ !b then z := z + 3 else z := z - 7
  return z + a.toUInt64

def boolPropEarly (x y : UInt64) : UInt64 := Id.run do
  let flag := decide (x < y)
  let other := y != 0
  if _h : flag = other then return x + y
  if flag ≠ false then return x - y
  return (if true = !other then y / x else x / y)

def rangeBoolPropYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    if first = second then a := a + 3 else a := a + 7
    if _h : first ≠ second then break
  return a

def rangeBoolPropBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let first := a % 7 == 0
    let second := decide (UInt64.ofNat i < 12)
    if first = second then break
  return a

def rangeBoolPropContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := UInt64.ofNat i % 3 == 1
    let second := a == seed
    if _h : first ≠ second then continue
    a := a + UInt64.ofNat i
    if first = false then break
  return a

def rangeBoolPropJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    let other ← pure (UInt64.ofNat i % 2 == 0)
    if even = other then a := a + 2 else a := a + 5
    if _h : (!even) ≠ other then a := a + UInt64.ofNat i else a := a - count
    if even = (a % 13 == 0) then break
  return a

def rangeBoolPropCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => if flag = outer then count else seed
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => if _h : flag ≠ outer then f (!flag) + a else a + 1
    a := g (UInt64.ofNat i % 2 == 0)
    if (a % 11 == 0) ≠ outer then break
  return a + f (a == 0)

def rangeBoolPropBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first : UInt64 := if flag = false then 0 else 1
  let stop := count + (if flag ≠ true then 1 else 0)
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    if even = flag then a := a + 1 else a := a + 3
    if (a % 7 == 0) ≠ flag then break
  return a

def rangeBoolPropStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      if _h : flag = outer then return .done (a + UInt64.ofNat i)
      else if flag ≠ false then return .yield (a - count)
      else return .yield (a + count)
    f (decide (UInt64.ofNat i ≥ 7))

def rangeBoolPropOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + (if flag = false then 3 else 1)
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (a % 7 == 0) ≠ flag then break
  return if _h : (a == seed) = flag then a + count else a - count

def localDecideEqual (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  (decide (a = b)).toUInt64 + (decide (a ≠ b)).toUInt64 * 3

def localDecideTruth (x y : UInt64) : UInt64 :=
  let flag := x != y
  (decide flag).toUInt64 + (decide (flag = true)).toUInt64 * 7

def localDecideImplicit (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y == 0
  let same : Bool := a = b
  let different : Bool := a ≠ b
  (same && different).toUInt64 + (same || different).toUInt64

def localDecideNested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let first := decide ((decide (a = b)) ≠ (decide (a = false)))
  if _h : !first then x + y else x - y

def localDecideLiterals (x y : UInt64) : UInt64 :=
  (decide (true = true)).toUInt64 * x + (decide (false ≠ false)).toUInt64 * y +
    (decide (false = false)).toUInt64 * 3 + (decide (true ≠ false)).toUInt64 * 7 +
    (decide ((x == y) = true)).toUInt64

def localDecideCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let g := fun other : Bool => (decide (flag = other)).toUInt64 + (decide (other ≠ outer)).toUInt64
    g (decide (flag ≠ outer)) + x
  f (y == 0)

def localDecideDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let same ← if a then pure (decide (a = b)) else pure (decide (a ≠ b))
  let mut z := x
  if same then z := z + y else z := z - y
  return z + (decide same).toUInt64

def localDecideChoices (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  if (if a then b else !b) = (if x < y then a else !a) then
    if _h : (a && b) ≠ (a || b) then x + y else x - y
  else if _h : !(a == b) = !!(a != b) then x / y else y % x

def rangeLocalDecideYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := a % 2 == 0
    let other := UInt64.ofNat i % 3 == 0
    let same ← pure (decide (even = other))
    a := a + same.toUInt64
    if !even ≠ other then break
  return a

def rangeLocalDecideJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    let other ← pure (UInt64.ofNat i % 2 == 0)
    if even = other then a := a + 2 else a := a + 5
    if _h : !even ≠ other then a := a + UInt64.ofNat i else a := a - count
    if even = (a % 13 == 0) then break
  return a

def rangeLocalDecideContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := UInt64.ofNat i % 3 == 1
    let second := a == seed
    let skip : Bool := first ≠ second
    if _h : skip then continue
    a := a + UInt64.ofNat i
    if decide (first = false) then break
  return a

def rangeLocalDecideCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (decide (flag = outer)).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (decide (flag ≠ outer)) + a
    a := g (UInt64.ofNat i % 2 == 0)
    if decide ((a % 11 == 0) ≠ outer) then break
  return a + f (decide (a == 0))

def rangeLocalDecideBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := (decide (flag = false)).toUInt64
  let stop := count + (decide (flag ≠ true)).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    a := a + (decide (even = flag)).toUInt64
    if decide ((a % 7 == 0) ≠ flag) then break
  return a

def rangeLocalDecideStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let same ← pure (decide (flag = outer))
      if _h : same then return .done (a + UInt64.ofNat i)
      else return .yield (a + (decide (flag ≠ false)).toUInt64)
    f (decide ((UInt64.ofNat i ≥ 7 : Bool) = outer))

def rangeLocalDecideOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + (decide (flag = false)).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if decide ((a % 7 == 0) ≠ flag) then break
  let changed ← if a = seed then pure (decide ((a == 0) = flag)) else pure (decide (flag ≠ false))
  return a + (decide (changed = flag)).toUInt64

def rangeLocalDecideUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := decide ((a == seed) = (UInt64.ofNat i == 0))
    let flag := decide ((a == 0) ≠ false)
    a := a + flag.toUInt64
    if _h : flag then break
  return a

def relationChoiceEqual (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let flag := if a = b then a else !b
  flag.toUInt64 + x

def relationChoiceUnequal (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y != 0
  (if a ≠ b then a == b else decide (a = b)).toUInt64 + y

def relationChoiceNested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let left := if a = false then !b else if b ≠ true then a else !a
  let right := if (if a then b else !b) = (if x < y then a else !a) then left else !left
  (if left ≠ right then !a else b).toUInt64

def relationChoiceCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let value := if flag = outer then decide (flag ≠ false) else !flag
    let g := fun other : Bool => (if other ≠ flag then value else !value).toUInt64 + x
    g (y == 0)
  f (y != 0)

def relationChoiceLiterals (x y : UInt64) : UInt64 :=
  (if true = false then true else false).toUInt64 * x +
  (if false = false then true else false).toUInt64 * y +
  (if true ≠ false then false else true).toUInt64 +
  (if false ≠ true then true else false).toUInt64 * 7

def relationChoiceDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let flag ← pure (if a = b then decide (a ≠ false) else !b)
  let mut z := x
  if _h : flag then z := z + y else z := z - y
  return z + (if flag ≠ a then b else !b).toUInt64

def relationChoiceTruth (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  let first := if a then b else !b
  let second := if a = true then b else !b
  (first == second).toUInt64 + (if first = false then x == y else x != y).toUInt64

def relationChoiceUnused (x y : UInt64) : UInt64 :=
  let _unused := if (x == 0) ≠ (y == 0) then decide (x < y) else decide (x > y)
  x + y

def rangeRelationChoiceYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    let same ← if first = second then pure first else pure (!second)
    a := a + (if same ≠ first then same else second).toUInt64
    if same then break
  return a

def rangeRelationChoiceJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    let other ← pure (UInt64.ofNat i % 2 == 0)
    let next ← if even then pure (if even = other then other else !other) else pure (if even ≠ other then even else !even)
    if next then a := a + 2 else a := a + 5
    if (if next = even then a % 7 == 0 else a % 11 == 0) then break
  return a

def rangeRelationChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := UInt64.ofNat i % 3 == 1
    let second := a == seed
    let skip := if first ≠ second then first else !second
    if _h : skip then continue
    a := a + UInt64.ofNat i
    if (if first = false then second else !second) then break
  return a

def rangeRelationChoiceCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (if flag = outer then flag else !flag).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (if flag ≠ outer then outer else !outer) + a
    a := g (UInt64.ofNat i % 2 == 0)
    if (if (a % 11 == 0) ≠ outer then outer else !outer) then break
  return a + f (a == 0)

def rangeRelationChoiceBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := (if flag = false then flag else !flag).toUInt64
  let stop := count + (if flag ≠ true then !flag else flag).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    a := a + (if even = flag then flag else !even).toUInt64
    if (if (a % 7 == 0) ≠ flag then even else flag) then break
  return a

def rangeRelationChoiceStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (if flag = outer then !flag else outer)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (if flag ≠ false then flag else !outer).toUInt64)
    f (if (UInt64.ofNat i ≥ 7 : Bool) = outer then outer else !outer)

def rangeRelationChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + (if flag = false then true else false).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (if (a % 7 == 0) ≠ flag then flag else !flag) then break
  let changed ← if a = seed then pure (if (a == 0) = flag then flag else !flag) else pure (if flag ≠ false then true else false)
  return a + (if changed = flag then changed else flag).toUInt64

def rangeRelationChoiceUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := a == seed
    let _unused := if flag = (UInt64.ofNat i == 0) then !flag else flag
    a := a + UInt64.ofNat i + 1
    if flag then break
  return a

def dependentChoiceEqual (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let flag := if _h : a = b then b else !b
  flag.toUInt64 + x

def dependentChoiceProposition (x y : UInt64) : UInt64 :=
  let flag := if _h : x < y then x == 0 else y != 0
  flag.toUInt64 + y

def dependentChoiceNested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  let flag := if _h : a then
      if _k : a ≠ b then decide (a = b) else !b
    else if _j : x ≤ y then a == b else a != b
  flag.toUInt64

def dependentChoiceCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let value := if _h : flag = outer then
        (let g := fun z : UInt64 => z + x; g y) == x
      else !flag
    (if _k : value then outer else !outer).toUInt64 + x
  f (y != 0)

def dependentChoiceLiterals (x y : UInt64) : UInt64 :=
  (if _h : True then true else false).toUInt64 * x +
  (if _h : False then true else false).toUInt64 * y +
  (if _h : true ≠ false then false else true).toUInt64 +
  (if _h : false = false then true else false).toUInt64 * 7

def dependentChoiceDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let flag ← pure (if _h : a = b then decide (a ≠ false) else !b)
  let mut z := x
  if _h : flag then z := z + y else z := z - y
  return z + (if _h : flag ≠ a then b else !b).toUInt64

def dependentChoiceTruth (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  let first := if _h : a then b else !b
  let second := if _h : a = true then b else !b
  (first == second).toUInt64 + (if _h : first = false then x == y else x != y).toUInt64

def dependentChoiceUnused (x y : UInt64) : UInt64 :=
  let _unused := if _h : (x == 0) ≠ (y == 0) then decide (x < y) else decide (x > y)
  x + y

def rangeDependentChoiceYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    let flag ← pure (if _h : first ≠ second then !second else first)
    a := a + (if _k : flag then first else !second).toUInt64
    if flag then break
  return a

def rangeDependentChoiceJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    let other ← pure (UInt64.ofNat i % 2 == 0)
    let next ← if even then pure (if _h : even = other then other else !other) else pure (if _h : even ≠ other then even else !even)
    if next then a := a + 2 else a := a + 5
    if (if _h : next = even then a % 7 == 0 else a % 11 == 0) then break
  return a

def rangeDependentChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := UInt64.ofNat i % 3 == 1
    let second := a == seed
    let skip := if _h : first ≠ second then first else !second
    if _h : skip then continue
    a := a + UInt64.ofNat i
    if (if _h : first = false then second else !second) then break
  return a

def rangeDependentChoiceCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (if _h : flag = outer then flag else !flag).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (if _h : flag ≠ outer then outer else !outer) + a
    a := g (UInt64.ofNat i % 2 == 0)
    if (if _h : (a % 11 == 0) ≠ outer then outer else !outer) then break
  return a + f (a == 0)

def rangeDependentChoiceBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := (if _h : flag = false then flag else !flag).toUInt64
  let stop := count + (if _h : flag ≠ true then !flag else flag).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    a := a + (if _h : even = flag then flag else !even).toUInt64
    if (if _h : a ≤ seed then even else flag) then break
  return a

def rangeDependentChoiceStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (if _h : flag = outer then !flag else outer)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (if _h : flag ≠ false then flag else !outer).toUInt64)
    f (if _h : (UInt64.ofNat i ≥ 7 : Bool) = outer then outer else !outer)

def rangeDependentChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + (if _h : flag = false then true else false).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (if _h : (a % 7 == 0) ≠ flag then flag else !flag) then break
  let changed ← if a = seed then pure (if _h : (a == 0) = flag then flag else !flag) else pure (if _h : flag ≠ false then true else false)
  return a + (if _h : changed = flag then changed else flag).toUInt64

def rangeDependentChoiceUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := a == seed
    let _unused := if _h : flag = (UInt64.ofNat i == 0) then !flag else flag
    a := a + UInt64.ofNat i + 1
    if flag then break
  return a

def boolLetNested (x y : UInt64) : UInt64 :=
  (let flag := x == 0; flag && y != 0).toUInt64 + x

def boolLetCapture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let flag := (let localFlag := y == 0; ((if localFlag then x else y) == x) || outer)
  flag.toUInt64 + y

def boolLetShadow (x y : UInt64) : UInt64 :=
  let a := x != 0
  (let a := a; let a := !a; a != false).toUInt64 + y

def boolLetUnused (x y : UInt64) : UInt64 :=
  (let _unused := x == y; y != 0).toUInt64

def boolLetDependent (x y : UInt64) : UInt64 :=
  (let flag := if _h : x < y then x == 0 else y != 0
   let other := x != y
   if _h : flag = other then !flag else decide (flag ≠ other)).toUInt64 + x

def boolLetHelper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    (let a := flag
     let b := outer
     (let g := fun z : UInt64 => if a then z + x else z + y; g y) == x || b).toUInt64
  f (y != 0) + x

def boolLetDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (let inside := x == 0; inside || y == 0)
  let other ← if flag then pure (let inside := y != 0; !inside) else pure (let inside := x != 0; inside)
  let mut z := x
  if (let same := flag == other; same) then z := z + y else z := z - y
  return z + (let answer := decide (flag ≠ other); answer).toUInt64

def boolLetNegated (x y : UInt64) : UInt64 :=
  let outside := y == 0
  (!(let inside := x == 0; inside == outside)).toUInt64 +
    (!!(let inside := outside; inside || x != 0)).toUInt64

def rangeBoolLetYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let even := a % 2 == 0; (if even then a else UInt64.ofNat i) != seed)
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag then break
  return a

def rangeBoolLetJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (let flag := a % 2 == 0; flag)
    let next ← if even then pure (let flag := UInt64.ofNat i == 0; !flag) else pure (let flag := a == seed; flag)
    if next then a := a + 2 else a := a + 5
    if (let flag := a % 7 == 0; flag != next) then break
  return a

def rangeBoolLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let skip := UInt64.ofNat i % 3 == 1; skip && a != 0) then continue
    a := a + UInt64.ofNat i
    if (let stop := a % 7 == 0; if _h : stop then a != seed else false) then break
  return a

def rangeBoolLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (let saved := outer; saved != flag).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (let saved := flag; saved || outer) + a
    a := g (let even := UInt64.ofNat i % 2 == 0; even)
    if (let saved := a % 11 == 0; saved != outer) then break
  return a + f (let saved := a == 0; saved)

def rangeBoolLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := (let flag := seed == 0; !flag).toUInt64
  let stop := count + (let flag := seed != 0; flag).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    a := a + (let flag := UInt64.ofNat i % 2 == 0; if flag then a == seed else !flag).toUInt64
    if (let flag := a % 7 == 0; flag) then break
  return a

def rangeBoolLetStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (let localFlag := flag; localFlag != outer)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (let localFlag := next; !localFlag).toUInt64)
    f (let even := UInt64.ofNat i % 2 == 0; even)

def rangeBoolLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (let positive := count != 0; positive)
  let mut a := seed + (let localFlag := flag; !localFlag).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (let stop := a % 7 == 0; stop != flag) then break
  let changed ← pure (let same := a == seed; same != flag)
  return a + (let answer := changed; answer || flag).toUInt64

def rangeBoolLetUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := a == seed
    let _unused := (let inner := UInt64.ofNat i == 0; !inner || flag)
    a := a + UInt64.ofNat i + 1
    if flag then break
  return a

def boolWordLetOriginal (x y : UInt64) : UInt64 :=
  (let word := x + y; word == 0).toUInt64

def boolWordLetMixed (x y : UInt64) : UInt64 :=
  let outer := x == 0
  (let word := if outer then x + y else x - y
   let flag := word == 0
   let more := word + y
   flag || more == x).toUInt64 + y

def boolWordLetShadow (x y : UInt64) : UInt64 :=
  (let x := x + y; let x := x * 3; x != y).toUInt64 + x

def boolWordLetHelper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  (let word := (let f := fun flag : Bool => if flag then x + y else x - y; f outer)
   if _h : word ≤ x then word == y else word != x).toUInt64

def boolWordLetDependent (x y : UInt64) : UInt64 :=
  (let word := x + y
   let flag := if _h : word < x then word == y else word != 0
   let other := if flag then word + x else word + y
   if _h : flag then other == x else other != y).toUInt64

def boolWordLetUnused (x y : UInt64) : UInt64 :=
  (let _word := x / y; y != 0).toUInt64 + x

def boolWordLetDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (let word := x + y; word != 0)
  let other ← if flag then pure (let word := x - y; word == 0) else pure (let word := x * y; word != 0)
  let mut z := x
  if (let word := if flag then x else y; word == z) then z := z + y else z := z - y
  return z + (let word := if other then z else y; word != 0).toUInt64

def boolWordLetNegated (x y : UInt64) : UInt64 :=
  (!(let word := x + y; word == 0)).toUInt64 +
    (!!(let word := x - y; decide (word < y))).toUInt64

def rangeBoolWordLetYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let word := a + UInt64.ofNat i; word % 7 == 0)
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag then break
  return a

def rangeBoolWordLetJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (let word := a + UInt64.ofNat i; word % 2 == 0)
    let next ← if even then pure (let word := a + seed; word != 0) else pure (let word := a - seed; word == 0)
    if next then a := a + 2 else a := a + 5
    if (let word := if next then a + 1 else a + 2; word % 7 == 0) then break
  return a

def rangeBoolWordLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let word := UInt64.ofNat i + a; word % 3 == 1) then continue
    a := a + UInt64.ofNat i
    if (let word := a - seed; if _h : word < a then word == 0 else word % 7 == 0) then break
  return a

def rangeBoolWordLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (let word := if flag then seed else count; word == 0).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (let word := if flag then a else seed; word != 0) + a
    a := g (let word := UInt64.ofNat i; word % 2 == 0)
    if (let word := a + seed; word % 11 == 0 && outer) then break
  return a + f (let word := a - seed; word == 0)

def rangeBoolWordLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := (let word := seed + 1; word == 0).toUInt64
  let stop := count + (let word := seed - 1; word != 0).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    a := a + (let word := UInt64.ofNat i + a; word % 2 == 0).toUInt64
    if (let word := a - seed; word % 7 == 0) then break
  return a

def rangeBoolWordLetStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (let word := if flag then a else seed; word == 0)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (let word := a - seed; word != 0).toUInt64)
    f (let word := UInt64.ofNat i; word % 2 == 0)

def rangeBoolWordLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (let word := count + seed; word != 0)
  let mut a := seed + (let word := if flag then seed else count; word == 0).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (let word := a - seed; word % 7 == 0) then break
  let changed ← pure (let word := a + seed; word == 0)
  return a + (let word := if changed then a else seed; word != 0).toUInt64

def rangeBoolWordLetUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := (let word := a + UInt64.ofNat i; word != seed)
    a := a + UInt64.ofNat i + 1
    if (let word := a - seed; word % 7 == 0) then break
  return a

def annotatedLetBoolean (x y : UInt64) : UInt64 :=
  (let flag : Id Bool := x == 0; flag && y != 0).toUInt64 + x

def annotatedLetWord (x y : UInt64) : UInt64 :=
  (let value : Id UInt64 := x + y; Id.run value == 0).toUInt64

def annotatedLetNested (x y : UInt64) : UInt64 :=
  (let flag : Id (Id Bool) := x == 0
   let value : Id (Id UInt64) := if flag && y != 0 then x + y else x - y
   let next : Id Bool := Id.run (Id.run value) != 0
   !(next : Bool)).toUInt64 + y

def annotatedLetHelper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    (let saved : Id Bool := flag
     let value : Id UInt64 := if saved && outer then x + y else x - y
     (Id.run value == x) || (saved && !outer)).toUInt64
  f (y != 0)

def annotatedLetUnused (x y : UInt64) : UInt64 :=
  (let _flag : Id (Id Bool) := x == y
   let _word : Id UInt64 := x / y
   x != y).toUInt64 + x

def annotatedLetDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (let saved : Id Bool := x == 0; !saved)
  let next ← if flag then
      pure (let value : Id UInt64 := Id.run (pure (x + y)); Id.run value == y)
    else pure (let value : Id (Id UInt64) := x - y; Id.run (Id.run value) != 0)
  return x + (let saved : Id Bool := next; saved && flag).toUInt64

def annotatedLetNegated (x y : UInt64) : UInt64 :=
  (!(let flag : Id Bool := x == 0; flag && y != 0)).toUInt64 +
    (!!(let value : Id (Id UInt64) := x - y; Id.run (Id.run value) == 0)).toUInt64

def annotatedLetShadow (x y : UInt64) : UInt64 :=
  (let value : Id UInt64 := x + y
   let value : Id (Id UInt64) := Id.run value * 3
   let flag : Id Bool := Id.run (Id.run value) == y
   flag || x == 0).toUInt64 + y

def rangeAnnotatedLetYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let word : Id UInt64 := a + UInt64.ofNat i
                    let stop : Id (Id Bool) := Id.run word % 7 == 0
                    (stop && seed != 0))
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag then break
  return a

def rangeAnnotatedLetJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (let value : Id UInt64 := a + UInt64.ofNat i; Id.run value % 2 == 0)
    let next ← if even then pure (let flag : Id Bool := UInt64.ofNat i == 0; !flag)
      else pure (let flag : Id (Id Bool) := a == seed; flag && even)
    if next then a := a + 2 else a := a + 5
    if (let value : Id UInt64 := a - seed; Id.run value % 7 == 0) then break
  return a

def rangeAnnotatedLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let skip : Id Bool := UInt64.ofNat i % 3 == 1; skip && a != 0) then continue
    a := a + UInt64.ofNat i
    if (let value : Id (Id UInt64) := a - seed; Id.run (Id.run value) % 7 == 0) then break
  return a

def rangeAnnotatedLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (let saved : Id Bool := flag; saved && outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (let value : Id UInt64 := if flag then a else seed; Id.run value != 0) + a
    a := g (let value : Id UInt64 := UInt64.ofNat i; Id.run value % 2 == 0)
    if (let stop : Id Bool := a % 11 == 0; stop && outer) then break
  return a + f (let value : Id UInt64 := a - seed; Id.run value == 0)

def rangeAnnotatedLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := (let value : Id UInt64 := seed + 1; Id.run value == 0).toUInt64
  let stop := count + (let positive : Id (Id Bool) := count != 0; !!positive).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    a := a + (let value : Id (Id UInt64) := UInt64.ofNat i + a; Id.run (Id.run value) % 2 == 0).toUInt64
    if (let stop : Id Bool := a % 7 == 0; stop && seed != 0) then break
  return a

def rangeAnnotatedLetStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (let value : Id UInt64 := if flag then a else seed; Id.run value == 0)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (let saved : Id (Id Bool) := next; !saved).toUInt64)
    f (let value : Id UInt64 := UInt64.ofNat i; Id.run value % 2 == 0)

def rangeAnnotatedLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (let saved : Id Bool := count != 0; saved || seed == 0)
  let mut a := seed + (let value : Id UInt64 := if flag then seed else count; Id.run value == 0).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (let value : Id (Id UInt64) := a - seed; Id.run (Id.run value) % 7 == 0) then break
  let changed ← pure (let saved : Id Bool := a == seed; !saved)
  return a + (let value : Id UInt64 := if changed then a else seed; Id.run value != 0).toUInt64

def rangeAnnotatedLetUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := (let value : Id UInt64 := a + UInt64.ofNat i
                   let saved : Id (Id Bool) := Id.run value != seed
                   !saved)
    a := a + UInt64.ofNat i + 1
    if (let value : Id UInt64 := a - seed; Id.run value % 7 == 0) then break
  return a

def nestedIdOperators (x y : UInt64) : UInt64 :=
  (Id.run (pure (x == 0)) && Id.run (pure (y != 0))).toUInt64 + x

def nestedIdBinding (x y : UInt64) : UInt64 :=
  (let flag : Id Bool := x == 0; Id.run flag || y != 0).toUInt64 + y

def nestedIdNested (x y : UInt64) : UInt64 :=
  (!(Id.run (pure (Id.run (pure (x == y)))) &&
    (let saved : Id (Id Bool) := x != 0; Id.run (Id.run saved)))).toUInt64 + x

def nestedIdHelper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    (Id.run (pure flag) && (let saved : Id Bool := outer; Id.run saved)).toUInt64 + x
  f (Id.run (pure (y == 0)))

def nestedIdDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (Id.run (pure (x == 0)) && y != 0)
  let next ← if flag then pure (Id.run (pure (x != y)) || flag)
    else pure (!(Id.run (pure (y == 0))))
  return x + (Id.run (pure next) && !flag).toUInt64

def nestedIdDependent (x y : UInt64) : UInt64 :=
  (if _h : Id.run (pure (x == 0)) && y != 0 then
    Id.run (pure (y == 1)) || x == y
   else Id.run (pure (x != y)) && y == 0).toUInt64 + x

def nestedIdUnused (x y : UInt64) : UInt64 :=
  (let _flag := Id.run (pure (x == y)) && x != 0
   Id.run (pure (x != y)) || y == 0).toUInt64 + x

def nestedIdShadow (x y : UInt64) : UInt64 :=
  (let flag : Id Bool := x == 0
   let flag : Id (Id Bool) := pure (Id.run flag && y != 0)
   Id.run (Id.run flag) || x == y).toUInt64 + y

def rangeNestedIdYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let stop := Id.run (pure (let value : Id Bool := (a + UInt64.ofNat i) % 7 == 0
                            Id.run value && Id.run (pure (seed != 0))))
    a := a + UInt64.ofNat i + 1
    if stop then break
  return a

def rangeNestedIdJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first ← pure (Id.run (pure (a % 2 == 0)) && seed != 0)
    let next ← if first then pure (Id.run (pure (UInt64.ofNat i == 0)) || a == seed)
      else pure (Id.run (pure (a != seed)) && !first)
    if next then a := a + 2 else a := a + 5
    if Id.run (pure (a % 7 == 0)) && seed != 0 then break
  return a

def rangeNestedIdContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if Id.run (pure (UInt64.ofNat i % 3 == 1)) && a != 0 then continue
    a := a + UInt64.ofNat i
    if Id.run (pure (a % 7 == 0)) && seed != 0 then break
  return a

def rangeNestedIdCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (Id.run (pure flag) && outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (Id.run (pure flag) || a == seed) + a
    a := g (Id.run (pure (UInt64.ofNat i % 2 == 0)) && outer)
    if Id.run (pure (a % 11 == 0)) && outer then break
  return a + f (Id.run (pure (a == seed)) || !outer)

def rangeNestedIdBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := (Id.run (pure (seed != 0)) && count != 0).toUInt64
  let stop := count + (Id.run (pure (count != 0)) || seed == 0).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    a := a + (Id.run (pure (UInt64.ofNat i % 2 == 0)) && a != 0).toUInt64
    if Id.run (pure (a % 7 == 0)) && seed != 0 then break
  return a

def rangeNestedIdStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (Id.run (pure flag) && a != 0)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (Id.run (pure (!next)) || flag).toUInt64)
    f (Id.run (pure (UInt64.ofNat i % 2 == 0)) && seed != 0)

def rangeNestedIdOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (Id.run (pure (count != 0)) && seed != 0)
  let mut a := seed + (Id.run (pure flag) || count == 0).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if Id.run (pure (a % 7 == 0)) && flag then break
  let changed ← pure (Id.run (pure (a != seed)) && flag)
  return a + (Id.run (pure changed) || !flag).toUInt64

def rangeNestedIdUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := Id.run (pure (a == seed)) && UInt64.ofNat i != 0
    a := a + UInt64.ofNat i + 1
    if Id.run (pure (a % 7 == 0)) && seed != 0 then break
  return a

def idLetWord (x y : UInt64) : UInt64 :=
  let value : Id UInt64 := x + y
  Id.run value + y

def idLetBoolean (x y : UInt64) : UInt64 :=
  let flag : Id Bool := x == 0
  if Id.run flag && y != 0 then x + y else x - y

def idLetLiteral (x y : UInt64) : UInt64 :=
  let value : Id (Id UInt64) := 3
  Id.run (Id.run value) + x + y

def idLetHelper (x y : UInt64) : UInt64 :=
  let f : Id (UInt64 → UInt64) := fun z => z + x
  f y

def idLetShadow (x y : UInt64) : UInt64 :=
  let value : Id (Id UInt64) := x + y
  let value : Id UInt64 := Id.run (Id.run value) * 3
  let flag : Id (Id Bool) := Id.run value == y
  if Id.run (Id.run flag) then Id.run value else x + y

def idLetOverflow (x y : UInt64) : UInt64 :=
  let value : Id (Id UInt64) := 18446744073709551619
  Id.run (Id.run value) + x + y

def idLetUnused (x y : UInt64) : UInt64 :=
  let _value : Id UInt64 := x / y
  let _flag : Id (Id Bool) := x == y
  x + y

def idLetDo (x y : UInt64) : UInt64 := Id.run do
  let flag : Id Bool := x != 0
  let value : Id (Id UInt64) := Id.run (pure (if Id.run flag then x + y else x - y))
  let saved ← pure (Id.run (Id.run value))
  let next : Id UInt64 := saved + y
  return Id.run next

def rangeIdLetYield (count seed : UInt64) : UInt64 := Id.run do
  let outer : Id Bool := seed != 0
  let mut a := seed
  for i in [:count.toNat] do
    let value : Id UInt64 := a + UInt64.ofNat i
    a := Id.run value + 1
    let stop : Id (Id Bool) := a % 7 == 0
    if Id.run (Id.run stop) && Id.run outer then break
  let value : Id UInt64 := a + seed
  return Id.run value

def rangeIdLetJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first : Id Bool := a % 2 == 0
    let next ← if Id.run first then pure (UInt64.ofNat i == 0) else pure (a != seed)
    let saved : Id (Id Bool) := next
    if Id.run (Id.run saved) then a := a + 2 else a := a + 5
    let stop : Id Bool := a % 7 == 0
    if Id.run stop && seed != 0 then break
  return a

def rangeIdLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip : Id (Id Bool) := UInt64.ofNat i % 3 == 1
    if Id.run (Id.run skip) && a != 0 then continue
    let value : Id UInt64 := a + UInt64.ofNat i
    a := Id.run value
    let stop : Id Bool := a % 7 == 0
    if Id.run stop && seed != 0 then break
  return a

def rangeIdLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer : Id Bool := seed != 0
  let f : Id (Bool → UInt64) := fun flag => (flag && Id.run outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g : Id (UInt64 → UInt64) := fun value => value + a
    a := g (f (UInt64.ofNat i % 2 == 0))
    let stop : Id (Id Bool) := a % 11 == 0
    if Id.run (Id.run stop) && Id.run outer then break
  return a + f (a == seed)

def rangeIdLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let first : Id UInt64 := 1
  let stop : Id (Id UInt64) := count + (seed != 0).toUInt64
  let mut a := seed
  for i in [(Id.run first).toNat:(Id.run (Id.run stop)).toNat:2] do
    let delta : Id UInt64 := UInt64.ofNat i + 1
    a := a + Id.run delta
    let stop : Id Bool := a % 7 == 0
    if Id.run stop && seed != 0 then break
  return a

def rangeIdLetStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Id (Bool → Id (ForInStep UInt64)) := fun flag => do
      let next : Id Bool := flag && a != 0
      if _h : Id.run next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (!flag).toUInt64)
    f (UInt64.ofNat i % 2 == 0)

def rangeIdLetOuter (count seed : UInt64) : UInt64 :=
  let initial : Id UInt64 := seed + 1
  let total : Id (Id UInt64) := Id.run do
    let mut a := Id.run initial
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i + 1
      let stop : Id Bool := a % 7 == 0
      if Id.run stop && seed != 0 then break
    return a
  Id.run (Id.run total) + seed

def rangeIdLetUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused : Id UInt64 := a / UInt64.ofNat i
    let _flag : Id (Id Bool) := a == seed
    a := a + UInt64.ofNat i + 1
    let stop : Id Bool := a % 7 == 0
    if Id.run stop && seed != 0 then break
  return a

def idArithmeticLeft (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  @HAdd.hAdd (Id UInt64) UInt64 UInt64 (@instHAdd UInt64 instAddUInt64) a y

def idArithmeticRight (x y : UInt64) : UInt64 :=
  let b : Id (Id UInt64) := y
  @HSub.hSub UInt64 (Id (Id UInt64)) UInt64 (@instHSub (Id UInt64) instSubUInt64) x b

def idArithmeticBoth (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  let b : Id (Id UInt64) := y
  @HMul.hMul (Id UInt64) (Id (Id UInt64)) (Id UInt64)
    (@instHMul (Id (Id UInt64)) instMulUInt64) a b

def idArithmeticBitwise (x y : UInt64) : UInt64 :=
  let a : Id (Id UInt64) := x
  let b : Id UInt64 := y
  @HXor.hXor (Id UInt64) (Id (Id UInt64)) UInt64 (@instHXorOfXorOp UInt64 instXorOpUInt64)
    (@HAnd.hAnd (Id (Id UInt64)) (Id UInt64) (Id UInt64)
      (@instHAndOfAndOp (Id UInt64) instAndOpUInt64) a b)
    (@HOr.hOr (Id (Id UInt64)) (Id UInt64) (Id (Id UInt64))
      (@instHOrOfOrOp (Id (Id UInt64)) instOrOpUInt64) a b)

def idArithmeticDivision (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  let b : Id (Id UInt64) := y
  @HDiv.hDiv (Id UInt64) (Id (Id UInt64)) UInt64
    (@instHDiv (Id UInt64) instDivUInt64) a b +
  @HMod.hMod (Id UInt64) (Id (Id UInt64)) UInt64
    (@instHMod (Id (Id UInt64)) instModUInt64) a b

def idArithmeticShifts (x y : UInt64) : UInt64 :=
  let a : Id (Id UInt64) := x
  let b : Id UInt64 := y
  @HShiftLeft.hShiftLeft (Id (Id UInt64)) (Id UInt64) UInt64
    (@instHShiftLeftOfShiftLeft (Id UInt64) instShiftLeftUInt64) a b ^^^
  @HShiftRight.hShiftRight (Id (Id UInt64)) (Id UInt64) UInt64
    (@instHShiftRightOfShiftRight (Id (Id UInt64)) instShiftRightUInt64) a b

def idArithmeticHelper (x y : UInt64) : UInt64 :=
  let a : Id (Id UInt64) := x
  let f := fun z : UInt64 =>
    (@HAdd.hAdd (Id (Id UInt64)) UInt64 UInt64
      (@instHAdd (Id UInt64) instAddUInt64) a z != 0).toUInt64
  if f y != 0 then f (x + y) + y else x

def idArithmeticDo (x y : UInt64) : UInt64 := Id.run do
  let a : Id UInt64 := x
  let value ← pure (@HAdd.hAdd (Id UInt64) UInt64 UInt64
    (@instHAdd (Id (Id UInt64)) instAddUInt64) a y)
  let b : Id (Id UInt64) := value
  let next : Id UInt64 := @HMul.hMul (Id (Id UInt64)) (Id UInt64) (Id UInt64)
    (@instHMul (Id UInt64) instMulUInt64) b a
  return Id.run next

def rangeIdArithmeticYield (count seed : UInt64) : UInt64 := Id.run do
  let bias : Id UInt64 := seed
  let mut a := seed
  for i in [:count.toNat] do
    let delta : Id (Id UInt64) := UInt64.ofNat i
    let current : Id UInt64 := a
    a := @HAdd.hAdd (Id UInt64) (Id (Id UInt64)) UInt64
      (@instHAdd (Id UInt64) instAddUInt64) current delta
    a := @HAdd.hAdd UInt64 (Id UInt64) UInt64 (@instHAdd UInt64 instAddUInt64) a bias
    if a % 7 == 0 && seed != 0 then break
  return a
def rangeIdArithmeticContinue (count seed : UInt64) : UInt64 := Id.run do
  let bias : Id (Id UInt64) := seed
  let mut a := seed
  for i in [:count.toNat] do
    let index : Id UInt64 := UInt64.ofNat i
    let value := @HAdd.hAdd (Id UInt64) (Id (Id UInt64)) UInt64
      (@instHAdd (Id UInt64) instAddUInt64) index bias
    if value % 3 == 1 then continue
    let current : Id UInt64 := a
    a := @HAdd.hAdd (Id UInt64) UInt64 UInt64
      (@instHAdd (Id (Id UInt64)) instAddUInt64) current value
    if a % 7 == 0 && seed != 0 then break
  return a

def rangeIdArithmeticBounds (count seed : UInt64) : UInt64 :=
  let limit : Id UInt64 := count
  let stop := @HAdd.hAdd (Id UInt64) UInt64 UInt64
    (@instHAdd (Id (Id UInt64)) instAddUInt64) limit 1
  let value : Id (Id UInt64) := Id.run do
    let mut a := seed
    for i in [1:stop.toNat:2] do
      let index : Id UInt64 := UInt64.ofNat i
      a := @HAdd.hAdd UInt64 (Id UInt64) UInt64
        (@instHAdd (Id UInt64) instAddUInt64) a index
      if a % 7 == 0 && seed != 0 then break
    return a
  @HAdd.hAdd (Id (Id UInt64)) UInt64 UInt64 (@instHAdd UInt64 instAddUInt64) value seed

def rangeIdArithmeticStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let current : Id (Id UInt64) := a
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let value := @HAdd.hAdd (Id (Id UInt64)) UInt64 UInt64
        (@instHAdd (Id UInt64) instAddUInt64) current (UInt64.ofNat i)
      if _h : flag then return .done value
      else return .yield (value + 1)
    f (a % 7 == 0 && seed != 0)

def rangeBooleanPredicateLoopLetBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let stop := f (UInt64.ofNat i % 3 == 0)
    a := a + UInt64.ofNat i + 1
    if stop && a % 7 == 0 then break
  return a

def rangeBooleanPredicateLoopLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => !b && a != seed
    let skip := f (UInt64.ofNat i % 3 == 0)
    if skip then continue
    let kept := f (!skip) || skip
    a := a + kept.toUInt64 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateLoopLetChoice (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == seed
    let g := fun b : Bool => !b && seed != 0
    let flag := if _h : a ≤ seed then f (g false) else g (f true)
    let flag := if f flag = g false then !(g flag) else f true
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag && a % 11 == 0 then break
  return a

def rangeBooleanPredicateLoopLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Bool → Id (Id Bool) := fun b => b && a != seed
    let flag : Id (Id Bool) := f (UInt64.ofNat i % 2 == 0)
    let _unused := f true
    let h := fun x : UInt64 => if @Eq Bool flag true then x + 3 else x + 1
    a := h a
    let flag := !(f false)
    if flag && a % 13 == 0 then break
  return a

def rangeBooleanPredicateOuterLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let flag := f (count == 0)
  let first : UInt64 := if flag then 0 else 1
  let stop := count + flag.toUInt64
  let mut a := seed + flag.toUInt64
  for i in [first.toNat:stop.toNat:2] do
    a := a + UInt64.ofNat i + 1
    if flag && a % 7 == 0 then break
  return if flag then a + 1 else a

def rangeBooleanPredicateOuterLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved := !(f false)
  let h := fun x : UInt64 => if saved then x + seed else x - seed
  let saved := f (count == 0)
  let mut a := seed
  for i in [:count.toNat] do
    let flag := f (a == seed)
    a := h a + UInt64.ofNat i
    if flag && saved then break
  return if saved then a + 1 else a

def rangeBooleanPredicateOuterLetChoice (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let flag := if _h : seed ≤ count then f (g false) else g (f true)
  let next := f flag != g false
  let _unused := if next then g false else f true
  let mut a := seed
  for i in [:count.toNat] do
    if next && a % 7 == 0 then continue
    a := a + UInt64.ofNat i + flag.toUInt64 + 1
  return if next then a + flag.toUInt64 else a

def rangeBooleanPredicateOuterLetId (count seed : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let flag : Id (Id Bool) := f (seed == 0)
  let g := fun b : Bool => (let saved := f b; Bool.toUInt64 saved) == 0
  let next := g flag
  let mut a := seed
  for i in [:count.toNat] do
    let saved := g (a == seed)
    a := a + UInt64.ofNat i + saved.toUInt64 + 1
    if next && a % 5 == 0 then break
  return if @Eq Bool flag true then a + next.toUInt64 else a

def natAliasLiteral (x y : UInt64) : UInt64 := x + (5 : Nat).toUInt64 - y

def natAliasOverflow (x y : UInt64) : UInt64 :=
  x + (18446744073709551621 : Nat).toUInt64 - y

def natAliasChoice (x y : UInt64) : UInt64 :=
  if x < (7 : Nat).toUInt64 then y + (19 : Nat).toUInt64 else x - (3 : Nat).toUInt64

def natAliasHelper (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n + (18446744073709551616 : Nat).toUInt64
  f x + f y

def natAliasDo (x y : UInt64) : UInt64 := Id.run do
  let a ← pure (x + (11 : Nat).toUInt64)
  let b ← pure (y + (13 : Nat).toUInt64)
  return a ^^^ b

def natAliasPredicate (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != (3 : Nat).toUInt64
  let g := fun n : UInt64 => f (n == (7 : Nat).toUInt64)
  (g y).toUInt64 + x

def rangeNatAliasStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + (7 : Nat).toUInt64
  return a

def rangeNatAliasCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:2] do
    if _h : i.toUInt64 == a then
      a := a + (5 : Nat).toUInt64
      break
    a := a + i.toUInt64
    if a % (3 : Nat).toUInt64 == 0 then continue
    a := a + 1
  return a

def rangeNatAliasCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n + (5 : Nat).toUInt64
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun n : UInt64 => f n + i.toUInt64
    a := g a
  return f a

def rangeNatAliasPredicateResult (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    let g := fun b : Bool => !(f b)
    if g (i.toUInt64 < seed) then
      a := a + 7
      break
    a := a + i.toUInt64 + 1
  return a

def booleanBoundResultValue (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let saved := f (x == 0); saved).toUInt64 + y

def booleanBoundResultBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  (let saved := x != 0; f (!saved)).toUInt64 + x

def booleanBoundResultNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let saved := f (x == 0); let saved := f (!saved); f saved).toUInt64 + y

def booleanBoundResultCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => let saved := f b; f (!saved)
  (g (x == 0)).toUInt64 + (g true).toUInt64

def booleanBoundResultApplication (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  ((fun saved : Bool => f (!saved)) (f (x == 0))).toUInt64 + x

def booleanBoundResultNamed (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let transform := fun saved : Bool => f (!saved); transform (f (x == 0))).toUInt64 + y

def rangeBooleanBoundResultStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    a := a + (let saved := f (i.toUInt64 == seed); f (!saved)).toUInt64 + 1
  return a

def rangeBooleanBoundResultCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (let saved := f (i.toUInt64 == seed); f (!saved)) then break
    a := a + i.toUInt64 + 1
  return a

def rangeBooleanBoundResultOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved := (let flag := f true; f (!flag))
  let mut a := seed + saved.toUInt64
  for i in [:count.toNat] do
    if (let flag := f (a == i.toUInt64); f (!flag)) then
      a := a + 3
      continue
    a := a + 1
  return a + saved.toUInt64

def rangeBooleanBoundResultHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => let saved := f b; f (!saved)
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => let saved := g b; f (!saved)
    if h (a == i.toUInt64) then break
    a := a + (g true).toUInt64 + 1
  return a + (g false).toUInt64

def booleanWordBoundResultValue (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let saved := x + (f true).toUInt64; f (saved == y)).toUInt64 + y

def booleanWordBoundResultBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  (let saved := x + y; f (saved == 0)).toUInt64 + x

def booleanWordBoundResultNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let saved := x + 1; let saved := saved + y; f (saved == y)).toUInt64 + y

def booleanWordBoundResultCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => let saved := n + x; f (saved == y)
  (g y).toUInt64 + (g x).toUInt64

def booleanWordBoundResultApplication (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  ((fun saved : UInt64 => f (saved == y)) (x + (f true).toUInt64)).toUInt64 + x

def booleanWordBoundResultNamed (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let transform := fun saved : UInt64 => f (saved == y); transform (x + (f true).toUInt64)).toUInt64 + y

def rangeBooleanWordBoundResultStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    a := a + (let saved := a + i.toUInt64; f (saved == seed)).toUInt64 + 1
  return a

def rangeBooleanWordBoundResultCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (let saved := a + i.toUInt64; f (saved != seed)) then break
    a := a + i.toUInt64 + 1
  return a

def rangeBooleanWordBoundResultOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved := (let value := seed + 1; f (value == 0))
  let mut a := seed + saved.toUInt64
  for i in [:count.toNat] do
    if (let value := a + i.toUInt64; f (value == seed)) then
      a := a + 3
      continue
    a := a + 1
  return a + saved.toUInt64

def rangeBooleanWordBoundResultHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => let saved := n + seed; f (saved == 0)
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun n : UInt64 => let saved := n + a; g saved
    if h i.toUInt64 then break
    a := a + (g a).toUInt64 + 1
  return a + (g seed).toUInt64

def booleanResultBindBool (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (Id.run do
    let saved ← pure (f (x == 0))
    return f (!saved)).toUInt64 + y

def booleanResultBindWord (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  (Id.run do
    let saved ← pure (x + (f true).toUInt64)
    return f (saved == y)).toUInt64 + x

def booleanResultBindNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (Id.run do
    let saved ← pure (f (x == 0))
    let word ← pure (x + saved.toUInt64)
    let saved ← pure (f (word == y))
    return f (!saved)).toUInt64 + y

def booleanResultBindCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => Id.run do
    let saved ← pure (f b)
    return f (!saved)
  (g (x == 0)).toUInt64 + (g true).toUInt64

def booleanResultBindUnused (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (Id.run do
    let _saved ← pure (f (x == 0))
    let _word ← pure (x + y)
    return f true).toUInt64 + x

def booleanResultBindCondition (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if Id.run (do let saved ← pure (f (x == 0)); return f (!saved)) then x + 3 else y + 7

def rangeBooleanResultBindStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    a := a + (Id.run do
      let saved ← pure (f (i.toUInt64 == seed))
      return f (!saved)).toUInt64 + 1
  return a

def rangeBooleanResultBindCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if Id.run (do let saved ← pure (a + i.toUInt64); return f (saved != seed)) then break
    a := a + i.toUInt64 + 1
  return a

def rangeBooleanResultBindOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved := Id.run do
    let flag ← pure (f true)
    return f (!flag)
  let mut a := seed + saved.toUInt64
  for i in [:count.toNat] do
    if Id.run (do let flag ← pure (f (a == i.toUInt64)); return f (!flag)) then
      a := a + 3
      continue
    a := a + 1
  return a + saved.toUInt64

def rangeBooleanResultBindHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => Id.run do
    let saved ← pure (n + seed)
    return f (saved == 0)
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun n : UInt64 => Id.run do
      let saved ← pure (n + a)
      return g saved
    if h i.toUInt64 then break
    a := a + (g a).toUInt64 + 1
  return a + (g seed).toUInt64

def savedMixedLeft (x y : UInt64) : UInt64 :=
  let flag := x != 0
  if flag ∧ x < y then x + 3 else y + 7

def savedMixedRight (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let flag := f (x == 0)
  if x ≤ y ∨ flag then (f (!flag)).toUInt64 + x else y

def savedMixedPair (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y == 0
  if a ∧ ¬ b then x + y else x - y

def savedMixedNegation (x y : UInt64) : UInt64 :=
  let flag := x != y
  if ¬ (flag ∧ ¬ (x = 0 ∨ !flag)) then x + 1 else y + 2

def savedMixedDecision (x y : UInt64) : UInt64 :=
  let flag := x != y
  let saved := decide ((flag ∧ x < y) ∨ (!flag ∧ y < x))
  saved.toUInt64 + x

def savedMixedHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => if b ∧ x < y then !b else b
  let a := x != 0
  (f a).toUInt64 + (f (!a)).toUInt64 + y

def rangeSavedMixedStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := a != 0
    if flag ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangeSavedMixedContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := i.toUInt64 == seed
    if a = 0 ∨ !flag then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeSavedMixedOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let mut a := if flag ∧ count < seed then seed + 1 else seed
  for i in [:count.toNat] do
    let other := a == i.toUInt64
    if flag ∧ ¬ other then a := a + 2 else a := a + 1
  return a + (decide (flag ∨ a = seed)).toUInt64

def rangeSavedMixedHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => if b ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    let flag := f (a == 0)
    if ¬ (flag ∧ i.toUInt64 < a) then
      a := a + (f (!flag)).toUInt64 + 1
    else break
  return a

def callMixedBool (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if f (x == 0) ∧ x < y then x + 3 else y + 7

def callMixedWord (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n != x
  if x ≤ y ∨ f (x + y) then (f y).toUInt64 + x else y

def callMixedPair (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => n != x
  if f true ∧ ¬ g y then x + y else x - y

def callMixedNegation (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => n != x
  if ¬ (f (g y) ∧ ¬ (x = 0 ∨ !f true)) then x + 1 else y + 2

def callMixedDecision (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => n != x
  let saved := decide ((f (x == 0) ∧ x < y) ∨ (!g y ∧ y < x))
  saved.toUInt64 + x

def callMixedHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => if f (n == 0) ∧ n < x then f true else f false
  (g x).toUInt64 + (g y).toUInt64 + y

def rangeCallMixedStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != 0
    if f (i.toUInt64 != seed) ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangeCallMixedContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n != seed
    if a = 0 ∨ !f i.toUInt64 then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeCallMixedOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => n != seed
  let mut a := if f true ∧ count < seed then seed + 1 else seed
  for i in [:count.toNat] do
    if f (g i.toUInt64) ∧ ¬ g a then a := a + 2 else a := a + 1
  return a + (decide (f true ∨ a = seed)).toUInt64

def rangeCallMixedHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if f b ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ (g (a == 0) ∧ i.toUInt64 < a) then
      a := a + (f (g true)).toUInt64 + 1
    else break
  return a

def extendedMixedJunction (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if (f (x == 0) && (x != y || f true)) ∧ x < y then x + 3 else y + 7

def extendedMixedChoice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if x ≤ y ∨ (if x < y then f true else f false) then x + 1 else y

def extendedMixedLet (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if (Id.run (let flag := f (x == 0); let word := x + flag.toUInt64; f (word != y))) ∧ x < y then x + y else x - y

def extendedMixedBind (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if x = 0 ∨ (Id.run do let flag ← pure (f (x == 0)); return f (!flag)) then x + 1 else y + 2

def extendedMixedWrapped (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let saved := decide ((Id.run (pure (f true))) ∧ x < y)
  saved.toUInt64 + x

def extendedMixedRelation (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => if (f b == b) ∧ x < y then f true else f false
  (g true).toUInt64 + (g false).toUInt64 + y

def rangeExtendedMixedStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != 0
    if (f (i.toUInt64 != seed) || f true) ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangeExtendedMixedContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n != seed
    if a = 0 ∨ (Id.run (let flag := f i.toUInt64; !flag)) then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeExtendedMixedOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => n != seed
  let mut a := if (Id.run (pure (f true))) ∧ count < seed then seed + 1 else seed
  for i in [:count.toNat] do
    if (f (g i.toUInt64) != g a) ∧ a < seed then a := a + 2 else a := a + 1
  return a + (decide ((f true && g a) ∨ a = seed)).toUInt64

def rangeExtendedMixedHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if (Id.run do let flag ← pure (f b); return f (!flag)) ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if (if a = 0 then g true else g false) ∧ i.toUInt64 < a then break
    a := a + (f (g true)).toUInt64 + 1
  return a

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
  if (let _saved := x == y; let _word := x + y; True) then y + 1 else x

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

def decisionLetUnused (x y : UInt64) : UInt64 :=
  if (let _saved := x == y; True) ∧ (let _word := x + y; False) then x else y + 1

def decisionLetLeft (x y : UInt64) : UInt64 :=
  if (let _word := x + y; let _saved := x == y; True) ∧ x < y then x + 3 else y + 7

def decisionLetRight (x y : UInt64) : UInt64 :=
  let flag := x == 0
  if flag ∨ (let _word := x + y; False) then x + 1 else y + 2

def decisionLetDependent (x y : UInt64) : UInt64 :=
  let flag := x == y
  if _h : (let _saved := flag; True) ∧ flag then x + y else x - y

def decisionLetSaved (x y : UInt64) : UInt64 :=
  let flag := decide ((let _saved := x == 0; False) ∨ (let _word := x + y; True))
  flag.toUInt64 + x

def decisionLetHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => if (let _saved := b; True) ∧ x < y then !b else b
  (f true).toUInt64 + (f false).toUInt64 + y

def rangeDecisionLetStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let _saved := a == seed; True) ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangeDecisionLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if a = seed ∨ (let _word := a + i.toUInt64; False) then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeDecisionLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let mut a := if flag ∧ (let _saved := flag; True) then seed + 1 else seed
  for i in [:count.toNat] do
    if (let _word := a + i.toUInt64; False) ∨ a < seed then a := a + 2 else a := a + 1
  return a + (decide ((let _saved := flag; True) ∧ a = seed)).toUInt64

def rangeDecisionLetHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => if (let _saved := b; True) ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if f true ∧ (let _word := a + i.toUInt64; True) then break
    a := a + (f (a == 0)).toUInt64 + 1
  return a

def localNotFlag (x y : UInt64) : UInt64 :=
  let flag := x == y
  if ¬ flag then x + 3 else y + 7

def localNotCall (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if ¬ f (x == 0) then x + 1 else y + 2

def localNotNested (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n != x
  if _h : ¬ ¬ ¬ f y then x + y else x - y

def localNotDecision (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let flag := decide (¬ (if x < y then f true else f false))
  flag.toUInt64 + x

def localNotLet (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  if ¬ (Id.run (let saved := f (x == 0); f (!saved))) then x + 1 else y + 2

def localNotHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => if ¬ f b then !b else b
  (g true).toUInt64 + (g false).toUInt64 + y

def rangeLocalNotStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != 0
    if ¬ f (i.toUInt64 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangeLocalNotContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n != seed
    if ¬ f a then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeLocalNotOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let flag := f true
  let mut a := if ¬ flag then seed + 1 else seed
  for i in [:count.toNat] do
    if ¬ (f (a == 0) || f (i.toUInt64 == seed)) then a := a + 2 else a := a + 1
  return a + (decide (¬ f true)).toUInt64

def rangeLocalNotHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if ¬ f b then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ ¬ g (a == 0) then break
    a := a + (f (g true)).toUInt64 + i.toUInt64 + 1
  return a

def rangeBoolWordHelperRepeat (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x + seed + 1
  let value := Id.run do
    let mut a := f seed
    for i in [:count.toNat] do
      a := f a + f i.toUInt64
    return a
  f value == f (f seed)

def rangeBoolWordHelperCount (count seed : UInt64) : Bool :=
  let limit := fun x : UInt64 => x % 17
  let value := Id.run do
    let mut a := seed
    for i in [:(limit count).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed + limit count

def rangeBoolWordHelperInitial (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x * 3 + seed
  let value := Id.run do
    let mut a := f 0
    for i in [:count.toNat] do
      a := a + f i.toUInt64
    return a
  value == f 0

def rangeBoolWordHelperNested (count seed : UInt64) : Id Bool :=
  let f := fun x : UInt64 => x + seed
  let g := fun x : UInt64 => f (x * 3) + f x
  let value := Id.run do
    let mut a := g 0
    for i in [:count.toNat] do
      a := g (a + i.toUInt64)
    return a
  pure (g value == g seed)

def rangeBoolWordHelperFlag (count : UInt64) (flag : Bool) : Bool :=
  let f := fun x : UInt64 => if flag then x + 7 else x - 3
  let value := Id.run do
    let mut a := f count
    for i in [:count.toNat] do
      a := f (a + i.toUInt64)
    return a
  flag && value == f count

def rangeBoolWordHelperExit (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x + seed % 5 + 1
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f (a + i.toUInt64)
      if a % 7 == 0 then break
    return a
  f value % 7 == 0

def rangeBoolWordHelperContinue (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 3
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f i.toUInt64 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  f value == f seed

def rangeBoolWordHelperStride (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 3
  let value := Id.run do
    let mut a := seed
    for i in [(f seed).toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  f value == f seed

def rangeBoolWordHelperId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (x : UInt64) : Id (Id UInt64) := pure (pure (x + seed + 1))
  let value : Id UInt64 := Id.run do
    let mut a := Id.run (Id.run (f 0))
    for i in [:(Id.run count).toNat] do
      a := Id.run (Id.run (f (a + i.toUInt64)))
    return a
  pure (Id.run (Id.run (f (Id.run value))) == seed)

def rangeBoolWordHelperShadow (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x + seed
  let initial := f 0
  let f := fun x : UInt64 => f x + count
  let value := Id.run do
    let mut a := initial
    for i in [:count.toNat] do
      a := f (a + i.toUInt64)
    return a
  f value == f initial

def rangeBoolBooleanHelperRepeat (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => seed + flag.toUInt64 + 1
  let value := Id.run do
    let mut a := f true
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0) + f false
    return a
  value == f true

def rangeBoolBooleanHelperCount (count seed : UInt64) : Bool :=
  let limit := fun flag : Bool => if flag then count % 17 else count % 5
  let value := Id.run do
    let mut a := seed
    for i in [:(limit (seed % 2 == 0)).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed + limit true

def rangeBoolBooleanHelperInitial (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => seed * 3 + flag.toUInt64
  let value := Id.run do
    let mut a := f false
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a
  value == f false

def rangeBoolBooleanHelperNested (count seed : UInt64) : Id Bool :=
  let f := fun flag : Bool => seed + flag.toUInt64
  let g := fun flag : Bool => f (!flag) + f flag
  let value := Id.run do
    let mut a := g false
    for i in [:count.toNat] do
      a := a + g (i.toUInt64 % 3 == 0)
    return a
  pure (value == g (seed == 0))

def rangeBoolBooleanHelperFlag (count : UInt64) (flag : Bool) : Bool :=
  let f := fun input : Bool => if flag && input then count + 7 else count - 3
  let value := Id.run do
    let mut a := f flag
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a
  flag && value == f flag

def rangeBoolBooleanHelperExit (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => seed % 5 + flag.toUInt64 + 1
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
      if a % 7 == 0 then break
    return a
  f (value % 7 == 0) == f true

def rangeBoolBooleanHelperContinue (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => if flag then 0 else seed % 3 + 1
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f (i.toUInt64 % 2 == 0) == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  f (value == seed) == f true

def rangeBoolBooleanHelperStride (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => if flag then seed % 3 else 0
  let value := Id.run do
    let mut a := seed
    for i in [(f true).toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  f (value == seed) == f true

def rangeBoolBooleanHelperId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (flag : Bool) : Id (Id UInt64) := pure (pure (seed + flag.toUInt64 + 1))
  let value : Id UInt64 := Id.run do
    let mut a := Id.run (Id.run (f false))
    for i in [:(Id.run count).toNat] do
      a := a + Id.run (Id.run (f (i.toUInt64 % 2 == 0)))
    return a
  pure (Id.run value == Id.run (Id.run (f false)))

def rangeBoolBooleanHelperShadow (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => seed + flag.toUInt64
  let initial := f false
  let f := fun flag : Bool => f (!flag) + count
  let value := Id.run do
    let mut a := initial
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a
  value == f (initial == seed)

def rangeBoolPredicateHelperRepeat (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 2 == seed % 2
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + (f i.toUInt64).toUInt64 + (f a).toUInt64
    return a
  f value && f seed

def rangeBoolPredicateHelperCount (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 3 == seed % 3
  let value := Id.run do
    let mut a := seed
    for i in [:(if f count then count % 17 else count % 5).toNat] do
      a := a + i.toUInt64 + 1
    return a
  f value

def rangeBoolPredicateHelperNested (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 2 == seed % 2
  let g := fun x : UInt64 => f (x + 1) || f x
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + (g i.toUInt64).toUInt64
    return a
  g value

def rangeBoolPredicateHelperExit (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 7 == seed % 7
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if f a then break
    return a
  f value

def rangeBoolPredicateHelperId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (x : UInt64) : Id (Id Bool) := pure (pure (x % 3 == seed % 3))
  let value : Id UInt64 := Id.run do
    let mut a := seed
    for i in [:(Id.run count).toNat] do
      if Id.run (Id.run (f i.toUInt64)) then continue
      a := a + i.toUInt64 + 1
    return a
  pure (Id.run (Id.run (f (Id.run value))))

def rangeBoolBooleanPredicateHelperRepeat (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => flag || seed % 2 == 0
  let value := Id.run do
    let mut a := seed + (f false).toUInt64
    for i in [:count.toNat] do
      a := a + (f (i.toUInt64 % 2 == 0)).toUInt64 + (f true).toUInt64
    return a
  f (value == seed)

def rangeBoolBooleanPredicateHelperFlag (count : UInt64) (flag : Bool) : Bool :=
  let f := fun input : Bool => flag && !input
  let value := Id.run do
    let mut a := (f false).toUInt64
    for i in [:count.toNat] do
      if f (i.toUInt64 % 2 == 0) then continue
      a := a + i.toUInt64 + 1
    return a
  f (value == count)

def rangeBoolBooleanPredicateHelperNested (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => flag || seed == 0
  let g := fun flag : Bool => f (!flag) && f flag
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + (g (i.toUInt64 % 3 == 0)).toUInt64
    return a
  g (value == seed)

def rangeBoolBooleanPredicateHelperStride (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => flag && seed % 3 == 0
  let value := Id.run do
    let mut a := seed
    for i in [(f true).toUInt64.toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if f (a % 5 == 0) then break
    return a
  f (value == seed)

def rangeBoolBooleanPredicateHelperId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (flag : Bool) : Id (Id Bool) := pure (pure (flag || seed % 2 == 0))
  let value : Id UInt64 := Id.run do
    let mut a := seed
    for i in [:(Id.run count).toNat] do
      a := a + (Id.run (Id.run (f (i.toUInt64 % 2 == 0)))).toUInt64
    return a
  pure (Id.run (Id.run (f (Id.run value == seed))))

def rangeBoolHelperInputIdWord (count seed : UInt64) : Bool :=
  let f (x : Id UInt64) := Id.run x + seed + 1
  let value := Id.run do
    let mut a := f (pure seed)
    for i in [:count.toNat] do
      a := f (pure (a + i.toUInt64))
    return a
  f (pure value) == f (pure seed)

def rangeBoolHelperInputIdBooleanWord (count seed : UInt64) : Bool :=
  let f (flag : Id Bool) := seed + (Id.run flag).toUInt64
  let value := Id.run do
    let mut a := f (pure false)
    for i in [:count.toNat] do
      a := a + f (pure (i.toUInt64 % 2 == 0))
    return a
  value == f (pure true)

def rangeBoolHelperInputIdPredicate (count seed : UInt64) : Bool :=
  let f (x : Id UInt64) := Id.run x % 2 == seed % 2
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + (f (pure i.toUInt64)).toUInt64
    return a
  f (pure value)

def rangeBoolHelperInputIdBooleanPredicate (count : UInt64) (flag : Bool) : Bool :=
  let f (input : Id Bool) := Id.run input && flag
  let value := Id.run do
    let mut a := (f (pure true)).toUInt64
    for i in [:count.toNat] do
      a := a + (f (pure (i.toUInt64 % 2 == 0))).toUInt64
    return a
  f (pure (value == count))

def rangeBoolHelperInputIdRepeated (count seed : UInt64) : Id Bool :=
  let f (x : Id (Id (Id UInt64))) : Id (Id UInt64) := pure (pure (Id.run (Id.run (Id.run x)) + seed))
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := Id.run (Id.run (f (pure (pure (pure (a + i.toUInt64))))))
    return a
  pure (value == Id.run (Id.run (f (pure (pure (pure seed))))))

def rangeBoolHelperInputIdBound (count seed : UInt64) : Bool :=
  let f (flag : Id (Id Bool)) := if Id.run (Id.run flag) then count % 17 else count % 5
  let value := Id.run do
    let mut a := seed
    for i in [:(f (pure (pure (seed % 2 == 0)))).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed + f (pure (pure true))

def rangeBoolHelperInputIdExit (count seed : UInt64) : Bool :=
  let f (x : Id (Id UInt64)) : Id Bool := pure (Id.run (Id.run x) % 7 == seed % 7)
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if Id.run (f (pure (pure a))) then break
    return a
  Id.run (f (pure (pure value)))

def rangeBoolHelperInputIdContinue (count seed : UInt64) : Id Bool :=
  let f (flag : Id (Id Bool)) : Id (Id Bool) := pure (pure (Id.run (Id.run flag) || seed == 0))
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if Id.run (Id.run (f (pure (pure (i.toUInt64 % 2 == 0))))) then continue
      a := a + i.toUInt64 + 1
    return a
  pure (Id.run (Id.run (f (pure (pure (value == seed))))))

def rangeBoolHelperInputIdMixed (count seed : UInt64) : Bool :=
  let f (x : Id UInt64) := Id.run x + seed
  let g (flag : Id Bool) := f (pure (Id.run flag).toUInt64)
  let value := Id.run do
    let mut a := g (pure false)
    for i in [:count.toNat] do
      a := a + g (pure (i.toUInt64 % 2 == 0))
    return a
  value == g (pure true)

def rangeBoolHelperInputIdShadow (count seed : UInt64) : Bool :=
  let f (x : Id UInt64) := Id.run x + seed
  let initial := f (pure 0)
  let f (x : Id (Id UInt64)) := f (pure (Id.run (Id.run x))) + count
  let value := Id.run do
    let mut a := initial
    for i in [:count.toNat] do
      a := f (pure (pure (a + i.toUInt64)))
    return a
  value == f (pure (pure initial))

def rangeBoolManyHelperBinaryRepeat (count seed : UInt64) : Bool :=
  let f := fun x y : UInt64 => x + 3 * y + seed
  let value := Id.run do
    let mut a := f seed 1
    for i in [:count.toNat] do
      a := f a i.toUInt64 + f i.toUInt64 a
    return a
  f value 1 == f seed 1

def rangeBoolManyHelperBinaryCount (count seed : UInt64) : Bool :=
  let limit := fun x y : UInt64 => (x + y) % 17
  let value := Id.run do
    let mut a := seed
    for i in [:(limit count seed).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed + limit seed count

def rangeBoolManyHelperTernaryInitial (count seed : UInt64) : Bool :=
  let f := fun x y z : UInt64 => x + y * 3 + z * 5 + seed
  let value := Id.run do
    let mut a := f 0 1 2
    for i in [:count.toNat] do
      a := f a i.toUInt64 3
    return a
  value == f 0 1 2

def rangeBoolManyHelperTernaryNested (count seed : UInt64) : Bool :=
  let f := fun x y z : UInt64 => x + 3 * y + 5 * z + seed
  let g := fun x y z : UInt64 => f (x + 1) (y + 2) (z + 3) + f z y x
  let value := Id.run do
    let mut a := g 0 1 2
    for i in [:count.toNat] do
      a := g a i.toUInt64 1
    return a
  value == g seed 1 2

def rangeBoolManyHelperFiveFlag (count : UInt64) (flag : Bool) : Bool :=
  let f := fun a b c d e : UInt64 => if flag then a + 3*b + 5*c + 7*d + 11*e else a-b-c-d-e
  let value := Id.run do
    let mut a := f count 1 2 3 4
    for i in [:count.toNat] do
      a := f a i.toUInt64 1 2 count
    return a
  flag && value == f count 1 2 3 4

def rangeBoolManyHelperBinaryExit (count seed : UInt64) : Bool :=
  let f := fun x y : UInt64 => x + 3 * y + seed % 5 + 1
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a i.toUInt64
      if a % 7 == 0 then break
    return a
  f value 1 % 7 == 0

def rangeBoolManyHelperTernaryContinue (count seed : UInt64) : Bool :=
  let f := fun x y z : UInt64 => (x + 3 * y + 5 * z) % 3
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f i.toUInt64 a seed == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  f value seed 1 == f seed value 1

def rangeBoolManyHelperFiveStride (count seed : UInt64) : Bool :=
  let f := fun a b c d e : UInt64 => (a + 3*b + 5*c + 7*d + 11*e) % 3
  let value := Id.run do
    let mut a := seed
    for i in [(f seed 1 2 3 4).toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  f value 1 2 3 4 == f seed 1 2 3 4

def rangeBoolManyHelperFiveId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (a b c d e : UInt64) : Id (Id UInt64) := pure (pure (a + 3*b + 5*c + 7*d + 11*e + seed))
  let value : Id UInt64 := Id.run do
    let mut a := Id.run (Id.run (f seed 1 2 3 4))
    for i in [:(Id.run count).toNat] do
      a := Id.run (Id.run (f a i.toUInt64 1 2 3))
    return a
  pure (Id.run value == Id.run (Id.run (f seed 1 2 3 4)))

def rangeBoolManyHelperBinaryShadow (count seed : UInt64) : Bool :=
  let f := fun x y : UInt64 => x + 3 * y + seed
  let initial := f 0 1
  let f := fun x y : UInt64 => f y x + count
  let value := Id.run do
    let mut a := initial
    for i in [:count.toNat] do
      a := f a i.toUInt64
    return a
  value == f initial 1

def rangeBoolUnitHelperRepeat (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x + seed + 1
  let value := Id.run do
    let mut a := f () seed
    for i in [:count.toNat] do
      a := f () a + f () i.toUInt64
    return a
  f () value == f () (f () seed)

def rangeBoolUnitHelperCount (count seed : UInt64) : Bool :=
  let limit := fun (_unit : PUnit) (x : UInt64) => x % 17
  let value := Id.run do
    let mut a := seed
    for i in [:(limit () count).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed + limit () count

def rangeBoolUnitHelperInitial (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x * 3 + seed
  let value := Id.run do
    let mut a := f () 0
    for i in [:count.toNat] do
      a := a + f () i.toUInt64
    return a
  value == f () 0

def rangeBoolUnitHelperNested (count seed : UInt64) : Id Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x + seed
  let g := fun (_unit : Unit) (x : UInt64) => f () (x * 3) + f () x
  let value := Id.run do
    let mut a := g () 0
    for i in [:count.toNat] do
      a := g () (a + i.toUInt64)
    return a
  pure (g () value == g () seed)

def rangeBoolUnitHelperFlag (count : UInt64) (flag : Bool) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => if flag then x + 7 else x - 3
  let value := Id.run do
    let mut a := f () count
    for i in [:count.toNat] do
      a := f () (a + i.toUInt64)
    return a
  flag && value == f () count

def rangeBoolUnitHelperExit (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x + seed % 5 + 1
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f () (a + i.toUInt64)
      if a % 7 == 0 then break
    return a
  f () value % 7 == 0

def rangeBoolUnitHelperContinue (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x % 3
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f () i.toUInt64 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  f () value == f () seed

def rangeBoolUnitHelperStride (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x % 3
  let value := Id.run do
    let mut a := seed
    for i in [(f () seed).toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  f () value == f () seed

def rangeBoolUnitHelperId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (_unit : Unit) (x : UInt64) : Id (Id UInt64) := pure (pure (x + seed + 1))
  let value : Id UInt64 := Id.run do
    let mut a := Id.run (Id.run (f () 0))
    for i in [:(Id.run count).toNat] do
      a := Id.run (Id.run (f () (a + i.toUInt64)))
    return a
  pure (Id.run (Id.run (f () (Id.run value))) == seed)

def rangeBoolUnitHelperShadow (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x + seed
  let initial := f () 0
  let f := fun (_unit : Unit) (x : UInt64) => f () x + count
  let value := Id.run do
    let mut a := initial
    for i in [:count.toNat] do
      a := f () (a + i.toUInt64)
    return a
  f () value == f () initial

def rangeBoolOuterConditionEqual (count seed : UInt64) : Bool :=
  if seed == 0 then
      let f := fun x : UInt64 => x + seed + 1
      let value := Id.run do
        let mut a := f seed
        for i in [:count.toNat] do
          a := f a + f i.toUInt64
        return a
      f value == f (f seed)
  else
      let f := fun x : UInt64 => x + seed % 5 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := f (a + i.toUInt64)
          if a % 7 == 0 then break
        return a
      f value % 7 == 0

def rangeBoolOuterConditionOrder (count seed : UInt64) : Bool :=
  if seed < count then
      let limit := fun x : UInt64 => x % 17
      let value := Id.run do
        let mut a := seed
        for i in [:(limit count).toNat] do
          a := a + i.toUInt64 + 1
        return a
      value == seed + limit count
  else
      let f := fun x : UInt64 => x * 3 + seed
      let value := Id.run do
        let mut a := f 0
        for i in [:count.toNat] do
          a := a + f i.toUInt64
        return a
      value == f 0

def rangeBoolOuterConditionFlag (count : UInt64) (flag : Bool) : Bool :=
  if flag then
      let f := fun x : UInt64 => if flag then x + 7 else x - 3
      let value := Id.run do
        let mut a := f count
        for i in [:count.toNat] do
          a := f (a + i.toUInt64)
        return a
      flag && value == f count
  else
      let f := fun input : Bool => if flag && input then count + 7 else count - 3
      let value := Id.run do
        let mut a := f flag
        for i in [:count.toNat] do
          a := a + f (i.toUInt64 % 2 == 0)
        return a
      flag && value == f flag

def rangeBoolOuterConditionNested (count seed : UInt64) : Bool :=
  if seed % 3 == 0 then
    if seed < count then
        let limit := fun x : UInt64 => x % 17
        let value := Id.run do
          let mut a := seed
          for i in [:(limit count).toNat] do
            a := a + i.toUInt64 + 1
          return a
        value == seed + limit count
    else
        let f := fun x : UInt64 => x * 3 + seed
        let value := Id.run do
          let mut a := f 0
          for i in [:count.toNat] do
            a := a + f i.toUInt64
          return a
        value == f 0
  else
      let f := fun x : UInt64 => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value == f seed

def rangeBoolOuterConditionHelper (count seed : UInt64) : Bool :=
  let p := fun x : UInt64 => x % 3 == seed % 3
  if p count then
      let f := fun x : UInt64 => x + seed + 1
      let value := Id.run do
        let mut a := f seed
        for i in [:count.toNat] do
          a := f a + f i.toUInt64
        return a
      f value == f (f seed)
  else
      let f := fun x : UInt64 => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value == f seed

def rangeBoolOuterConditionExit (count seed : UInt64) : Bool :=
  if count != 0 then
      let f := fun x y : UInt64 => x + 3 * y + seed % 5 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := f a i.toUInt64
          if a % 7 == 0 then break
        return a
      f value 1 % 7 == 0
  else
      let f := fun flag : Bool => seed % 5 + flag.toUInt64 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := a + f (i.toUInt64 % 2 == 0)
          if a % 7 == 0 then break
        return a
      f (value % 7 == 0) == f true

def rangeBoolOuterConditionContinue (count seed : UInt64) : Bool :=
  if seed % 2 == 0 then
      let f := fun x : UInt64 => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value == f seed
  else
      let f := fun x y z : UInt64 => (x + 3 * y + 5 * z) % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 a seed == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value seed 1 == f seed value 1

def rangeBoolOuterConditionStride (count seed : UInt64) : Bool :=
  if seed < count then
      let f := fun (_unit : Unit) (x : UInt64) => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [(f () seed).toNat:count.toNat:3] do
          a := a + i.toUInt64 + 1
          if a % 5 == 0 then break
        return a
      f () value == f () seed
  else
      let f := fun a b c d e : UInt64 => (a + 3*b + 5*c + 7*d + 11*e) % 3
      let value := Id.run do
        let mut a := seed
        for i in [(f seed 1 2 3 4).toNat:count.toNat:3] do
          a := a + i.toUInt64 + 1
          if a % 5 == 0 then break
        return a
      f value 1 2 3 4 == f seed 1 2 3 4

def rangeBoolOuterConditionId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  if Id.run count < seed then
      let f (x : UInt64) : Id (Id UInt64) := pure (pure (x + seed + 1))
      let value : Id UInt64 := Id.run do
        let mut a := Id.run (Id.run (f 0))
        for i in [:(Id.run count).toNat] do
          a := Id.run (Id.run (f (a + i.toUInt64)))
        return a
      pure (Id.run (Id.run (f (Id.run value))) == seed)
  else
      let f (a b c d e : UInt64) : Id (Id UInt64) := pure (pure (a + 3*b + 5*c + 7*d + 11*e + seed))
      let value : Id UInt64 := Id.run do
        let mut a := Id.run (Id.run (f seed 1 2 3 4))
        for i in [:(Id.run count).toNat] do
          a := Id.run (Id.run (f a i.toUInt64 1 2 3))
        return a
      pure (Id.run value == Id.run (Id.run (f seed 1 2 3 4)))

def rangeBoolOuterConditionCapture (count seed : UInt64) : Id Bool :=
  let threshold := seed + count
  let selected := threshold % 5 == 0
  if selected then
      let f := fun flag : Bool => seed + flag.toUInt64
      let g := fun flag : Bool => f (!flag) + f flag
      let value := Id.run do
        let mut a := g false
        for i in [:count.toNat] do
          a := a + g (i.toUInt64 % 3 == 0)
        return a
      pure (value == g (seed == 0))
  else
      let f := fun x : UInt64 => x + seed
      let g := fun x : UInt64 => f (x * 3) + f x
      let value := Id.run do
        let mut a := g 0
        for i in [:count.toNat] do
          a := g (a + i.toUInt64)
        return a
      pure (g value == g seed)

def rangeBoolMixedConditionScalarLeft (count seed : UInt64) : Bool :=
  if seed == 0 then
    true
  else
      let f := fun x : UInt64 => x + seed + 1
      let value := Id.run do
        let mut a := f seed
        for i in [:count.toNat] do
          a := f a + f i.toUInt64
        return a
      f value == f (f seed)

def rangeBoolMixedConditionScalarRight (count seed : UInt64) : Bool :=
  if count < seed then
      let f := fun x y : UInt64 => x + 3 * y + seed % 5 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := f a i.toUInt64
          if a % 7 == 0 then break
        return a
      f value 1 % 7 == 0
  else
    seed % 7 == 0

def rangeBoolMixedConditionFlag (count : UInt64) (flag : Bool) : Bool :=
  if flag then
      let f := fun input : Bool => if flag && input then count + 7 else count - 3
      let value := Id.run do
        let mut a := f flag
        for i in [:count.toNat] do
          a := a + f (i.toUInt64 % 2 == 0)
        return a
      flag && value == f flag
  else
    !flag

def rangeBoolMixedConditionNested (count seed : UInt64) : Bool :=
  if seed < count then
    if seed % 2 == 0 then
      false
    else
        let limit := fun x : UInt64 => x % 17
        let value := Id.run do
          let mut a := seed
          for i in [:(limit count).toNat] do
            a := a + i.toUInt64 + 1
          return a
        value == seed + limit count
  else
    seed == count

def rangeBoolMixedConditionHelper (count seed : UInt64) : Bool :=
  let p := fun x : UInt64 => x % 3 == seed % 3
  if p count then
    p (seed + 1) || p count
  else
      let f := fun x : UInt64 => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value == f seed

def rangeBoolMixedConditionBooleanHelper (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  if p (count % 2 == 0) then
      let f := fun flag : Bool => seed % 5 + flag.toUInt64 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := a + f (i.toUInt64 % 2 == 0)
          if a % 7 == 0 then break
        return a
      f (value % 7 == 0) == f true
  else
    p true

def rangeBoolMixedConditionContinue (count seed : UInt64) : Bool :=
  if seed % 3 == 0 then
    seed == count
  else
      let f := fun x y z : UInt64 => (x + 3 * y + 5 * z) % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 a seed == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value seed 1 == f seed value 1

def rangeBoolMixedConditionStride (count seed : UInt64) : Bool :=
  if count < seed then
      let f := fun (_unit : Unit) (x : UInt64) => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [(f () seed).toNat:count.toNat:3] do
          a := a + i.toUInt64 + 1
          if a % 5 == 0 then break
        return a
      f () value == f () seed
  else
    seed % 5 == 0

def rangeBoolMixedConditionId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  if Id.run count < seed then
    pure (seed == 0)
  else
      let f (a b c d e : UInt64) : Id (Id UInt64) := pure (pure (a + 3*b + 5*c + 7*d + 11*e + seed))
      let value : Id UInt64 := Id.run do
        let mut a := Id.run (Id.run (f seed 1 2 3 4))
        for i in [:(Id.run count).toNat] do
          a := Id.run (Id.run (f a i.toUInt64 1 2 3))
        return a
      pure (Id.run value == Id.run (Id.run (f seed 1 2 3 4)))

def rangeBoolMixedConditionCapture (count seed : UInt64) : Id Bool :=
  let threshold := seed + count
  let selected := threshold % 5 == 0
  if selected then
      let f := fun x : UInt64 => x + seed
      let g := fun x : UInt64 => f (x * 3) + f x
      let value := Id.run do
        let mut a := g 0
        for i in [:count.toNat] do
          a := g (a + i.toUInt64)
        return a
      pure (g value == g seed)
  else
    pure (threshold == seed)

def rangeBoolDirectWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  run (count % 17)

def rangeBoolDirectFlag (count : UInt64) (flag : Bool) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if selected then 1 else 3)
      return a
    selected && value != count
  run (!flag)

def rangeBoolDirectBooleanArgument (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    selected || value % 5 == 0
  run (seed % 2 == 0 && count != 0)

def rangeBoolDirectWordCapture (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x * 3 + seed
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := f seed
      for i in [:limit.toNat] do
        a := f a + i.toUInt64
      return a
    f value == f seed
  run (count % 19)

def rangeBoolDirectBooleanCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    p selected && value != seed
  run (p (count == 0))

def rangeBoolDirectNested (count seed : UInt64) : Bool :=
  let outer := fun selected : Bool =>
    let inner := fun limit : UInt64 =>
      let value := Id.run do
        let mut a := seed
        for i in [:limit.toNat] do
          a := a + i.toUInt64 + (if selected then 1 else 3)
        return a
      selected && value != seed
    inner (count % 17)
  outer (seed % 2 == 0)

def rangeBoolDirectExit (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  run (count % 17)

def rangeBoolDirectContinue (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected && i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  run (seed % 2 == 0)

def rangeBoolDirectStride (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  run (count % 23)

def rangeBoolDirectId (count seed : UInt64) : Id Bool :=
  let run (selected : Id (Id Bool)) : Id (Id Bool) := do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if Id.run (Id.run selected) then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    pure (Id.run (Id.run selected) && value != seed)
  run (pure (pure (seed % 2 == 0)))

def rangeBoolWrappedCallWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  Id.run (run (count % 17))

def rangeBoolWrappedCallFlag (count : UInt64) (flag : Bool) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if selected then 1 else 3)
      return a
    selected && value != count
  Id.run (pure (run (!flag)) : Id Bool)

def rangeBoolWrappedCallBooleanArgument (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    selected || value % 5 == 0
  Id.run (Id.run (pure (pure (run (seed % 2 == 0 && count != 0))) : Id (Id Bool)))

def rangeBoolWrappedCallWordCapture (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x * 3 + seed
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := f seed
      for i in [:limit.toNat] do
        a := f a + i.toUInt64
      return a
    f value == f seed
  Id.run (run (count % 19))

def rangeBoolWrappedCallBooleanCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    p selected && value != seed
  Id.run (pure (run (p (count == 0))) : Id Bool)

def rangeBoolWrappedCallNested (count seed : UInt64) : Bool :=
  let outer := fun selected : Bool =>
    let inner := fun limit : UInt64 =>
      let value := Id.run do
        let mut a := seed
        for i in [:limit.toNat] do
          a := a + i.toUInt64 + (if selected then 1 else 3)
        return a
      selected && value != seed
    Id.run (inner (count % 17))
  Id.run (Id.run (pure (pure (outer (seed % 2 == 0))) : Id (Id Bool)))

def rangeBoolWrappedCallExit (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  Id.run (run (count % 17))

def rangeBoolWrappedCallContinue (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected && i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  Id.run (pure (run (seed % 2 == 0)) : Id Bool)

def rangeBoolWrappedCallStride (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  Id.run (Id.run (pure (pure (run (count % 23))) : Id (Id Bool)))

def rangeBoolWrappedCallId (count seed : UInt64) : Id Bool :=
  let run (selected : Id (Id Bool)) : Id (Id Bool) := do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if Id.run (Id.run selected) then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    pure (Id.run (Id.run selected) && value != seed)
  Id.run (run (pure (pure (seed % 2 == 0))))

def rangeBoolForwardedWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  Id.run do
    let argument ← (pure (count % 17) : Id (UInt64))
    run argument

def rangeBoolForwardedFlag (count : UInt64) (flag : Bool) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if selected then 1 else 3)
      return a
    selected && value != count
  Id.run do
    let argument ← (pure (!flag) : Id (Bool))
    run argument

def rangeBoolForwardedBooleanArgument (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    selected || value % 5 == 0
  Id.run do
    let argument ← (pure (seed % 2 == 0 && count != 0) : Id (Bool))
    run argument

def rangeBoolForwardedWordCapture (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x * 3 + seed
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := f seed
      for i in [:limit.toNat] do
        a := f a + i.toUInt64
      return a
    f value == f seed
  Id.run do
    let argument ← (pure (count % 19) : Id (UInt64))
    run argument

def rangeBoolForwardedBooleanCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    p selected && value != seed
  Id.run do
    let argument ← (pure (p (count == 0)) : Id (Bool))
    run argument

def rangeBoolForwardedNested (count seed : UInt64) : Bool :=
  let outer := fun selected : Bool =>
    let inner := fun limit : UInt64 =>
      let value := Id.run do
        let mut a := seed
        for i in [:limit.toNat] do
          a := a + i.toUInt64 + (if selected then 1 else 3)
        return a
      selected && value != seed
    Id.run do
      let argument ← (pure (count % 17) : Id UInt64)
      inner argument
  Id.run do
    let argument ← (pure (seed % 2 == 0) : Id (Bool))
    outer argument

def rangeBoolForwardedExit (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  Id.run do
    let argument ← (pure (count % 17) : Id (UInt64))
    run argument

def rangeBoolForwardedContinue (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected && i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  Id.run do
    let argument ← (pure (seed % 2 == 0) : Id (Bool))
    run argument

def rangeBoolForwardedStride (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  Id.run do
    let argument ← (pure (count % 23) : Id (UInt64))
    run argument

def rangeBoolForwardedId (count seed : UInt64) : Id Bool :=
  let run (selected : Id (Id Bool)) : Id (Id Bool) := do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if Id.run (Id.run selected) then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    pure (Id.run (Id.run selected) && value != seed)
  Id.run do
    let argument ← (pure (pure (pure (seed % 2 == 0))) : Id (Id (Id Bool)))
    run argument

def rangeBoolConditionalCallSaved (count seed : UInt64) : Id Bool :=
  do
    let flag ← if count == 0 then pure (seed == 0) else pure (seed % 2 == 0)
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if flag then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    return flag && value != seed

def rangeBoolConditionalCallNested (count seed : UInt64) : Id Bool :=
  do
    let flag ← if count == 0 then pure (seed == 0) else if seed % 3 == 0 then pure true else pure (seed % 2 == 0)
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if flag then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    return flag && value != seed

def rangeBoolConditionalCallExit (count seed : UInt64) : Id Bool :=
  do
    let flag ← if count < seed then pure (seed % 2 != 0) else pure (seed % 3 == 0)
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
        if flag && a % 7 == 0 then break
      return a)
    return flag || value == 0

def rangeBoolConditionalCallContinue (count seed : UInt64) : Bool :=
  Id.run do
    let flag ← if count == 0 then pure (seed % 3 == 0) else pure (seed % 2 == 0)
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if flag && i.toUInt64 % 3 == 0 then continue
        a := a + i.toUInt64 + 1
      return a)
    return flag && value == seed

def rangeBoolConditionalCallCapture (count seed : UInt64) : Id Bool :=
  do
    let flag ← if count < seed then pure (seed % 7 == 0) else pure (seed == 0)
    let value ← (do
      let f := fun b : Bool => if b && flag then seed + 7 else seed + 3
      let mut a := f false
      for i in [:count.toNat] do
        a := a + f (i.toUInt64 % 2 == 0)
      return a)
    return flag || value == seed

def rangeBoolConditionalCallHelper (count seed : UInt64) : Id Bool :=
  let p := fun x : UInt64 => x % 3 == seed % 3
  do
    let flag ← if p count then pure (p seed) else pure (p (count + 1))
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if flag then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    return flag && value != seed

def rangeBoolConditionalCallFlag (count : UInt64) (input : Bool) : Id Bool :=
  do
    let flag ← if input then pure (count % 2 == 0) else pure (!input)
    let value ← (do
      let mut a := input.toUInt64
      for i in [:count.toNat] do
        a := a + i.toUInt64 + flag.toUInt64
      return a)
    return flag && value != input.toUInt64

def rangeBoolConditionalCallStride (count seed : UInt64) : Id Bool :=
  do
    let limit ← if seed % 2 == 0 then pure (count % 17) else pure (count % 11)
    let value ← (do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a)
    return value % 7 == 0

def rangeBoolConditionalCallWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  if seed % 2 == 0 then run (count % 17) else run (count % 11)

def rangeBoolConditionalCallId (count seed : UInt64) : Id (Id Bool) :=
  do
    let flag : Id Bool ← if count < seed then pure (pure (seed % 2 == 0)) else pure (pure (seed % 3 == 0))
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
        if Id.run flag && a % 7 == 0 then break
      return a)
    return pure (Id.run flag && value != seed)

def rangeBoolSavedCallWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  show Id Bool from do
    let argument ← (pure (count % 17) : Id (UInt64))
    run argument

def rangeBoolSavedCallFlag (count : UInt64) (flag : Bool) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if selected then 1 else 3)
      return a
    selected && value != count
  show Id Bool from do
    let argument ← (pure (!flag) : Id (Bool))
    run argument

def rangeBoolSavedCallBooleanArgument (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    selected || value % 5 == 0
  show Id Bool from do
    let argument ← (pure (seed % 2 == 0 && count != 0) : Id (Bool))
    run argument

def rangeBoolSavedCallWordCapture (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x * 3 + seed
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := f seed
      for i in [:limit.toNat] do
        a := f a + i.toUInt64
      return a
    f value == f seed
  show Id Bool from do
    let argument ← (pure (count % 19) : Id (UInt64))
    run argument

def rangeBoolSavedCallBooleanCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    p selected && value != seed
  show Id Bool from do
    let argument ← (pure (p (count == 0)) : Id (Bool))
    run argument

def rangeBoolSavedCallNested (count seed : UInt64) : Bool :=
  let outer := fun selected : Bool =>
    let inner := fun limit : UInt64 =>
      let value := Id.run do
        let mut a := seed
        for i in [:limit.toNat] do
          a := a + i.toUInt64 + (if selected then 1 else 3)
        return a
      selected && value != seed
    show Id Bool from do
      let argument ← (pure (count % 17) : Id UInt64)
      inner argument
  show Id Bool from do
    let argument ← (pure (seed % 2 == 0) : Id (Bool))
    outer argument

def rangeBoolSavedCallExit (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  show Id Bool from do
    let argument ← (pure (count % 17) : Id (UInt64))
    run argument

def rangeBoolSavedCallContinue (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected && i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  show Id Bool from do
    let argument ← (pure (seed % 2 == 0) : Id (Bool))
    run argument

def rangeBoolSavedCallStride (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  show Id Bool from do
    let argument ← (pure (count % 23) : Id (UInt64))
    run argument

def rangeBoolSavedCallId (count seed : UInt64) : Id Bool :=
  let run (selected : Id (Id Bool)) : Id (Id Bool) := do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if Id.run (Id.run selected) then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    pure (Id.run (Id.run selected) && value != seed)
  show Id Bool from do
    let argument ← (pure (pure (pure (seed % 2 == 0))) : Id (Id (Id Bool)))
    run argument

def rangeBoolWrappedChoiceWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  Id.run (if count % 2 == 0 then run (count % 17) else run (count % 7))

def rangeBoolWrappedChoiceFlag (count : UInt64) (flag : Bool) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if selected then 1 else 3)
      return a
    selected && value != count
  show Id Bool from if count % 2 == 0 then run (!flag) else run (count % 3 == 0)

def rangeBoolWrappedChoiceBooleanArgument (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    selected || value % 5 == 0
  Id.run (pure (if count % 2 == 0 then run (seed % 2 == 0 && count != 0) else run (count % 3 == 0)) : Id Bool)

def rangeBoolWrappedChoiceWordCapture (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x * 3 + seed
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := f seed
      for i in [:limit.toNat] do
        a := f a + i.toUInt64
      return a
    f value == f seed
  Id.run (if count % 2 == 0 then run (count % 19) else run (count % 7))

def rangeBoolWrappedChoiceBooleanCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    p selected && value != seed
  show Id Bool from if count % 2 == 0 then run (p (count == 0)) else run (count % 3 == 0)

def rangeBoolWrappedChoiceNested (count seed : UInt64) : Bool :=
  let outer := fun selected : Bool =>
    let inner := fun limit : UInt64 =>
      let value := Id.run do
        let mut a := seed
        for i in [:limit.toNat] do
          a := a + i.toUInt64 + (if selected then 1 else 3)
        return a
      selected && value != seed
    inner (count % 17)
  Id.run (pure (if count % 2 == 0 then outer (seed % 2 == 0) else outer (count % 3 == 0)) : Id Bool)

def rangeBoolWrappedChoiceExit (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  Id.run (if count % 2 == 0 then run (count % 17) else run (count % 7))

def rangeBoolWrappedChoiceContinue (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected && i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  show Id Bool from if count % 2 == 0 then run (seed % 2 == 0) else run (count % 3 == 0)

def rangeBoolWrappedChoiceStride (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  Id.run (pure (if count % 2 == 0 then run (count % 23) else run (count % 7)) : Id Bool)

def rangeBoolWrappedChoiceId (count seed : UInt64) : Id Bool :=
  let run (selected : Id (Id Bool)) : Id (Id Bool) := do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if Id.run (Id.run selected) then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    pure (Id.run (Id.run selected) && value != seed)
  Id.run (if count % 2 == 0 then run (pure (pure (seed % 2 == 0))) else run (pure (pure false)))

def rangeBoolResultLet (count seed : UInt64) : Bool :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  !flag

def rangeBoolResultDo (count seed : UInt64) : Id Bool := do
  let flag ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == seed % 7))
  pure (flag && seed != 0)

def rangeBoolResultFlag (count : UInt64) (flag : Bool) : Bool :=
  let selected :=
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if flag then 1 else 3)
      return a
    value != count
  selected != flag

def rangeBoolResultCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p (i.toUInt64 == 0) then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    value != seed
  p (!flag)

def rangeBoolResultSaved (count seed : UInt64) : Bool :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == 0
  let saved := !flag
  saved || seed == 0

def rangeBoolResultMixed (count seed : UInt64) : Bool :=
  let flag := if seed == 0 then count == 0 else
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == 0
  !flag && count != 0

def rangeBoolResultExit (count seed : UInt64) : Bool :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  flag || count == 0

def rangeBoolResultContinue (count seed : UInt64) : Id Bool := do
  let flag ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == seed % 7))
  pure (!flag || seed == 0)

def rangeBoolResultStride (count seed : UInt64) : Bool :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:count.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  !flag

def rangeBoolResultId (count seed : UInt64) : Id (Id Bool) := do
  let flag : Id (Id Bool) ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (pure (pure (value % 7 == seed % 7))))
  pure (pure (!(Id.run (Id.run flag)) && seed != 0))

def rangeLetBool (count seed : UInt64) : UInt64 :=
  let flag := Id.run do
    let mut a := seed
    for _ in [:count.toNat] do
      a := a + 1
    return a == 0
  if flag then count else seed


def rangeWordFromBoolLet (count seed : UInt64) : UInt64 :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  (if flag then seed + 7 else seed * 3) + count

def rangeWordFromBoolDo (count seed : UInt64) : Id UInt64 := do
  let flag ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == seed % 7))
  pure ((if flag then seed + 7 else seed * 3) + count)

def rangeWordFromBoolFlag (count : UInt64) (flag : Bool) : UInt64 :=
  let selected :=
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if flag then 1 else 3)
      return a
    value != count
  if selected != flag then count + 11 else count * 5

def rangeWordFromBoolHelper (count seed : UInt64) : UInt64 :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value != seed
  let f := fun b : Bool => if b then seed + 7 else count * 3
  f flag + f (!flag)

def rangeWordFromBoolConverted (count seed : UInt64) : UInt64 :=
  (let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
   value % 7 == seed % 7).toUInt64

def rangeWordFromBoolMixed (count seed : UInt64) : UInt64 :=
  let flag := if seed == 0 then count == 0 else
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == 0
  if !flag && count != 0 then seed + 7 else seed * 3

def rangeWordFromBoolExit (count seed : UInt64) : UInt64 :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  if flag || count == 0 then seed + 5 else seed * 7

def rangeWordFromBoolContinue (count seed : UInt64) : Id UInt64 := do
  let flag ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == seed % 7))
  pure ((if !flag || seed == 0 then seed + 11 else seed * 3) + count)

def rangeWordFromBoolStride (count seed : UInt64) : UInt64 :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:count.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  flag.toUInt64 * 23 + seed

def rangeWordFromBoolId (count seed : UInt64) : Id (Id UInt64) := do
  let flag : Id (Id Bool) ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (pure (pure (value % 7 == seed % 7))))
  pure (pure ((if !(Id.run (Id.run flag)) && seed != 0 then seed + 7 else seed * 3) + count))

def rangeWordBoolSetupWord (count seed : UInt64) : UInt64 :=
  let limit := count % 17
  let initial := seed + 7
  let flag :=
    let value := Id.run do
      let mut a := initial
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == initial % 7
  (if flag then initial + 7 else initial * 3) + limit

def rangeWordBoolSetupFlag (count seed : UInt64) : UInt64 :=
  let selected := seed % 3 == 0
  let initial := if selected then seed + 7 else seed * 3
  let flag :=
    let value := Id.run do
      let mut a := initial
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == initial % 7
  (if flag then initial + 7 else initial * 3) + count

def rangeWordBoolSetupDo (count seed : UInt64) : Id UInt64 :=
do
  let limit ← pure (count % 17)
  let initial ← pure (seed + 7)
  let flag ← (do
    let value ← (do
      let mut a := initial
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == initial % 7))
  pure ((if flag then initial + 7 else initial * 3) + limit)

def rangeWordBoolSetupNested (count seed : UInt64) : Id UInt64 :=
do
  let selected ← pure (seed % 3 == 0)
  let limit := count % 17
  let initial ← pure (if selected then seed + 7 else seed * 3)
  let flag ← (do
    let value ← (do
      let mut a := initial
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == initial % 7))
  pure ((if flag then initial + 7 else initial * 3) + limit)

def rangeWordBoolSavedResult (count seed : UInt64) : UInt64 :=
  let saved :=
    let flag :=
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := a + i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    (if flag then seed + 7 else seed * 3) + count
  saved + seed * 3

def rangeWordBoolShowResult (count seed : UInt64) : Id UInt64 :=
  show Id UInt64 from do
    let flag ← (do
      let value ← (do
        let mut a := seed
        for i in [:count.toNat] do
          a := a + i.toUInt64 + 1
        return a)
      pure (value % 7 == seed % 7))
    pure ((if flag then seed + 7 else seed * 3) + count)

def rangeWordBoolSetupExit (count seed : UInt64) : UInt64 :=
  let limit := count % 23
  let initial := seed + 11
  let flag :=
    let value := Id.run do
      let mut a := initial
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  if flag || limit == 0 then initial + 5 else initial * 7

def rangeWordBoolSetupContinue (count seed : UInt64) : Id UInt64 :=
do
  let selected ← pure (seed % 2 == 0)
  let initial := if selected then seed + 5 else seed * 3
  let flag ← (do
    let value ← (do
      let mut a := initial
      for i in [:count.toNat] do
        if i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == initial % 7))
  pure ((if !flag || initial == 0 then initial + 11 else initial * 3) + count)

def rangeWordBoolSetupStride (count seed : UInt64) : UInt64 :=
  let limit := count % 23
  let initial := seed + 11
  let flag :=
    let value := Id.run do
      let mut a := initial
      for i in [(initial % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  flag.toUInt64 * 23 + initial

def rangeWordBoolSetupId (count seed : UInt64) : Id (Id UInt64) :=
do
  let limit : Id (Id UInt64) ← pure (pure (pure (count % 17)))
  let selected : Id (Id Bool) ← pure (pure (pure (seed % 2 == 0)))
  let initial : Id UInt64 := if Id.run (Id.run selected) then seed + 7 else seed * 3
  let stop := Id.run (Id.run limit)
  let start := Id.run initial
  let flag : Id (Id Bool) ← (do
    let value ← (do
      let mut a := start
      for i in [:stop.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (pure (pure (value % 7 == start % 7))))
  pure (pure ((if !(Id.run (Id.run flag)) && start != 0 then start + 7 else start * 3) + stop))

def rangeWordBoolHelperWord (count seed : UInt64) : UInt64 :=
  let bump : UInt64 → UInt64 := fun x => x + seed % 7
  let flag :=
    let value := Id.run do
      let mut a := bump seed
      for i in [:(bump count % 17).toNat] do
        a := a + bump i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  if flag then bump count else bump seed * 3

def rangeWordBoolHelperBoolean (count seed : UInt64) : UInt64 :=
  let select : Bool → UInt64 := fun b => if b then seed + 7 else seed * 3
  let flag :=
    let value := Id.run do
      let mut a := select (seed % 2 == 0)
      for i in [:count.toNat] do
        if i.toUInt64 % 2 == 0 then continue
        a := a + select (i.toUInt64 % 3 == 0)
      return a
    value % 7 == seed % 7
  select flag + count

def rangeWordBoolHelperPredicate (count seed : UInt64) : UInt64 :=
  let pred : UInt64 → Bool := fun x => x % 7 == seed % 7
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
        if pred a then break
      return a
    pred value
  if flag then seed + count else seed * 3

def rangeWordBoolHelperBooleanPredicate (count seed : UInt64) : UInt64 :=
  let selected := seed % 3 == 0
  let flip : Bool → Bool := fun b => b != selected
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if flip (i.toUInt64 % 2 == 0) then a := a + i.toUInt64 + 1
      return a
    flip (value % 7 == seed % 7)
  if flag then seed + count else seed * 3

def rangeWordBoolHelperBinary (count seed : UInt64) : UInt64 :=
  let combine : UInt64 → UInt64 → UInt64 := fun x y => x * 3 + y + seed
  let flag :=
    let value := Id.run do
      let mut a := combine seed 1
      for i in [:(combine count 2 % 17).toNat] do
        a := combine a i.toUInt64
      return a
    value % 7 == seed % 7
  if flag then combine count seed else combine seed count

def rangeWordBoolHelperMany (count seed : UInt64) : UInt64 :=
  let combine : UInt64 → UInt64 → UInt64 → UInt64 := fun x y z => x * 3 + y * 5 + z + seed
  let flag :=
    let value := Id.run do
      let mut a := combine seed 1 2
      for i in [:(combine count 2 3 % 17).toNat] do
        a := combine a i.toUInt64 7
      return a
    value % 7 == seed % 7
  if flag then combine count seed 11 else combine seed count 13

def rangeWordBoolHelperManyFive (count seed : UInt64) : Id UInt64 := do
  let combine : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 :=
    fun a b c d e => a * 3 + b * 5 + c * 7 + d * 11 + e + seed
  let flag ← (do
    let value ← (do
      let mut a := combine seed 1 2 3 4
      for i in [:(combine count 2 3 4 5 % 17).toNat] do
        a := combine a i.toUInt64 7 11 13
      return a)
    pure (value % 7 == seed % 7))
  pure (if flag then combine count seed 11 13 17 else combine seed count 13 17 19)

def rangeWordBoolHelperUnit (count seed : UInt64) : UInt64 :=
  let bump : Unit → UInt64 → UInt64 := fun _ x => x + seed % 7
  let flag :=
    let value := Id.run do
      let mut a := bump () seed
      for i in [:(bump () count % 17).toNat] do
        a := a + bump () i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  if flag then bump () count else bump () seed * 3

def rangeWordBoolHelperPunit (count seed : UInt64) : UInt64 :=
  let bump : PUnit.{1} → UInt64 → UInt64 := fun _ x => x + seed % 7
  let flag :=
    let value := Id.run do
      let mut a := bump PUnit.unit seed
      for i in [:count.toNat:2] do
        a := a + bump PUnit.unit i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  if flag then bump PUnit.unit count else bump PUnit.unit seed * 3

def rangeWordBoolHelperId (count seed : UInt64) : Id UInt64 := do
  let bump : Id (Id UInt64) → Id UInt64 := fun x => Id.run (Id.run x) + seed % 7
  let flip : Id (Id Bool) → Id Bool := fun b => !(Id.run (Id.run b))
  let flag ← (do
    let value ← (do
      let mut a := Id.run (bump seed)
      for i in [:count.toNat] do
        a := a + Id.run (bump i.toUInt64) + 1
      return a)
    pure (Id.run (flip (value % 7 == seed % 7))))
  pure (if flag then Id.run (bump count) else Id.run (bump seed) * 3)

def rangeWordChooseLoops (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then Id.run do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64 + 1
    return a
  else Id.run do
    let mut a := seed + 7
    for i in [:count.toNat] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseScalarLeft (count seed : UInt64) : UInt64 :=
  if seed < count then seed * 7 + count else Id.run do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64 + 1
    return a

def rangeWordChooseScalarRight (count seed : UInt64) : UInt64 :=
  if seed % 3 == 0 then Id.run do
    let mut a := seed + 7
    for i in [:count.toNat] do a := a * 3 + i.toUInt64
    return a
  else seed * 7 + count

def rangeWordChooseNested (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then
    if count % 3 == 0 then Id.run do
      let mut a := seed
      for i in [:count.toNat] do a := a + i.toUInt64 + 1
      return a
    else seed + count * 3
  else
    if seed < count then seed * 7 else Id.run do
      let mut a := seed + 7
      for i in [:count.toNat] do a := a * 3 + i.toUInt64
      return a

def rangeWordChooseBooleanLoop (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do a := a + i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then seed + count else seed * 3
  else Id.run do
    let mut a := seed + 7
    for i in [:count.toNat] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseExit (count seed : UInt64) : UInt64 :=
  if seed % 3 == 0 then Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a
  else Id.run do
    let mut a := seed + 7
    for i in [:count.toNat] do
      a := a * 3 + i.toUInt64
      if a % 11 == 0 then break
    return a

def rangeWordChooseContinue (count seed : UInt64) : Id UInt64 := do
  if seed % 2 == 0 then
    let mut a := seed
    for i in [:count.toNat] do
      if i.toUInt64 % 2 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  else
    let mut a := seed + 7
    for i in [:count.toNat] do
      if i.toUInt64 % 3 == 0 then continue
      a := a * 3 + i.toUInt64
    return a

def rangeWordChooseStride (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then Id.run do
    let mut a := seed
    for i in [1:count.toNat:3] do a := a + i.toUInt64 + 1
    return a
  else Id.run do
    let mut a := seed + 7
    for i in [2:count.toNat:5] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseHelpers (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then
    let bump : UInt64 → UInt64 := fun x => x + seed % 7
    let flag :=
      let value := Id.run do
        let mut a := bump seed
        for i in [:count.toNat] do a := a + bump i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then bump count else bump seed * 3
  else
    let combine : UInt64 → UInt64 → UInt64 := fun x y => x * 3 + y + seed
    Id.run do
      let mut a := combine seed 1
      for i in [:count.toNat] do a := combine a i.toUInt64
      return a

def rangeWordChooseId (count seed : UInt64) : Id (Id UInt64) :=
  Id.run (pure (if seed % 2 == 0 then (Id.run do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64 + 1
    return a) else seed * 7 + count) : Id (Id UInt64))

def rangeWordChooseSetupWord (count seed : UInt64) : UInt64 :=
  let limit := count % 17
  let initial := seed + 7
  if initial % 3 == 0 then Id.run do
    let mut a := initial
    for i in [:limit.toNat] do a := a + i.toUInt64 + 1
    return a
  else initial * 3 + limit

def rangeWordChooseSetupFlag (count seed : UInt64) : UInt64 :=
  let selected := seed % 3 == 0
  let initial := if selected then seed + 7 else seed * 3
  if selected then Id.run do
    let mut a := initial
    for i in [:count.toNat] do a := a + i.toUInt64 + 1
    return a
  else Id.run do
    let mut a := initial + 11
    for i in [:count.toNat] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseSetupDo (count seed : UInt64) : Id UInt64 := do
  let limit ← pure (count % 17)
  let initial ← pure (seed + 7)
  if initial % 3 == 0 then
    let mut a := initial
    for i in [:limit.toNat] do a := a + i.toUInt64 + 1
    return a
  else pure (initial * 3 + limit)

def rangeWordChooseSetupNested (count seed : UInt64) : Id UInt64 := do
  let selected ← pure (seed % 3 == 0)
  let limit := count % 17
  let initial ← pure (if selected then seed + 7 else seed * 3)
  if selected then
    let mut a := initial
    for i in [:limit.toNat] do a := a + i.toUInt64 + 1
    return a
  else if limit < 7 then pure (initial + 11) else
    let mut a := initial + 11
    for i in [:limit.toNat] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseSavedResult (count seed : UInt64) : UInt64 :=
  let saved :=
    if seed % 2 == 0 then Id.run do
      let mut a := seed
      for i in [:count.toNat] do a := a + i.toUInt64 + 1
      return a
    else seed * 3 + count
  let again := saved + seed * 3
  again * 7 + saved

def rangeWordChooseShowResult (count seed : UInt64) : Id UInt64 :=
  show Id UInt64 from do
    let saved ← (if seed % 2 == 0 then (do
      let mut a := seed
      for i in [:count.toNat] do a := a + i.toUInt64 + 1
      return a) else pure (seed * 3 + count))
    pure (saved * 7 + seed)

def rangeWordChooseSetupExit (count seed : UInt64) : UInt64 :=
  let limit := count % 23
  let initial := seed + 11
  let saved := if initial % 3 == 0 then Id.run do
      let mut a := initial
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    else initial * 7
  if saved % 5 == 0 then saved + limit else saved * 3

def rangeWordChooseSetupContinue (count seed : UInt64) : Id UInt64 := do
  let selected ← pure (seed % 2 == 0)
  let initial := if selected then seed + 5 else seed * 3
  let saved ← (if selected then (do
    let mut a := initial
    for i in [:count.toNat] do
      if i.toUInt64 % 2 == 0 then continue
      a := a + i.toUInt64 + 1
    return a) else pure (initial + 11))
  pure (saved + count)

def rangeWordChooseSetupStride (count seed : UInt64) : UInt64 :=
  let initial := seed + 11
  let saved := if initial % 2 == 0 then Id.run do
      let mut a := initial
      for i in [1:count.toNat:3] do a := a + i.toUInt64 + 1
      return a
    else Id.run do
      let mut a := initial + 7
      for i in [2:count.toNat:5] do a := a * 3 + i.toUInt64
      return a
  saved + initial

def rangeWordChooseSetupId (count seed : UInt64) : Id (Id UInt64) := do
  let limit : Id (Id UInt64) ← pure (count % 17)
  let selected : Id (Id Bool) ← pure (seed % 2 == 0)
  let stop := Id.run (Id.run limit)
  let flag := Id.run (Id.run selected)
  let saved : Id (Id UInt64) ← (if flag then (do
    let mut a := seed
    for i in [:stop.toNat] do a := a + i.toUInt64 + 1
    return a) else pure (seed * 3))
  pure (Id.run (Id.run saved) + stop)

def rangeWordChooseHelperWord (count seed : UInt64) : UInt64 :=
  let bump : UInt64 → UInt64 := fun x => x + seed % 7
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := bump seed
        for i in [:(bump count % 17).toNat] do
          a := a + bump i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then bump count else bump seed * 3
  else seed * 13 + count

def rangeWordChooseHelperBoolean (count seed : UInt64) : UInt64 :=
  let select : Bool → UInt64 := fun b => if b then seed + 7 else seed * 3
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := select (seed % 2 == 0)
        for i in [:count.toNat] do
          if i.toUInt64 % 2 == 0 then continue
          a := a + select (i.toUInt64 % 3 == 0)
        return a
      value % 7 == seed % 7
    select flag + count
  else seed * 13 + count

def rangeWordChooseHelperPredicate (count seed : UInt64) : UInt64 :=
  let pred : UInt64 → Bool := fun x => x % 7 == seed % 7
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := a + i.toUInt64 + 1
          if pred a then break
        return a
      pred value
    if flag then seed + count else seed * 3
  else seed * 13 + count

def rangeWordChooseHelperBooleanPredicate (count seed : UInt64) : UInt64 :=
  let selected := seed % 3 == 0
  let flip : Bool → Bool := fun b => b != selected
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if flip (i.toUInt64 % 2 == 0) then a := a + i.toUInt64 + 1
        return a
      flip (value % 7 == seed % 7)
    if flag then seed + count else seed * 3
  else seed * 13 + count

def rangeWordChooseHelperBinary (count seed : UInt64) : UInt64 :=
  let combine : UInt64 → UInt64 → UInt64 := fun x y => x * 3 + y + seed
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := combine seed 1
        for i in [:(combine count 2 % 17).toNat] do
          a := combine a i.toUInt64
        return a
      value % 7 == seed % 7
    if flag then combine count seed else combine seed count
  else seed * 13 + count

def rangeWordChooseHelperMany (count seed : UInt64) : UInt64 :=
  let combine : UInt64 → UInt64 → UInt64 → UInt64 := fun x y z => x * 3 + y * 5 + z + seed
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := combine seed 1 2
        for i in [:(combine count 2 3 % 17).toNat] do
          a := combine a i.toUInt64 7
        return a
      value % 7 == seed % 7
    if flag then combine count seed 11 else combine seed count 13
  else seed * 13 + count

def rangeWordChooseHelperManyFive (count seed : UInt64) : Id UInt64 := do
  let combine : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 :=
    fun a b c d e => a * 3 + b * 5 + c * 7 + d * 11 + e + seed
  if seed % 2 == 0 then
    let flag ← (do
      let value ← (do
        let mut a := combine seed 1 2 3 4
        for i in [:(combine count 2 3 4 5 % 17).toNat] do
          a := combine a i.toUInt64 7 11 13
        return a)
      pure (value % 7 == seed % 7))
    pure (if flag then combine count seed 11 13 17 else combine seed count 13 17 19)
  else pure (seed * 13 + count)

def rangeWordChooseHelperUnit (count seed : UInt64) : UInt64 :=
  let bump : Unit → UInt64 → UInt64 := fun _ x => x + seed % 7
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := bump () seed
        for i in [:(bump () count % 17).toNat] do
          a := a + bump () i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then bump () count else bump () seed * 3
  else seed * 13 + count

def rangeWordChooseHelperPunit (count seed : UInt64) : UInt64 :=
  let bump : PUnit.{1} → UInt64 → UInt64 := fun _ x => x + seed % 7
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := bump PUnit.unit seed
        for i in [:count.toNat:2] do
          a := a + bump PUnit.unit i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then bump PUnit.unit count else bump PUnit.unit seed * 3
  else seed * 13 + count

def rangeWordChooseHelperId (count seed : UInt64) : Id UInt64 := do
  let bump : Id (Id UInt64) → Id UInt64 := fun x => Id.run (Id.run x) + seed % 7
  let flip : Id (Id Bool) → Id Bool := fun b => !(Id.run (Id.run b))
  if seed % 2 == 0 then
    let flag ← (do
      let value ← (do
        let mut a := Id.run (bump seed)
        for i in [:count.toNat] do
          a := a + Id.run (bump i.toUInt64) + 1
        return a)
      pure (Id.run (flip (value % 7 == seed % 7))))
    pure (if flag then Id.run (bump count) else Id.run (bump seed) * 3)
  else pure (seed * 13 + count)

def rangeBoolLetIdWord (count seed : UInt64) : Bool :=
  let start : Id UInt64 := seed + 7
  let value := Id.run do
    let mut a := Id.run start
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == Id.run start

def rangeBoolLetIdWordLayers (count seed : UInt64) : Bool :=
  let start : Id (Id UInt64) := pure (pure (seed + 1))
  let stop : Id UInt64 := count % 17
  let value := Id.run do
    let mut a := Id.run (Id.run start)
    for i in [:(Id.run stop).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value != Id.run (Id.run start)

def rangeBoolLetIdFlag (count seed : UInt64) : Bool :=
  let flag : Id Bool := seed % 3 == 0
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + (Id.run flag).toUInt64
    return a
  Id.run flag && value == seed

def rangeBoolLetIdFlagLayers (count seed : UInt64) : Bool :=
  let flag : Id (Id Bool) := pure (pure (seed % 2 == 0))
  let start : Id UInt64 := seed + (Id.run (Id.run flag)).toUInt64
  let value := Id.run do
    let mut a := Id.run start
    for i in [:count.toNat] do
      if Id.run (Id.run flag) && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  Id.run (Id.run flag) || value == Id.run start

def rangeBoolLetIdResult (count seed : UInt64) : Bool :=
  let value : Id UInt64 := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
  Id.run value == seed

def rangeBoolLetIdResultLayers (count seed : UInt64) : Id Bool :=
  let value : Id (Id UInt64) := pure (pure (Id.run do
    let mut a := seed
    for i in [1:count.toNat:3] do
      a := a + i.toUInt64
      if a % 7 == 0 then break
    return a))
  pure (Id.run (Id.run value) % 7 == 0)

def rangeBoolLetIdMixed (count seed : UInt64) : Bool :=
  let start : Id UInt64 := seed + 3
  let flag : Id Bool := Id.run start % 2 == 0
  let value : Id UInt64 := Id.run do
    let mut a := Id.run start
    for i in [:count.toNat] do
      a := a + i.toUInt64 + (Id.run flag).toUInt64
    return a
  Id.run flag && Id.run value != Id.run start

def rangeBoolLetIdExit (count seed : UInt64) : Bool :=
  let flag : Id Bool := seed != 0
  let value : Id (Id UInt64) := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if Id.run flag && a % 7 == 0 then break
    return a
  Id.run flag || Id.run (Id.run value) == seed

def rangeBoolLetIdContinue (count seed : UInt64) : Bool := Id.run (
  let flag : Id Bool := seed % 3 == 0
  let value : Id UInt64 := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if Id.run flag && i.toUInt64 % 2 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  pure (Id.run flag && Id.run value == seed))

def rangeBoolLetIdInput (count : Id UInt64) (input : Id Bool) : Id (Id Bool) :=
  let flag : Id (Id Bool) := pure (pure (!Id.run input))
  let start : Id UInt64 := (Id.run input).toUInt64
  let value : Id (Id UInt64) := Id.run do
    let mut a := Id.run start
    for i in [:(Id.run count).toNat] do
      a := a + i.toUInt64 + 1
      if Id.run (Id.run flag) && a % 7 == 0 then break
    return a
  pure (pure (Id.run (Id.run flag) && Id.run (Id.run value) == Id.run start))

def rangeBoolFlagSetupLet (count seed : UInt64) : Bool :=
  let flag := seed % 3 == 0
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + flag.toUInt64
    return a
  flag && value == seed

def rangeBoolFlagSetupChain (count seed : UInt64) : Bool :=
  let first := seed % 3 == 0
  let second := !first || count == 0
  let start := seed + second.toUInt64
  let value := Id.run do
    let mut a := start
    for i in [:count.toNat] do
      a := a + i.toUInt64 + first.toUInt64
    return a
  second && value == start

def rangeBoolFlagSetupBind (count seed : UInt64) : Id Bool := do
  let flag ← pure (seed != 0)
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + flag.toUInt64
    return a)
  return flag || value == seed

def rangeBoolFlagSetupCondition (count seed : UInt64) : Id Bool := do
  let flag ← pure (if count == 0 then seed == 0 else seed % 2 == 0)
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if flag then a := a + i.toUInt64 + 1 else a := a + 3
    return a)
  return flag && value != seed

def rangeBoolFlagSetupExit (count seed : UInt64) : Id Bool := do
  let flag ← pure (seed % 2 != 0)
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if flag && a % 7 == 0 then break
    return a)
  return flag || value == 0

def rangeBoolFlagSetupContinue (count seed : UInt64) : Bool := Id.run do
  let flag := seed % 3 == 0
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a)
  return flag && value == seed

def rangeBoolFlagSetupStride (count seed : UInt64) : Bool :=
  let flag := seed % 2 == 0
  let value := Id.run do
    let mut a := seed
    for i in [1:count.toNat:3] do
      a := a + i.toUInt64 + flag.toUInt64
      if a % 5 == 0 then break
    return a
  flag && decide (value ≤ seed)

def rangeBoolFlagSetupCapture (count seed : UInt64) : Id Bool := do
  let flag ← pure (seed % 7 == 0)
  let value ← (do
    let f := fun b : Bool => if b && flag then seed + 7 else seed + 3
    let mut a := f false
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a)
  return flag || value == seed

def rangeBoolFlagSetupInput (count : UInt64) (input : Bool) : Bool :=
  let flag := !input || count == 0
  let value := Id.run do
    let mut a := input.toUInt64
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  flag && value == input.toUInt64

def rangeBoolFlagSetupId (count : UInt64) (input : Id Bool) : Id (Id Bool) := do
  let flag : Id Bool ← pure (pure (!Id.run input || count == 0))
  let value ← (do
    let mut a := (Id.run input).toUInt64
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if Id.run flag && a % 7 == 0 then break
    return a)
  return pure (Id.run flag && value == (Id.run input).toUInt64)

def rangeBoolWordSetupLet (count seed : UInt64) : Bool :=
  let start := seed + 7
  let value := Id.run do
    let mut a := start
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == start

def rangeBoolWordSetupChain (count seed : UInt64) : Bool :=
  let start := seed + 7
  let stop := count % 17
  let delta := seed % 5 + 1
  let value := Id.run do
    let mut a := start
    for i in [:stop.toNat] do
      a := a + i.toUInt64 + delta
    return a
  value == start || value == seed

def rangeBoolWordSetupBind (count seed : UInt64) : Id Bool := do
  let start ← pure (seed + 3)
  let stop ← pure (count % 17)
  let value ← (do
    let mut a := start
    for i in [:stop.toNat] do
      a := a + i.toUInt64 + 1
    return a)
  return value != start

def rangeBoolWordSetupCount (count seed : UInt64) : Bool :=
  let stop := count % 17
  let value := Id.run do
    let mut a := seed
    for i in [:stop.toNat] do
      a := a + i.toUInt64 + stop
    return a
  value == seed + stop

def rangeBoolWordSetupExit (count seed : UInt64) : Id Bool := do
  let delta ← pure (seed % 7 + 1)
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + delta
      if a % 7 == 0 then break
    return a)
  return value % 7 == 0

def rangeBoolWordSetupContinue (count seed : UInt64) : Bool := Id.run do
  let offset := seed % 3
  let start := seed + offset
  let value ← (do
    let mut a := start
    for i in [:count.toNat] do
      if i.toUInt64 % 3 == offset then continue
      a := a + i.toUInt64 + 1
    return a)
  return value == start

def rangeBoolWordSetupStride (count seed : UInt64) : Bool :=
  let start := seed % 3
  let value := Id.run do
    let mut a := seed
    for i in [start.toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  decide (value ≤ seed)

def rangeBoolWordSetupCapture (count seed : UInt64) : Id Bool := do
  let captured ← pure (seed + 7)
  let value ← (do
    let f := fun x : UInt64 => x + captured
    let mut a := f seed
    for i in [:count.toNat] do
      a := f (a + i.toUInt64)
    return a)
  return value == captured || value == seed

def rangeBoolWordSetupFlag (count : UInt64) (flag : Bool) : Bool :=
  let start := count + flag.toUInt64
  let value := Id.run do
    let mut a := start
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  flag && value != start

def rangeBoolWordSetupId (count : Id UInt64) (seed : UInt64) : Id (Id Bool) := do
  let start : Id UInt64 ← pure (pure (seed + 1))
  let value ← (do
    let mut a := Id.run start
    for i in [:(Id.run count).toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a)
  return pure (value == Id.run start)

def rangeBoolResultBindYield (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a)
  return value == seed

def rangeBoolResultBindExit (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a)
  return value % 7 == 0

def rangeBoolResultBindContinue (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64
    return a)
  return value != seed && value != 0

def rangeBoolResultBindStride (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [1:count.toNat:3] do
      a := a + i.toUInt64
      if a % 5 == 0 then break
    return a)
  return decide (value ≤ seed)

def rangeBoolResultBindStepHelper (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      let f := fun x : UInt64 => x + i.toUInt64 + seed
      a := f a
      if a % 11 == 0 then break
    return a)
  return value == 0 || value == seed

def rangeBoolResultBindCapture (count seed : UInt64) : Id Bool := do
  let value ← (do
    let f := fun b : Bool => if b then seed + 7 else seed + 3
    let mut a := f false
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a)
  return value == seed || value == seed + 3

def rangeBoolResultBindFlag (count : UInt64) (flag : Bool) : Id Bool := do
  let value ← (do
    let mut a := flag.toUInt64
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a)
  return flag && value != 0

def rangeBoolResultBindIdInputs (count : Id UInt64) (flag : Id Bool) : Id Bool := do
  let value ← (do
    let mut a := (Id.run flag).toUInt64
    for i in [:(Id.run count).toNat] do
      a := a + i.toUInt64 + 1
      if Id.run flag && a % 7 == 0 then break
    return a)
  return Id.run flag || value == 0

def rangeBoolResultBindIdAction (count seed : UInt64) : Id Bool := do
  let value : Id UInt64 ← pure (Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a)
  return Id.run value != seed

def rangeBoolResultBindNestedResult (count seed : UInt64) : Id (Id Bool) := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if i.toUInt64 % 2 == 0 then continue
      a := a + i.toUInt64 + 1
    return a)
  return pure (value == seed)

def rangeBoolYield (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed

def rangeBoolExit (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a
  value % 7 == 0

def rangeBoolContinue (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64
    return a
  value != seed && value != 0

def rangeBoolStride (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [1:count.toNat:3] do
      a := a + i.toUInt64
      if a % 5 == 0 then break
    return a
  decide (value ≤ seed)

def rangeBoolStepHelper (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      let f := fun x : UInt64 => x + i.toUInt64 + seed
      a := f a
      if a % 11 == 0 then break
    return a
  value == 0 || value == seed

def rangeBoolCapture (count seed : UInt64) : Bool :=
  let value := Id.run do
    let f := fun b : Bool => if b then seed + 7 else seed + 3
    let mut a := f false
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a
  let f := fun x : UInt64 => x == seed
  f value

def rangeBoolFlag (count : UInt64) (flag : Bool) : Bool :=
  let value := Id.run do
    let mut a := flag.toUInt64
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  flag && value != 0

def rangeBoolIdInputs (count : Id UInt64) (flag : Id Bool) : Bool :=
  let value := Id.run do
    let mut a := (Id.run flag).toUInt64
    for i in [:(Id.run count).toNat] do
      a := a + i.toUInt64 + 1
      if Id.run flag && a % 7 == 0 then break
    return a
  Id.run flag || value == 0

def rangeBoolPure (count seed : UInt64) : Id Bool :=
  pure (
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value != seed)

def rangeBoolRun (count seed : UInt64) : Bool := Id.run (
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  pure (value == seed))

def publicInputIdWord (x : Id UInt64) (y : UInt64) : UInt64 := Id.run x + y

def publicInputIdFlag (flag : Id Bool) (x : UInt64) : UInt64 :=
  if Id.run flag then x + 7 else x - 3

def publicInputIdBoth (flag : Id (Id Bool)) (x : Id (Id UInt64)) : Id UInt64 :=
  pure (Id.run (Id.run x) + (Id.run (Id.run flag)).toUInt64)

def publicInputIdResult (x : Id UInt64) (flag : Id Bool) : Bool :=
  Id.run flag && Id.run x != 0

def publicInputIdCapture (flag : Id Bool) (x : Id UInt64) : Bool :=
  let f := fun b : Bool => b && Id.run flag && Id.run x != 0
  f (Id.run flag)

def publicInputIdBind (flag : Id Bool) (x : Id UInt64) : Id Bool := do
  let saved ← flag
  let n ← x
  return saved && n != 0

def rangeInputIdYield (count : Id UInt64) (flag : Id Bool) : UInt64 := Id.run do
  let mut a := (Id.run flag).toUInt64
  for i in [:(Id.run count).toNat] do
    a := a + i.toUInt64 + (Id.run flag).toUInt64
  return a

def rangeInputIdExit (count : Id (Id UInt64)) (flag : Id (Id Bool)) : Id UInt64 := do
  let mut a : UInt64 := 1
  for i in [:(Id.run (Id.run count)).toNat] do
    a := a + i.toUInt64 + 1
    if Id.run (Id.run flag) && a % 7 == 0 then break
  return a

def rangeInputIdContinue (count : Id UInt64) (flag : Id Bool) : UInt64 := Id.run do
  let saved ← flag
  let mut a := Id.run count
  for i in [:(Id.run count).toNat] do
    if saved && i.toUInt64 % 3 == 0 then continue
    a := a + i.toUInt64 + saved.toUInt64
  return a

def rangeInputIdCapture (count : Id UInt64) (flag : Id Bool) : UInt64 := Id.run do
  let f := fun b : Bool => if b then Id.run count + (Id.run flag).toUInt64 else Id.run count
  let mut a := f false
  for i in [:(Id.run count).toNat] do
    a := a + f (i.toUInt64 % 2 == 0)
    if a % 11 == 0 then break
  return a

def rangeFlagYield (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let mut a := flag.toUInt64
  for i in [:count.toNat] do
    a := a + i.toUInt64 + flag.toUInt64
  return a

def rangeFlagExit (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let mut a : UInt64 := 1
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if flag && a % 7 == 0 then break
  return a

def rangeFlagContinue (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let mut a := count
  for i in [:count.toNat] do
    if flag && i.toUInt64 % 3 == 0 then continue
    a := a + i.toUInt64 + 1
  return a

def rangeFlagsBoth (left right : Bool) : UInt64 := Id.run do
  let n : UInt64 := if left then 7 else 3
  let mut a := right.toUInt64
  for i in [:n.toNat] do
    a := a + i.toUInt64 + left.toUInt64
    if right && a % 5 == 0 then break
  return a

def rangeFlagOuter (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let f := fun b : Bool => if b then count + flag.toUInt64 else count - flag.toUInt64
  let mut a := f false
  for i in [:count.toNat] do
    a := a + f (i.toUInt64 % 2 == 0)
  return a

def rangeFlagStepHelper (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let mut a := count
  for i in [:count.toNat] do
    let f := fun b : Bool => if b then a + flag.toUInt64 else a + i.toUInt64
    a := f flag
    if a % 11 == 0 then break
  return a

def rangeFlagAlias (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let saved := !flag
  let mut a := count + saved.toUInt64
  for i in [:count.toNat] do
    if saved then a := a + i.toUInt64 else a := a + 1
  return a

def rangeFlagBind (count : UInt64) (flag : Bool) : Id UInt64 := do
  let saved ← pure flag
  let mut a := count
  for i in [:count.toNat] do
    if !saved && i.toUInt64 % 2 == 0 then continue
    a := a + i.toUInt64 + saved.toUInt64
  return a

def rangeFlagCount (flag : Bool) (count : UInt64) : UInt64 := Id.run do
  let stop := count % 17 + flag.toUInt64
  let mut a : UInt64 := if flag then 1 else 7
  for i in [:stop.toNat] do
    a := a + i.toUInt64
  return a

def rangeFlagResult (flag : Bool) (count : UInt64) : UInt64 := Id.run do
  let stop := count % 17
  let mut a := count
  for i in [:stop.toNat] do
    a := a + i.toUInt64
    if flag && a % 7 == 0 then break
  return if flag then a + count else a - count

def booleanPropRelationDecision (left right : Bool) : Id (Id Bool) :=
  pure (pure (decide (left = right ∨ ¬ left)))

def booleanPropRelationMixed (left right : Bool) : UInt64 :=
  if left ≠ right ∧ left then 7 else 11

def booleanPropRelationNegated (left right : Bool) : Bool :=
  decide (¬ (left = right) ∧ ¬ (left ≠ right ∧ right))

def booleanPropRelationWords (x y : UInt64) : UInt64 :=
  let left := x == y
  let right := x != 0
  if (left ≠ right ∨ x < y) ∧ (right = left ∨ y < x) then x + 7 else y - 3

def booleanPropRelationHelpers (x y : UInt64) : Id Bool := do
  let f := fun b : Bool => b && x != 0
  let g := fun n : UInt64 => n == y
  return decide (f (x == y) = g x ∧ (g y ≠ f false ∨ x < y))

def booleanPropRelationLet (x y : UInt64) : UInt64 :=
  if (let flag := x == y; flag ≠ (x == 0) ∧ x < y) then x + 3 else y + 7

def rangeBoolRelationStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := i.toUInt64 % 3 == 0
    if first = second ∨ ¬ first then a := a + i.toUInt64 + 7 else a := a * 3 + 1
  return a

def rangeBoolRelationExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (a % 2 == 0) ≠ (i.toUInt64 % 3 == 0) ∧ a > 7 then break
  return a

def rangeBoolRelationContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ ((a % 2 == 0) = (i.toUInt64 % 3 == 0)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBoolRelationTail (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a)
  return decide ((value == seed) = (seed == 0) ∨ ¬ (value == 0))

def rangePredicateOuterBodyWord (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f a then a := a + i.toUInt64 + 7 else a := a * 3 + 1
  return a

def rangePredicateOuterBodyBoolean (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (a == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyUnused (count seed : UInt64) : Id UInt64 := do
  let _unused := fun b : Bool => (let g := fun n : UInt64 => n % 3 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a

def rangePredicateOuterBodyBound (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (count == 0))
  let mut a := seed
  for i in [:(count + (f seed).toUInt64).toNat] do
    if f a then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyInitial (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed + (f (seed == 0)).toUInt64
  for i in [:count.toNat] do
    if f (a == seed) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyTail (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 5 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if f a then break
  return a + (f a).toUInt64 + (f seed).toUInt64

def rangePredicateOuterBodyCapture (count seed : UInt64) : Id UInt64 := do
  let p := fun n : UInt64 => n % 5 == 0
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (i.toUInt64 == 0) then continue
    a := a + i.toUInt64 + 1
    if f (a == seed) then break
  return a

def rangePredicateOuterBodyWrapped (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => Id.run do
    let g := fun k : Bool => k || count == seed
    return g b && g (seed == 0)
  let mut a := seed
  for i in [:count.toNat] do
    if _h : f (a % 3 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyNested (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun b : Bool => (let h := fun k : UInt64 => k == n || b; h count && h seed); g (n % 3 == 0) || g (seed == 0))
  let mut a := seed
  for i in [:count.toNat] do
    if f a then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyId (count seed : UInt64) : Id UInt64 := do
  let f := fun n : Id UInt64 => Id.run do
    let g := fun k : UInt64 => k == seed
    return g (Id.run n) || g count
  let mut a := seed
  for i in [:count.toNat] do
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyBreakWord (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 7 == 0; g n || g seed)
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyBreakBoolean (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g a && g seed)
    if f (i.toUInt64 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyContinueWord (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0))
    if f a || f i.toUInt64 then continue
    a := a * 3 + i.toUInt64 + 1
    if f a then break
  return a

def rangePredicateBodyContinueBoolean (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => n % 3 == 0 || b; g a && g seed)
    if f (i.toUInt64 == 0) then continue
    a := a * 3 + i.toUInt64 + 1
    if f (a == seed) then break
  return a

def rangePredicateBodyDependent (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (if _h : n < seed then (let g := fun k : UInt64 => k % 3 == 0; g n || g a) else n == a)
    if _h : f a ≠ f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyCapture (count seed : UInt64) : Id UInt64 := do
  let p := fun n : UInt64 => n % 5 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g a && g seed)
    a := a + i.toUInt64 + 1
    if f (a == seed) then break
  return a

def rangePredicateBodyUnused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := fun b : Bool => (let g := fun n : UInt64 => n % 3 == 0 || b; g a && g seed)
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a

def rangePredicateBodyWrapped (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => Id.run do
      let g := fun k : Bool => k || a == seed
      return g b && g (i.toUInt64 == 0)
    if _h : f (a % 3 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyNested (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun b : Bool => (let h := fun k : UInt64 => k == n || b; h a && h seed); g (n % 3 == 0) || g (i.toUInt64 == 0))
    if f a then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyId (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : Id UInt64 => Id.run do
      let g := fun k : UInt64 => k == seed
      return g (Id.run n) || g a
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def predicateBodyWordRepeated (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0)
  (f x).toUInt64 + (f y).toUInt64 + x

def predicateBodyWordBoolean (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => (let g := fun n : UInt64 => n == y || b; g x && g 0)
  if f (x == 0) then x + 7 else y * 3

def predicateBodyWordUnused (x y : UInt64) : UInt64 :=
  let _unused := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0)
  x + y

def predicateBodyWordCapture (x y : UInt64) : UInt64 :=
  let p := fun n : UInt64 => n == y
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g x && g 0)
  if _h : f (x == 0) ≠ f (y == 0) then x + 3 else y + 11

def predicateBodyWordProposition (x y : UInt64) : UInt64 :=
  if x < y ∧ (let f := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0); f x && f y) then x + 7 else y + 3

def predicateBodyWordDo (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => Id.run do
    let g := fun k : Bool => k || x == y
    return g b && g (y == 0)
  if _h : f (x == 0) then x + y else x - y

def rangePredicateBodyWordStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g a); (f a).toUInt64 + (f i.toUInt64).toUInt64) = 1 then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangePredicateBodyWordExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g a && g seed); (f (i.toUInt64 == 0)).toUInt64) = 1 then break
  return a

def rangePredicateBodyWordContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0)); f a || f i.toUInt64) ∧ a ≤ seed then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangePredicateBodyWordTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (let f := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g a && g 0); (f (a == 0)).toUInt64 + (f (a == seed)).toUInt64) + a

def booleanHelperBodyNested (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 =>
    let g := fun k : UInt64 => k == y
    g n || g 0
   f x && f y).toUInt64 + x

def booleanHelperBodyWrapped (x y : UInt64) : UInt64 :=
  (let f := fun b : Bool => Id.run do
    let g := fun k : Bool => k || x == y
    return g b && g (y == 0)
   f (x == 0) || f (x == y)).toUInt64 + y

def booleanHelperBodyMixed (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 =>
    let g := fun b : Bool => b || n == y
    g (n == 0) && g (y == 0)
   f x || f (x + y)).toUInt64 + x

def booleanHelperBodyCaptures (x y : UInt64) : UInt64 :=
  (let p := fun n : UInt64 => n == y
   let f := fun b : Bool =>
    let g := fun n : UInt64 => p n || b
    g x && g 0
   f (x == 0) || f (y == 0)).toUInt64 + y

def booleanHelperBodyUnused (x y : UInt64) : UInt64 :=
  (let _unused := fun n : UInt64 =>
    let g := fun k : UInt64 => k == y
    g n || g 0
   x == y).toUInt64 + x

def booleanHelperBodyChoice (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 =>
    if _h : n < y then (let g := fun k : UInt64 => k % 3 == 0; g n || g y)
    else (let g := fun b : Bool => !b || y == 0; g (n == 0) && g (n == y))
   f x && f y).toUInt64 + x

def rangeHelperBodyStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g a); f a && f i.toUInt64) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperBodyExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g a && g seed); f (i.toUInt64 == 0) || f (a == seed)) then break
  return a

def rangeHelperBodyContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0)); f a || f i.toUInt64) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperBodyTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (let f := fun b : Bool => Id.run do
    let g := fun n : UInt64 => n == seed || b
    return g a && g 0
   f (a == 0) || f (a == seed)).toUInt64 + a

def propositionHelperLetCompound (x y : UInt64) : UInt64 :=
  (if x < y ∧ (let f := fun n : UInt64 => n == y; f x || f 0) then
    (let g := fun b : Bool => b || y == 0; g (x == 0)) else x == y).toUInt64 + x

def propositionHelperLetBoolean (x y : UInt64) : UInt64 :=
  if (let f := fun b : Bool => b || x == y; f (x == 0) && f (y == 0)) ∨ x < y then
    x + 7 else y * 3

def propositionHelperLetDecision (x y : UInt64) : UInt64 :=
  (decide (¬ (let f := fun n : UInt64 => n % 3 == 0; f x = f y) ∧ x ≤ y)).toUInt64 + y

def propositionHelperLetDependent (x y : UInt64) : UInt64 :=
  (if _h : (let f := fun b : Bool => b && x != y; f (x == 0) ≠ f (y == 0)) ∨ y < x then
    (let g := fun n : UInt64 => n == x; g y || g 0)
   else !(x == y)).toUInt64 + x

def propositionHelperLetUnused (x y : UInt64) : UInt64 :=
  if (let _unused := fun n : UInt64 => n == y; True) ∧
      (let _unused := fun b : Bool => b || x == y; True) then x + y else 0

def propositionHelperLetNested (x y : UInt64) : UInt64 :=
  if (let f := fun n : UInt64 => n == y; let word := x + y;
      let flag := f word; flag = f x) then x + 1 else y + 2

def rangePropositionHelperLetStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => n % 3 == 0; f a || f i.toUInt64) ∧ a ≤ seed then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangePropositionHelperLetExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (let f := fun b : Bool => b || seed == 0; f (a % 7 == 0) ≠ f (i.toUInt64 == 0)) ∨ a = seed then break
  return a

def rangePropositionHelperLetContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => n % 3 == 0; let flag := f a; flag = f i.toUInt64) ∧ seed ≤ a then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangePropositionHelperLetTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (decide ((let f := fun b : Bool => !b || seed == 0; f (a == seed) && f (a == 0)) ∨ a < seed)).toUInt64 + a

def booleanHelperRelationChoiceLeft (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) = (x == 0) then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else y == 0).toUInt64 + x

def booleanHelperRelationChoiceRight (x y : UInt64) : UInt64 :=
  (if (x == y) ≠ (Id.run do
      let f := fun b : Bool => !b || y == 0
      return f (x == y) && f (x == 0)) then
    (let g := fun n : UInt64 => n % 3 == 0; g x || g y) else x == 0).toUInt64 + x

def booleanHelperRelationChoiceFalse (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) = false then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else x == y).toUInt64 + x

def booleanHelperRelationChoiceDependent (x y : UInt64) : UInt64 :=
  (if _h : (let f := fun n : UInt64 => n == y; f x || f 0) =
      (let h := fun n : UInt64 => n % 3 == 0; h x || h y) then
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))
   else (let h := fun n : UInt64 => n % 5 == 0; h x && h y)).toUInt64 + y

def booleanHelperRelationChoiceTrue (x y : UInt64) : UInt64 :=
  (if _h : (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) ≠ true then
    (let f := fun n : UInt64 => n == y; f x || f 0) else x == y).toUInt64 + x

def booleanHelperRelationChoiceNested (x y : UInt64) : UInt64 :=
  (Id.run do
    if _h : (let f := fun n : UInt64 => n == y; f x || f 0) ≠ false then
      return if (x == 0) = false then
        (let g := fun b : Bool => b || y != 0; g (x == y) && g (x == 0))
        else false
    else return !(let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + x

def rangeHelperRelationChoiceStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if (let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) = (a == seed) then
        (let g := fun b : Bool => !b || seed == 0; g (a == seed) && g (i.toUInt64 == 0)) else a == seed) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperRelationChoiceExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (if _h : (let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) ≠ false then
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))
      else a % 11 == 0) then break
  return a

def rangeHelperRelationChoiceContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if (a == seed) ≠ (let f := fun n : UInt64 => n % 3 == 0; f a || f i.toUInt64) then
        (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))
      else false) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperRelationChoiceTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (if (let f := fun n : UInt64 => n == seed; f a || f 0) = false then
      (let f := fun n : UInt64 => n % 3 == 0; f a && f seed)
    else !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0))).toUInt64 + a

def booleanHelperPropositionChoiceWord (x y : UInt64) : UInt64 :=
  (if x < y then (let f := fun n : UInt64 => n == y; f x || f 0)
   else (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y))).toUInt64 + x

def booleanHelperPropositionChoiceLe (x y : UInt64) : UInt64 :=
  (Id.run do
    if x ≤ y then
      return (let f := fun b : Bool => !b || y == 0; f (x == y) && f (x == 0))
    else return !(let f := fun n : UInt64 => n == y; f x || f 0)).toUInt64 + x

def booleanHelperPropositionChoiceCompound (x y : UInt64) : UInt64 :=
  (if x < y ∧ (let f := fun n : UInt64 => n == y; f x || f 0).toUInt64 = 1 then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y))
   else (let g := fun n : UInt64 => n % 3 == 0; g x || g y)).toUInt64 + y

def booleanHelperPropositionChoiceDependent (x y : UInt64) : UInt64 :=
  (if _h : x ≠ y ∨ (let f := fun n : UInt64 => n == y; f x || f 0).toUInt64 = 1 then
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))
   else (let h := fun n : UInt64 => n % 3 == 0; h x || h y)).toUInt64 + y

def booleanHelperPropositionChoiceNegated (x y : UInt64) : UInt64 :=
  (if _h : ¬ x < y then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else x == y).toUInt64 + x

def booleanHelperPropositionChoiceLet (x y : UInt64) : UInt64 :=
  (if (let k := y + 1; x < k) then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else x == y).toUInt64 + x

def rangeHelperPropositionChoiceStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if a < seed + i.toUInt64 + 1 then
        (let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) else a == seed) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperPropositionChoiceExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (if _h : a ≠ seed ∧ (let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)).toUInt64 = 1 then
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))
      else a % 11 == 0) then break
  return a

def rangeHelperPropositionChoiceContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if a ≤ seed ∨ i.toUInt64 < 4 then
        (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))
      else false) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperPropositionChoiceTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (if (let k := seed + 1; a < k) then
      (let f := fun n : UInt64 => n == seed; f a || f 0)
    else !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0))).toUInt64 + a

def booleanHelperChoiceCondition (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) then x == 0 else y == 0).toUInt64 + x

def booleanHelperChoiceYes (x y : UInt64) : UInt64 :=
  (if x == y then (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0)) else y != 0).toUInt64 + x

def booleanHelperChoiceNo (x y : UInt64) : UInt64 :=
  (if x == 0 then x == y else
    !(let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))).toUInt64 + y

def booleanHelperChoiceDependent (x y : UInt64) : UInt64 :=
  (if _h : (let f := fun n : UInt64 => n == y; f x || f 0) then
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))
   else (let h := fun n : UInt64 => n % 3 == 0; h x || h y)).toUInt64 + y

def booleanHelperChoiceNested (x y : UInt64) : UInt64 :=
  (Id.run do
    if _h : (let f := fun n : UInt64 => n == y; f x || f 0) then
      return if x == 0 then
        (let g := fun b : Bool => b || y != 0; g (x == y) && g (x == 0))
        else false
    else return !(let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + x

def booleanHelperChoiceUnused (x y : UInt64) : UInt64 :=
  (if false then (let _unused := fun b : Bool => b && x != 0; x == y)
   else (let f := fun n : UInt64 => n == x; f y && f 0)).toUInt64 + y

def rangeHelperChoiceStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if (let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) then a == seed else i.toUInt64 == 0) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperChoiceExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (if _h : (let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) then
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))
      else a % 11 == 0) then break
  return a

def rangeHelperChoiceContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if a == seed then
        (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))
      else false) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperChoiceTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (if a == 0 then (let f := fun n : UInt64 => n == seed; f a || f 0)
    else !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0))).toUInt64 + a

def booleanHelperEqualityLeft (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) == (x == 0)).toUInt64 + x

def booleanHelperEqualityRight (x y : UInt64) : UInt64 :=
  ((x == 0) != (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0))).toUInt64 + x

def booleanHelperEqualityBoth (x y : UInt64) : UInt64 :=
  (decide ((let f := fun n : UInt64 => n == y; f x || f 0) =
    !(let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0)))).toUInt64 + x

def booleanHelperEqualityDependent (x y : UInt64) : UInt64 :=
  if _h : decide ((let f := fun n : UInt64 => n == y; f x || f 0) ≠
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))) then x + 7 else y + 11

def booleanHelperEqualityNested (x y : UInt64) : UInt64 :=
  ((!((let f := fun n : UInt64 => n == y; f x || f 0) ==
    (Id.run do
      let g := fun b : Bool => b || y != 0
      return g (x == y) && g (x == 0)))) ||
    (let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + y

def booleanHelperEqualityUnused (x y : UInt64) : UInt64 :=
  ((let _unused := fun b : Bool => b && x != 0; x == y) !=
    !(let f := fun n : UInt64 => n == x; f y && f 0)).toUInt64 + y

def rangeHelperEqualityStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ((let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) == (a == seed)) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperEqualityExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : decide ((let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) ≠
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))) then break
  return a

def rangeHelperEqualityContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ((a == seed) != (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperEqualityTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (decide ((let f := fun n : UInt64 => n == seed; f a || f 0) =
    !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0)))).toUInt64 + a

def booleanHelperJunctionLeft (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) && (x == 0)).toUInt64 + x

def booleanHelperJunctionRight (x y : UInt64) : UInt64 :=
  ((x == 0) || (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0))).toUInt64 + x

def booleanHelperJunctionBoth (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) &&
    !(let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))).toUInt64 + x

def booleanHelperJunctionDependent (x y : UInt64) : UInt64 :=
  if _h : ((let f := fun n : UInt64 => n == y; f x || f 0) ||
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))) then x + 7 else y + 11

def booleanHelperJunctionNested (x y : UInt64) : UInt64 :=
  (((!(let f := fun n : UInt64 => n == y; f x || f 0)) &&
    (Id.run do
      let g := fun b : Bool => b || y != 0
      return g (x == y) && g (x == 0))) ||
    (let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + y

def booleanHelperJunctionUnused (x y : UInt64) : UInt64 :=
  ((let _unused := fun b : Bool => b && x != 0; x == y) ||
    !(let f := fun n : UInt64 => n == x; f y && f 0)).toUInt64 + y

def rangeHelperJunctionStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ((let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) || a == seed) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperJunctionExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : ((let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) &&
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))) then break
  return a

def rangeHelperJunctionContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (a == seed || (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperJunctionTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return ((let f := fun n : UInt64 => n == seed; f a || f 0) &&
    !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0))).toUInt64 + a

def booleanHelperNegationWord (x y : UInt64) : UInt64 :=
  (!(let f := fun n : UInt64 => n == y; f x || f 0)).toUInt64 + x

def booleanHelperNegationBoolean (x y : UInt64) : UInt64 :=
  if !(Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0)) then x + 7 else y + 11

def booleanHelperNegationDependent (x y : UInt64) : UInt64 :=
  if _h : !(let f := fun n : UInt64 => n == y; f x || f 0) then x - 3 else y * 7

def booleanHelperNegationNested (x y : UInt64) : UInt64 :=
  (!(!(!(Id.run (pure (let f := fun n : UInt64 => n == y; f x || f 0) : Id (Id Bool)))))).toUInt64 + x

def booleanHelperNegationUnused (x y : UInt64) : UInt64 :=
  (!(let _unused := fun b : Bool => b && x != 0; x == y)).toUInt64 + y

def booleanHelperNegationIdResult (x y : UInt64) : UInt64 :=
  (!(!(pure (let f := fun n : UInt64 => (pure (n == y) : Id Bool); f x || f 0) : Id (Id Bool)))).toUInt64 + x

def rangeHelperNegationStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if !(let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperNegationExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if !(Id.run do
      let f := fun n : UInt64 => n % 7 == 0
      return f a || f (i.toUInt64 + 1)) then break
  return a

def rangeHelperNegationContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if !(!(let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperNegationTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (!(Id.run do
    let f := fun n : UInt64 => n == seed
    return f a || f 0)).toUInt64 + a

def booleanInnerWrapperWord (x y : UInt64) : UInt64 :=
  (Id.run do
    let f := fun n : UInt64 => n == y
    return f x || f 0).toUInt64 + x

def booleanInnerWrapperBoolean (x y : UInt64) : UInt64 :=
  if (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0)) then x + 7 else y + 11

def booleanInnerWrapperDependent (x y : UInt64) : UInt64 :=
  if _h : (Id.run do
    let f := fun n : UInt64 => n == y
    return f x || f 0) then x - 3 else y * 7

def booleanInnerWrapperNested (x y : UInt64) : UInt64 :=
  (Id.run (pure (let f := fun n : UInt64 => n == y; f x || f 0) : Id (Id Bool))).toUInt64 + x

def booleanInnerWrapperUnused (x y : UInt64) : UInt64 :=
  (pure (let _unused := fun b : Bool => b && x != 0; x == y) : Id Bool).toUInt64 + y

def booleanInnerWrapperIdResult (x y : UInt64) : UInt64 :=
  (pure (let f := fun n : UInt64 => (pure (n == y) : Id Bool); f x || f 0) : Id (Id Bool)).toUInt64 + x

def rangeInnerWrapperStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (Id.run do
      let f := fun n : UInt64 => n % 2 == 0
      return f a && f i.toUInt64) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeInnerWrapperExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (Id.run do
      let f := fun n : UInt64 => n % 7 == 0
      return f a || f (i.toUInt64 + 1)) then break
  return a

def rangeInnerWrapperContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (Id.run do
      let f := fun b : Bool => !b || a % 2 == 0
      return f (i.toUInt64 % 3 == 0) && f (a == seed)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeInnerWrapperTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (Id.run do
    let f := fun n : UInt64 => n == seed
    return f a || f 0).toUInt64 + a

def booleanInnerHelperWord (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 => n == y; f x || f 0).toUInt64 + x

def booleanInnerHelperBoolean (x y : UInt64) : UInt64 :=
  if (let f := fun b : Bool => !b || y == 0; f (x == y) && f (x == 0)) then x + 7 else y + 11

def booleanInnerHelperDependent (x y : UInt64) : UInt64 :=
  if _h : (let f := fun n : UInt64 => n == y; f x || f 0) then x - 3 else y * 7

def booleanInnerHelperNested (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 => n == y
   let g := fun b : Bool => !b || x == 0
   g (f x) && g (f 0)).toUInt64 + x

def booleanInnerHelperUnused (x y : UInt64) : UInt64 :=
  (let _unused := fun b : Bool => b && x != 0; x == y).toUInt64 + y

def booleanInnerHelperIdResult (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 => (pure (n == y) : Id Bool); f x || f 0).toUInt64 + x

def rangeInnerHelperStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeInnerHelperExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) then break
  return a

def rangeInnerHelperContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeInnerHelperTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (let f := fun n : UInt64 => n == seed; f a || f 0).toUInt64 + a

def booleanPropLetRelationWord (x y : UInt64) : UInt64 :=
  if (let b := x == y; b = (x == 0)) then x + 7 else y + 11

def booleanPropLetRelationDecision (x y : UInt64) : Bool :=
  decide (let b := x == y; b ≠ (x == 0))

def booleanPropLetRelationDependent (x y : UInt64) : Bool :=
  if _h : (let b := x == y; b = (y == 0)) then x != 0 else y != 0

def booleanPropLetRelationNested (x y : UInt64) : Id (Id Bool) :=
  pure (pure (decide (let n := x + y; let b := n == x; b ≠ (y == 0))))

def booleanPropLetRelationHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && y != 0
  if (let flag := f (x == y); flag = f (x == 0)) then x - 3 else y * 7

def booleanPropLetRelationUnused (x y : UInt64) : UInt64 :=
  if (let _unused := x + y; (x == 0) ≠ (y == 0)) then x + y else x - y

def rangeBoolLetRelationStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let b := a % 2 == 0; b = (i.toUInt64 % 3 == 0)) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeBoolLetRelationExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let b := a % 7 == 0; b ≠ (i.toUInt64 % 3 == 0)) then break
  return a

def rangeBoolLetRelationContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ (let b := a % 2 == 0; b = (i.toUInt64 % 3 == 0)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBoolLetRelationTail (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a)
  return decide (let b := value == seed; b = (seed == 0))

def booleanHelperReturnWord (x y : UInt64) : UInt64 :=
  let flag := Id.run do
    let f := fun n : UInt64 => n == y
    return f x
  flag.toUInt64 + x

def booleanHelperReturnBoolean (x y : UInt64) : UInt64 :=
  let flag := Id.run do
    let f := fun b : Bool => b && y != 7
    return f (x != 0)
  flag.toUInt64 * 13 + y

def booleanHelperReturnNested (x y : UInt64) : UInt64 :=
  let flag : Id (Id Bool) :=
    let f := fun n : Id UInt64 => Id.run n != y
    pure (pure (f x))
  flag.toUInt64 + y

def booleanHelperReturnCondition (x y : UInt64) : UInt64 :=
  if (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y)) then x + 3 else y - 5

def booleanHelperReturnCaptured (x y : UInt64) : UInt64 :=
  let g := fun n : UInt64 =>
    let flag := Id.run do
      let f := fun k : UInt64 => k != n && k == x
      return f y
    n + flag.toUInt64
  g x + g y

def booleanHelperReturnIgnored (x y : UInt64) : UInt64 :=
  let flag := Id.run do
    let f := fun (_ : Bool) => x != y
    return f (x == 0)
  flag.toUInt64 + 7

def rangeBoolTailHelperCapture (count seed : UInt64) : Id Bool := do
  let value ← (do
    let f := fun b : Bool => if b then seed + 7 else seed + 3
    let mut a := f false
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a)
  let f := fun x : UInt64 => x == seed
  return f value

def rangeBoolTailHelperBoolean (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a)
  let f := fun b : Bool => b || value == seed
  return f (value % 3 == 0)

def rangeBoolTailHelperNestedId (count seed : UInt64) : Id (Id Bool) := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if i.toUInt64 % 2 == 0 then continue
      a := a * 3 + i.toUInt64
    return a)
  let f := fun n : Id (Id UInt64) => Id.run (Id.run n) != seed
  return pure (f value)

def rangeWordStepReturnedHelper (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := Id.run do
      let f := fun b : Bool => b && a % 3 != 0
      return f (i.toUInt64 % 2 == 0)
    if flag then a := a + i.toUInt64 + 7 else a := a * 3 + 1
  return a

def publicBoolHelpersNested (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag
  let g := fun n : UInt64 => f (n != x)
  g (x + 1)

def publicBoolHelpersRepeated (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag && x != 0
  f (x != 7) || f (x == 7)

def publicBoolHelpersWrapped (flag : Bool) (x : UInt64) : Id (Id Bool) :=
  let f := fun b : Bool => b && flag
  pure (pure (f (x != 0) || f (x == 7)))

def publicBoolHelpersInputId (x : UInt64) (flag : Bool) : Bool :=
  let f := fun b : Id (Id Bool) => Id.run b && flag
  let g := fun n : Id UInt64 => f (Id.run n != x)
  g (x + 1) != g x

def publicBoolHelpersWord (flag : Bool) (x : UInt64) : Bool :=
  let f := fun n : UInt64 => n * 13 + x
  let g := fun b : Bool => if b then f (x + 1) else f (x - 1)
  g flag == f x || g (!flag) != 0

def publicBoolHelpersMany (x y : UInt64) : Bool :=
  let f := fun a b c : UInt64 => a + b * 7 - c + x
  f x y 3 == f y x 5 || f 0 1 2 != y

def publicBoolHelpersUnit (flag : Bool) (x : UInt64) : Bool :=
  let f := fun (_ : Unit) (n : UInt64) => n + x + flag.toUInt64
  f () 3 != x && f () x != 0

def publicBoolHelpersShadow (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b != flag
  let f := fun b : Bool => f b && x != 7
  let f := fun n : UInt64 => f (n == x)
  f x || f (x + 7)

def publicBoolHelpersSaved (flag : Bool) (x : UInt64) : Id Bool := do
  let f := fun b : Bool => b && flag
  let g := fun n : UInt64 => f (n != x)
  let saved ← pure (g (x + 1))
  return if saved then g x else !f saved

def publicBoolHelpersUnused (flag : Bool) (x : UInt64) : Bool :=
  let _ignored := fun n : UInt64 => n / (x - x)
  let f := fun b : Bool => b && flag
  let g := fun n : UInt64 => f (n != x)
  g x || g (x + 1)

def publicFlagWord (flag : Bool) (x : UInt64) : UInt64 :=
  if flag then x + 7 else x - 3

def publicWordFlag (x : UInt64) (flag : Bool) : UInt64 :=
  x * 11 + flag.toUInt64

def publicFlagsWord (left right : Bool) : UInt64 :=
  left.toUInt64 * 3 + right.toUInt64 * 7

def publicFlagResult (flag : Bool) (x : UInt64) : Bool := flag && x != 0

def publicWordFlagResult (x : UInt64) (flag : Bool) : Bool := !flag || x == 7

def publicFlagsResult (left right : Bool) : Bool := left != right

def publicFlagLet (flag : Bool) (x : UInt64) : UInt64 :=
  let saved := !flag
  let n := x + flag.toUInt64
  if saved then n / x else n % x

def publicFlagBind (x : UInt64) (flag : Bool) : Id UInt64 := do
  let saved ← pure (!flag)
  let n ← pure (x + saved.toUInt64)
  return if flag then n + 3 else n - 5

def publicFlagCapture (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag && x != 0
  f flag

def publicFlagsDecision (left right : Bool) : Id (Id Bool) :=
  pure (pure (decide (left = right)))

def publicIdWord (x y : UInt64) : Id UInt64 := pure (x + y)

def publicIdNested (x y : UInt64) : Id (Id UInt64) :=
  pure (pure (if x < y then x / y else y % x))

def publicIdBind (x y : UInt64) : Id UInt64 := do
  let n ← pure (x + y)
  let flag ← pure (n == 0)
  return if flag then n + 3 else y - 7

def publicIdBool (x y : UInt64) : Id Bool := pure (x != y && x != 0)

def publicIdBoolNested (x y : UInt64) : Id (Id Bool) :=
  pure (pure (decide (x < y ∧ ¬ (y == 0))))

def publicIdBoolHelper (x y : UInt64) : Id Bool := pure (
  let f : UInt64 → Bool := fun n => n != y
  f (x + 1))

def rangePublicIdYield (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a

def rangePublicIdExit (count seed : UInt64) : Id (Id UInt64) := pure (Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a)

def rangePublicIdContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    a := a + i.toUInt64
  return a

def rangePublicIdCapture (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if b then seed + 1 else seed
  let mut a := g (f (count == 0))
  for i in [:count.toNat] do
    a := a + g (f (a == seed)) + i.toUInt64
    if a % 7 == 0 then break
  return a

def publicBooleanTrue (_x _y : UInt64) : Bool := true

def publicBooleanCompare (x y : UInt64) : Bool := x != y && x + 1 == y

def publicBooleanChoice (x y : UInt64) : Bool :=
  if x < y then x / y == 0 else !(y % x == 0)

def publicBooleanDependent (x y : UInt64) : Bool :=
  if _h : x == y then x != 0 else y != 0

def publicBooleanLet (x y : UInt64) : Bool :=
  let n := x + y
  let flag := n == 0
  let other := flag || x < y
  other && !(n == y)

def publicBooleanDo (x y : UInt64) : Bool := Id.run do
  let n ← pure (x + y)
  let flag ← pure (n == 0)
  return flag || y == 0

def publicBooleanNamed (x y : UInt64) : Bool :=
  let f : UInt64 → Bool := fun n => n != y
  f (x + 1)

def publicBooleanCaptured (x y : UInt64) : Bool :=
  let flag := x == 0
  (fun b : Bool => b || flag) (y == 0)

def publicBooleanDecision (x y : UInt64) : Bool :=
  decide ((let b := x == y; b ∨ x < y) ∧ ¬ (y == 0))

def publicBooleanWrapped (x y : UInt64) : Bool :=
  Id.run (pure (Id.run (pure ((x == y) != (x == 0)))))

def booleanCallArgumentNested (x y : UInt64) : UInt64 :=
  let f : Id (Id Bool) → Id (Id Bool) := fun (b : Id (Id Bool)) => b && x != y
  let g : Id Bool → Id UInt64 := fun (b : Id Bool) => (f b).toUInt64 + y
  Id.run (g (f (x == 0))) + Id.run (g (x != y))

def booleanCallArgumentWord (x y : UInt64) : UInt64 :=
  let p := fun n : UInt64 => n != y
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => if b then x + y else x - y
  g (f (p x)) + g (p (g (f true)))

def booleanCallArgumentChoice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => if b then x / y else x % y
  g (if f (x == 0) then f true else !(f (x != y)))

def booleanCallArgumentBind (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let g := fun b : Bool => if b then x + 3 else y + 7
  g (Id.run do
    let saved ← pure (f (x == 0))
    let word := g (f saved)
    return f (word == y))

def booleanCallArgumentCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b != (x == y)
  let g := fun b : Bool => if b then x + 1 else y - 1
  let h := fun b : Bool =>
    let saved := f b
    let f := fun other : Bool => other && saved
    g (f saved) + g (f (x == 0))
  h (f true) + h (f false)

def booleanCallArgumentDecision (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let g := fun b : Bool => if b then x + y else y - x
  g (decide (¬ f (x == 0) ∧ x < y)) + g (decide (f false ∨ y ≤ x))

def rangeBooleanCallArgumentStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Id Bool → Id Bool := fun (b : Id Bool) => b && a != 0
    let g : Id Bool → Id (ForInStep UInt64) := fun (b : Id Bool) =>
      pure (if Id.run b then .done (a + i.toUInt64) else .yield (a + 1))
    g (f (f (i.toUInt64 == seed)))

def rangeBooleanCallArgumentContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == seed
    let g := fun b : Bool => if b then a + 3 else a + i.toUInt64
    if g (f (i.toUInt64 == 0)) % 3 == 0 then
      a := g (f false)
      continue
    a := g (f (a == 0))
  return a

def rangeBooleanCallArgumentOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if b then seed + 1 else seed
  let mut a := g (f (count == 0))
  for i in [:count.toNat] do
    if a < g (f (i.toUInt64 == 0)) then break
    a := a + g (f (a == seed)) + i.toUInt64
  return a + g (f false)

def rangeBooleanCallArgumentBind (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => if b then ForInStep.done (a + 3) else .yield (a + i.toUInt64 + 1)
    return g (Id.run do
      let saved ← pure (f (i.toUInt64 == seed))
      return !(f saved))

def booleanInputWord (x y : UInt64) : UInt64 :=
  let f : Id Bool → UInt64 := fun (b : Id Bool) => if Id.run b then x + y else x - y
  f (x == 0) + f (x != y)

def booleanInputPredicate (x y : UInt64) : UInt64 :=
  let f : Id Bool → Id Bool := fun (b : Id Bool) => b || x == y
  (f (x == 0)).toUInt64 + (f (x != y)).toUInt64 + x

def booleanInputNested (x y : UInt64) : UInt64 :=
  let f : Id (Id Bool) → Id (Id Bool) := fun (b : Id (Id Bool)) => b && x != y
  let g : Id Bool → Id UInt64 := fun (b : Id Bool) => (f b).toUInt64 + y
  Id.run (g (x == 0)) + Id.run (g (x != y))

def booleanInputUnused (x y : UInt64) : UInt64 :=
  let _unused : Id Bool → UInt64 := fun (b : Id Bool) => if Id.run b then x / 0 else y % 0
  x + y

def booleanInputDecision (x y : UInt64) : UInt64 :=
  let f : Id Bool → Bool := fun (b : Id Bool) => b || x == y
  let g : Id (Id Bool) → Bool := fun (b : Id (Id Bool)) => if ¬ f b then !b else b
  (decide (g true ∧ x < y)).toUInt64 + (g false).toUInt64 + y

def booleanInputBind (x y : UInt64) : UInt64 := Id.run do
  let f : Id Bool → Id (Id UInt64) := fun (b : Id Bool) => do
    let saved ← pure (b || x == y)
    return (show UInt64 from if saved then x + 3 else y + 7)
  let a ← f (x == 0)
  return Id.run a + Id.run (← f (decide (Id.run a < y)))

def rangeBooleanInputStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Id Bool → Id (ForInStep UInt64) := fun (flag : Id Bool) => do
      let g : Id (Id Bool) → ForInStep UInt64 := fun (inner : Id (Id Bool)) =>
        if flag && !inner then .done (a + i.toUInt64) else .yield (a - count)
      return g (a == seed)
    f (i.toUInt64 % 3 == 0)

def rangeBooleanInputContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Id Bool → Id Bool := fun (b : Id Bool) => b && a != 0
    if Id.run (f (i.toUInt64 == seed)) then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeBooleanInputOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let f : Id (Id Bool) → UInt64 := fun (b : Id (Id Bool)) => if b || flag then seed + 1 else seed
  let mut a := f (count == 0)
  for i in [:count.toNat] do
    if a < f (i.toUInt64 == 0) then break
    a := a + i.toUInt64 + 1
  return a + f (a == seed)

def rangeBooleanInputHelper (count seed : UInt64) : UInt64 := Id.run do
  let f : Id Bool → Id Bool := fun (b : Id Bool) => b && seed != 0
  let mut a := seed
  for i in [:count.toNat] do
    let g : Id (Id Bool) → UInt64 := fun (b : Id (Id Bool)) => (f b).toUInt64 + a
    if g (i.toUInt64 == 0) < seed then break
    a := g (a == seed) + i.toUInt64 + 1
  return a + (f (a == seed)).toUInt64

def booleanPredicateResultBool (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b && x != 0
  let g := fun b : Bool => f b
  (g (x == y)).toUInt64 + (g true).toUInt64

def booleanPredicateResultWord (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || y == 0
  let g := fun n : UInt64 => f (n == x)
  if g y then x + 7 else y + (g x).toUInt64

def booleanPredicateResultNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  let g := fun b : Bool => f b && f (x == y)
  let h := fun n : UInt64 => if n < y then g (f false) else f (g (n == x))
  (h x).toUInt64 + (g (h y)).toUInt64 * 3

def booleanPredicateResultCapture (x y : UInt64) : UInt64 :=
  let saved := x == 0
  let f := fun b : Bool => b || saved
  let g := fun b : Bool => f b && y != 0
  let f := fun b : Bool => !b
  let g := fun b : Bool => g (f b)
  if _h : g (x == y) then x + 3 else y + (g false).toUInt64

def booleanPredicateResultUnused (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x / y == 0
  let _unused := fun _n : UInt64 => f true
  let g := fun b : Bool => f true || f b
  x + y + (g false).toUInt64

def booleanPredicateResultWrapped (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == y
  let g : Bool → Id (Id Bool) := fun b => pure (Id.run (pure (f b)))
  let h : Id (Id UInt64) → Id Bool := fun n => pure (g ((show UInt64 from n) == y))
  (h x).toUInt64 + (g false).toUInt64

def rangeBooleanPredicateResultLocalBool (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    let g := fun b : Bool => !(f b)
    if g ((UInt64.ofNat i) < seed) then
      a := a + 7
      break
    a := a + (UInt64.ofNat i) + 1
  return a

def rangeBooleanPredicateResultLocalWord (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == seed
    let g := fun n : UInt64 => f (n == (UInt64.ofNat i))
    if g a then
      a := a + 3
      continue
    a := a + (UInt64.ofNat i) + 1
  return a

def rangeBooleanPredicateResultLocalNested (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    let g := fun b : Bool => f (!b)
    let h := fun n : UInt64 => g (n == (UInt64.ofNat i))
    if h seed then break
    a := a + (g (h a)).toUInt64 + 1
  return a

def rangeBooleanPredicateResultLocalWrapped (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    let g : Bool → Id (Id Bool) := fun b => pure (Id.run (pure (f b)))
    let h : Id (Id UInt64) → Id Bool := fun n => pure (g ((show UInt64 from n) == (UInt64.ofNat i)))
    if Id.run (h a) then
      a := a + 9
      break
    a := a + (g true).toUInt64 + 1
  return a

def rangeBooleanPredicateResultOuterBool (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => !(f b)
  let mut a := seed + (g true).toUInt64
  for i in [:count.toNat] do
    if g (a == (UInt64.ofNat i)) then
      a := a + 5
      continue
    a := a + 1
  return a + (g false).toUInt64

def rangeBooleanPredicateResultOuterWord (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun n : UInt64 => f (n == seed)
  let mut a := seed
  for i in [:(count + (g 0).toUInt64).toNat] do
    if g (a + (UInt64.ofNat i)) then break
    a := a + 1
  return a + (g seed).toUInt64

def rangeBooleanPredicateResultOuterNested (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => f (!b)
  let h := fun n : UInt64 => g (n == seed)
  let mut a := seed
  for i in [:count.toNat] do
    let localHelper := fun b : Bool => h (a + b.toUInt64)
    if localHelper ((UInt64.ofNat i) == seed) then break
    a := a + (g (h a)).toUInt64 + 1
  return a + (h seed).toUInt64

def rangeBooleanPredicateResultOuterWrapped (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g : Bool → Id (Id Bool) := fun b => pure (Id.run (pure (f b)))
  let h : Id (Id UInt64) → Id Bool := fun n => pure (g ((show UInt64 from n) == seed))
  let _unused := fun b : Bool => g (!b)
  let mut a := seed + (g true).toUInt64
  for i in [:count.toNat] do
    if Id.run (h (a + (UInt64.ofNat i))) then break
    a := a + 1
  return a + (g false).toUInt64

def rangeBooleanPredicateResultStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let delta := Id.run do
      let f := fun b : Bool => b || a == 0
      let g := fun b : Bool => f b
      return if g (UInt64.ofNat i % 3 == 0) then 3 else 1
    a := a + UInt64.ofNat i + delta
    if a % 7 == 0 then break
  return a

def rangeBooleanPredicateResultCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (Id.run do
      let f := fun b : Bool => !b || a == seed
      let g := fun n : UInt64 => f (n % 3 == 0)
      return (g (UInt64.ofNat i)).toUInt64) == 0 then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateResultOuter (count seed : UInt64) : UInt64 := Id.run do
  let extra := Id.run do
    let f := fun b : Bool => b || seed == 0
    let g := fun b : Bool => f b
    return (g (count == 0)).toUInt64
  let mut a := seed + extra
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if a % 7 == 0 then break
  return a

def rangeBooleanPredicateResultHelper (count seed : UInt64) : UInt64 := Id.run do
  let h := fun value : UInt64 =>
    let f := fun b : Bool => !b && seed != 0
    let g := fun b : Bool => f b
    if g (value == seed) then value + 3 else value - 1
  let mut a := seed
  for i in [:count.toNat] do
    a := h a + UInt64.ofNat i
    if a % 11 == 0 then break
  return a

def booleanPredicateBind (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b && x != 0
  let flag ← pure (f (x == y))
  return if flag then x + 7 else y + 11

def booleanPredicateBindNested (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || x == 0
  let flag ← Id.run (pure (f (x == y)))
  let next ← pure (Id.run (pure (f (!flag))))
  return flag.toUInt64 + next.toUInt64 * 3

def booleanPredicateBindChoice (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b
  let g := fun b : Bool => b && y != 0
  let flag ← pure (if f (x == y) = g false then g true else f false)
  let next ← pure (if _h : x < y then f flag else g flag)
  return if _h : next then x + flag.toUInt64 else y - flag.toUInt64

def booleanPredicateBindCapture (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || y == 0
  let saved ← pure (f (x == y))
  let g := fun z : UInt64 => if saved then z + x else z - y
  let saved ← pure (f (!saved))
  return g y + saved.toUInt64

def booleanPredicateBindUnused (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || x / y == 0
  let _unused ← pure (f true)
  let flag ← f (x == y)
  return if flag then x + y else x - y

def booleanPredicateBindBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g : UInt64 → Id UInt64 := fun z => do
    let flag ← pure (f (z == y))
    return if flag then z + 7 else z - 11
  Id.run (g x) + Id.run (g y)

def rangeBooleanPredicateLoopBindBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let stop ← pure (f (UInt64.ofNat i % 3 == 0))
    a := a + UInt64.ofNat i + 1
    if stop && a % 7 == 0 then break
  return a

def rangeBooleanPredicateLoopBindContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => !b || a == seed
    let skip ← Id.run (pure (!(f (UInt64.ofNat i % 3 == 0))))
    if skip then continue
    let kept ← pure (f (!skip) || skip)
    a := a + UInt64.ofNat i + kept.toUInt64 + 1
  return a

def rangeBooleanPredicateLoopBindChoice (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == seed
    let g := fun b : Bool => !b && seed != 0
    let flag ← pure (if _h : a ≤ seed then f (g false) else g (f true))
    let next ← pure (if f flag = g false then !(g flag) else f true)
    a := a + next.toUInt64 + UInt64.ofNat i
    if _h : flag then break
  return a

def rangeBooleanPredicateLoopBindCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Bool → Id Bool := fun b => b && a != seed
    let saved ← f (UInt64.ofNat i % 2 == 0)
    let _unused ← pure (Id.run (f true))
    let h := fun x : UInt64 => if saved then x + 3 else x + 1
    let saved ← pure (!(f false))
    a := h a + UInt64.ofNat i
    if saved && a % 13 == 0 then break
  return a

def rangeBooleanPredicateOuterBindBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let flag ← pure (f (count == 0))
  let first : UInt64 := if flag then 0 else 1
  let stop := count + flag.toUInt64
  let mut a := seed + flag.toUInt64
  for i in [first.toNat:stop.toNat:2] do
    a := a + UInt64.ofNat i + 1
    if flag && a % 7 == 0 then break
  return if flag then a + 1 else a

def rangeBooleanPredicateOuterBindCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved ← Id.run (pure (!(f false)))
  let h := fun x : UInt64 => if saved then x + seed else x - seed
  let saved ← pure (f (count == 0))
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (f (a == seed))
    a := h a + UInt64.ofNat i
    if flag && saved then break
  return if saved then a + 1 else a

def rangeBooleanPredicateOuterBindChoice (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let flag ← pure (if _h : seed ≤ count then f (g false) else g (f true))
  let next ← pure (f flag != g false)
  let _unused ← pure (if next then g false else f true)
  let mut a := seed
  for i in [:count.toNat] do
    if next && a % 7 == 0 then continue
    a := a + UInt64.ofNat i + flag.toUInt64 + 1
  return if next then a + flag.toUInt64 else a

def rangeBooleanPredicateOuterBindDirect (count seed : UInt64) : UInt64 := Id.run do
  let f : Bool → Id Bool := fun b => !b
  let flag ← f (seed == 0)
  let g := fun b : Bool => (Id.run do let saved ← pure (Id.run (f b)); return saved.toUInt64) == 0
  let next ← pure (g flag)
  let mut a := seed
  for i in [:count.toNat] do
    let saved ← g (a == seed)
    a := a + UInt64.ofNat i + saved.toUInt64 + 1
    if next && a % 5 == 0 then break
  return if flag then a + next.toUInt64 else a

def rangeBooleanPredicateBindStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let delta := Id.run do
      let flag ← pure (f (UInt64.ofNat i % 3 == 0))
      return if flag then 3 else 1
    a := a + delta + UInt64.ofNat i
    if a % 7 == 0 then break
  return a

def rangeBooleanPredicateBindCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => !b || a == seed
    if (Id.run do
      let flag ← pure (f (UInt64.ofNat i % 3 == 0))
      return flag.toUInt64) == 0 then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateBindOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let extra := Id.run do
    let flag ← pure (f (count == 0))
    return flag.toUInt64
  let mut a := seed + extra
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if a % 7 == 0 then break
  let last := Id.run do
    let flag ← pure (f (a == seed))
    return if flag then a + 3 else a
  return last

def rangeBooleanPredicateBindOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b && seed != 0
  let h : UInt64 → Id UInt64 := fun value => do
    let saved ← Id.run (pure (f (value == seed)))
    return if saved then value + 3 else value - 1
  let mut a := seed
  for i in [:count.toNat] do
    a := Id.run (h a) + UInt64.ofNat i
    if a % 11 == 0 then break
  return a

def booleanPredicateWrapper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b && x != 0
  (Id.run (pure (f (x == y)))).toUInt64

def booleanPredicateWrapperNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  (!(Id.run (pure (Id.run (pure (f true)))))).toUInt64 +
    (Id.run (pure (!(f false)))).toUInt64

def booleanPredicateWrapperLet (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let flag := Id.run (pure (f (x != 0)))
  let saved := flag
  let flag := Id.run (pure (f (!saved)))
  if saved then x + flag.toUInt64 else y + flag.toUInt64

def booleanPredicateWrapperCondition (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  if _h : Id.run (pure (f (x == y))) = false then x + 7 else y + 11

def booleanPredicateWrapperArgument (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == y
  (f (Id.run (pure (f (x == 0))))).toUInt64 +
    (Id.run (pure (f (Id.run (pure (f false)))))).toUInt64

def booleanPredicateWrapperBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == 0
  let g := fun b : Bool => (Id.run (pure (f b))).toUInt64 == 0 && y != 0
  (Id.run (pure (g (x == y)))).toUInt64

def rangeBooleanPredicateWrapperStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    if Id.run (pure (f (UInt64.ofNat i == seed % 7))) then break
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateWrapperContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => !b || a == seed
    if !(Id.run (pure (f (UInt64.ofNat i % 3 == 0)))) then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateWrapperOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let flag := Id.run (pure (f (count == 0)))
  let stop := count + (Id.run (pure (f false))).toUInt64
  let mut a := seed + flag.toUInt64
  for i in [:stop.toNat] do
    a := a + UInt64.ofNat i + 1
    if _h : Id.run (pure (f (a % 7 == 0))) ≠ false then break
  return a + (Id.run (pure (f (a == seed)))).toUInt64

def rangeBooleanPredicateWrapperCapture (count seed : UInt64) : UInt64 :=
  let f := fun b : Bool => b && seed != 0
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let g := fun b : Bool => (Id.run (pure (f b))).toUInt64 == 0
    let flag := Id.run (pure (g (UInt64.ofNat i % 3 == 0)))
    if flag then .yield (a + 3) else .done (a + UInt64.ofNat i)

def booleanPredicateCondition (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  if f (x == y) then x + 3 else if g false then y * 5 else x - y

def booleanPredicateConditionRelations (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  let a := if f (x == y) = g true then x + y else x - y
  let b := if f false ≠ g (x == 0) then x * 3 else y * 5
  if f true == g false then a + b else if f false != g true then a - b else a

def booleanPredicateConditionDependent (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  if _h : f (x == y) then
    if _k : f false = g true then x + 7 else y - 11
  else
    if _k : f true ≠ g false then x ^^^ y else x * y

def booleanPredicateConditionNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || y == 0
  let g := fun b : Bool => !b && x != y
  if !(f (g (x == y))) && g true then x + 3
  else if (if _h : x < y then f false else g true) then y + 5
  else if (if f false then g true else f true) then x - 7 else y - 11

def booleanPredicateConditionCapture (x y : UInt64) : UInt64 :=
  let saved := x == y
  let f := fun b : Bool => b || saved
  let h := fun a : UInt64 => if f (a == y) then a + x else a - x
  let x := x + 1
  let g := fun b : Bool => (if f b then x else y) == x
  if g (x == y) = f saved then h x else h y

def booleanPredicateConditionBody (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let g := fun b : Bool => (if @Eq Bool (f b) true then x else y) == x
  let a ← if @Eq Bool (f (x == y)) true then pure (x + 1) else pure (y + 3)
  let b := if g false then x - y else y - x
  return if _h : @Ne Bool (f true) (f false) then a + b else a - b

def rangeBooleanPredicateConditionBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun flag : Bool => flag || a % 7 == 0
    if f (UInt64.ofNat i == seed % 9) then break
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateConditionSkip (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun flag : Bool => !flag || a == seed
    if !f (UInt64.ofNat i % 3 == 0) then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateConditionEq (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun b : Bool => b != (a % 5 == 0)
    if f (UInt64.ofNat i == seed % 11) = false then .done (a + 7)
    else .yield (a + UInt64.ofNat i + 1)

def rangeBooleanPredicateConditionNe (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun b : Bool => b && a != 0
    if f (UInt64.ofNat i % 3 == 0) ≠ f (seed == 0) then .yield (a + 11)
    else .done (a + UInt64.ofNat i)

def rangeBooleanPredicateConditionProof (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun b : Bool => !b || a % 7 == 0
    if _h : f (UInt64.ofNat i != seed % 13) then pure (.done (a + 3))
    else pure (.yield (a + UInt64.ofNat i + 1))

def rangeBooleanPredicateConditionOuterBreak (count seed : UInt64) : UInt64 := Id.run do
  let captured := seed == 0
  let f := fun b : Bool => b || captured
  let mut a := seed
  for i in [:count.toNat] do
    if f (UInt64.ofNat i == seed % 11) then break
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateConditionNestedStep (count seed : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let g := fun b : Bool => b || a == seed
    if f (g (UInt64.ofNat i % 3 == 0)) then pure (.done (a + 7))
    else if _h : g (UInt64.ofNat i == seed % 7) ≠ false then pure (.yield (a + 2))
    else pure (.done a)

def rangeBooleanPredicateConditionIdStep (count seed : UInt64) : UInt64 :=
  let f : Bool → Id (Id Bool) := fun b => !b
  forIn (m := Id) [:count.toNat] seed fun i a =>
    if _h : @Eq Bool (f (UInt64.ofNat i % 3 == 0)) false then .yield (a + 3)
    else .done (a + UInt64.ofNat i)

def rangeBooleanPredicateConditionStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    a := a + (if f (UInt64.ofNat i % 2 == 0) then 3 else 1)
    if (if f (a % 7 == 0) then 1 else 0 : UInt64) == 1 then break
  return a

def rangeBooleanPredicateConditionContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (if _h : f (UInt64.ofNat i % 3 == 0) ≠ f false then 1 else 0 : UInt64) == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateConditionOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let stop := count + (if f false then 1 else 0)
  let mut a := seed + (if _h : f true = f false then 1 else 0)
  for i in [:stop.toNat] do
    if (if f (a % 7 == 0) then 1 else 0 : UInt64) == 1 then break
    a := a + UInt64.ofNat i + 1
  return if f (a == seed) then a + 1 else a

def rangeBooleanPredicateConditionOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (if f b then (1 : UInt64) else 0) == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (if g b = f b then (1 : UInt64) else 0) == 1 && a != seed
    if (if h (a % 5 == 0) then 1 else 0 : UInt64) == 1 then break
    a := a + UInt64.ofNat i + 1
  return if _h : g (a == seed) ≠ f false then a + 1 else a

def booleanPredicateLet (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  let first := f (x == y)
  let second := g first && !(f false)
  if first || second then x + second.toUInt64 else y - first.toUInt64

def booleanPredicateLetNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  let flag := !!!(f (g (f (x == y))))
  let flag := g flag != f (!flag)
  if _h : flag then x + y else x - y

def booleanPredicateLetChoice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  let first := if f (x == y) then g true else !(f false)
  let second := if _h : x < y ∧ (g first).toUInt64 ≠ 0 then f first else g (!first)
  let third := decide (f second ≠ g first)
  if second && third then x * 3 else y + first.toUInt64

def booleanPredicateLetCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let saved := f (x == 0)
  let h := fun a : UInt64 =>
    let inner := f (a == y) && saved
    if inner then a + x else a - x
  let x := x + 1
  let saved := f (x == y)
  if saved then h x else h y

def booleanPredicateLetUnused (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let _unused := f (x == y)
  let kept := f true
  let _unused := if False then f kept else !(f false)
  x + y + kept.toUInt64

def booleanPredicateLetBody (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let flag : Id (Id Bool) := f (x == y)
  let g := fun b : Bool => (let saved := f b; Bool.toUInt64 saved) == x
  let result := g flag
  return if result then Bool.toUInt64 flag + x else y

def rangeBooleanPredicateLetStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    a := a + (let flag := f (UInt64.ofNat i % 2 == 0); if flag then 3 else 1)
    if (let stop := f (a % 7 == 0); stop.toUInt64) == 1 then break
  return a

def rangeBooleanPredicateLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (let skip := !(f (UInt64.ofNat i % 3 == 0)); skip.toUInt64) == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let stop := count + (let flag := f false; flag.toUInt64)
  let mut a := seed + (let flag := f true; if flag then 1 else 0)
  for i in [:stop.toNat] do
    if (let flag := f (a % 7 == 0); flag.toUInt64) == 1 then break
    a := a + UInt64.ofNat i + 1
  return let flag := f (a == seed); if flag then a + 1 else a

def rangeBooleanPredicateLetOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (let flag := !(f b); flag.toUInt64) == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (let flag := g b && f b; flag.toUInt64) == 1 && a != seed
    if (let flag := h (a % 5 == 0); flag.toUInt64) == 1 then break
    a := a + UInt64.ofNat i + 1
  return let flag := g (a == seed); if flag then a + 1 else a

def booleanPredicateProposition (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  (if x < y then f false else g true).toUInt64 +
    (if x ≤ y then g (x == 0) else f (y == 0)).toUInt64 * 3 +
    (if x > y then f true else g false).toUInt64 * 5 +
    (if x ≥ y then g false else f true).toUInt64 * 7

def booleanPredicatePropositionDependent (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  (if _h : x ≠ y then f false else !(g true)).toUInt64 +
    (if _h : x = y then !(f true) else g (f false)).toUInt64

def booleanPredicatePropositionNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  (!(if (x < y ∨ y = 0) ∧ ¬ (x = 0) then
    (if _h : (f true).toUInt64 ≤ (g false).toUInt64 then g false else f true)
    else g (x == 0) && f (y == 0))).toUInt64

def booleanPredicatePropositionArgument (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  (f (if x < y then f false else g true)).toUInt64 +
    (!(g (if _h : (g true).toUInt64 ≠ 0 ∨ x = y then g (f false) else f (g true)))).toUInt64

def booleanPredicatePropositionCapture (x y : UInt64) : UInt64 :=
  let saved := x == y
  let f := fun b : Bool => b || saved
  let y := y + 1
  let g := fun b : Bool => !b && x == y
  (if True ∧ ¬ False then f saved else g false).toUInt64 +
    (if _h : False ∨ ¬ True then g true else f false).toUInt64 * 3 +
    (if ¬ (x ≤ y) ∧ (x != 0) then g saved else f false).toUInt64 * 5

def booleanPredicatePropositionBody (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let g := fun b : Bool => Bool.toUInt64 (if x ≤ y then f b else f false) == x
  let a ← pure (if x = y then g false else !(f true)).toUInt64
  let b ← pure (!(if _h : x ≠ 0 ∧ y ≤ x then f false else g (f true))).toUInt64
  return a + b

def rangeBooleanPredicatePropositionStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => !b && a != seed
    a := a + UInt64.ofNat i
    if (if a % 7 ≤ 1 then g (a == seed) else f true).toUInt64 == 1 then break
  return a

def rangeBooleanPredicatePropositionContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (!(if _h : UInt64.ofNat i % 3 = 0 ∨ a = seed then f (a == seed) else f true)).toUInt64 == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicatePropositionOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let stop := count + (if seed < count then g true else f true).toUInt64
  let mut a := seed + (if _h : seed ≤ 1 then f false else g false).toUInt64
  for i in [:stop.toNat] do
    if (!(if a % 7 = 0 ∧ (f false).toUInt64 ≤ 1 then g (a == seed) else f true)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (if _h : a ≠ seed ∨ ¬ (seed ≤ count) then f true else g false).toUInt64

def rangeBooleanPredicatePropositionOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (!(if _h : seed ≤ count then f (!b) else f b)).toUInt64 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (if (g b).toUInt64 < 1 then f b else g false).toUInt64 == 1 && a != seed
    if (if a % 5 = 0 then g (a == seed) else h true).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(if _h : (g (a == seed)).toUInt64 ≥ 1 then f true else g false)).toUInt64

def booleanPredicateChoice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  (if f (x == y) then f false else g true).toUInt64 +
    (if g false = f true then g (x == 0) else f (y == 0)).toUInt64 * 3

def booleanPredicateChoiceDependent (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  (if _h : f (x == 0) ≠ g (x == y) then f false else !(g true)).toUInt64 +
    (if _h : g false then !(f true) else g (f false)).toUInt64

def booleanPredicateChoiceNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  (!(if f (x == y) then
    (if _h : g true = f false then g false else f true)
    else g (x == 0) && f (y == 0))).toUInt64

def booleanPredicateChoiceArgument (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  (f (if g (x == 0) then f false else g true)).toUInt64 +
    (!(g (if _h : f true ≠ g false then g (f false) else f (g true)))).toUInt64

def booleanPredicateChoiceBranches (x y : UInt64) : UInt64 :=
  let saved := x == y
  let f := fun b : Bool => b || saved
  let y := y + 1
  let g := fun b : Bool => !b && x == y
  (if saved then f true else g false).toUInt64 +
    (if _h : x != y then g true else f false).toUInt64 * 3

def booleanPredicateChoiceBody (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let g := fun b : Bool => Bool.toUInt64 (if @Eq Bool (f b) true then f false else f true) == x
  let a ← pure (if g (x == y) then g false else !(f true)).toUInt64
  let b ← pure (!(if _h : g true then f false else g (f true))).toUInt64
  return a + b

def rangeBooleanPredicateChoiceStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => !b && a != seed
    a := a + UInt64.ofNat i
    if (if f (a % 7 == 0) then g (a == seed) else f true).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (!(if _h : f (UInt64.ofNat i % 3 == 0) then f (a == seed) else f true)).toUInt64 == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let stop := count + (if f false then g true else f true).toUInt64
  let mut a := seed + (if _h : g false = f true then f false else g false).toUInt64
  for i in [:stop.toNat] do
    if (!(if f (a % 7 == 0) then g (a == seed) else f true)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (if _h : g (f (a == seed)) ≠ f false then f true else g false).toUInt64

def rangeBooleanPredicateChoiceOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (!(if _h : f b then f (!b) else f b)).toUInt64 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (if g b then f b else g false).toUInt64 == 1 && a != seed
    if (if h (a % 5 == 0) then g (a == seed) else h true).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(if _h : g (a == seed) then f true else g false)).toUInt64

def booleanPredicateEqual (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  (f (x == y) == g false).toUInt64 + (g (x != 0) != f true).toUInt64 * 3

def booleanPredicateDecideEqual (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  (decide (f (x == 0) = g (x == y))).toUInt64 + (decide (g false ≠ f true)).toUInt64 * 3

def booleanPredicateEqualityNot (x y : UInt64) : UInt64 :=
  let saved := x == y
  let f := fun b : Bool => !b || x == 0
  (!(f saved != !(f false && saved))).toUInt64 + (!(decide (f true = saved))).toUInt64

def booleanPredicateEqualityMixed (x y : UInt64) : UInt64 :=
  let word := fun n : UInt64 => n % 3 == 0
  let flag := fun b : Bool => b && y != 0
  (word x == flag (x / y == 0)).toUInt64 + (decide (flag true ≠ word y)).toUInt64 * 3

def booleanPredicateEqualityArgument (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  (f (g (x == 0) == f false)).toUInt64 + (!(g (decide (f true ≠ g false)))).toUInt64

def booleanPredicateEqualityBody (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let g := fun b : Bool => (@BEq.beq Bool (@instBEqOfDecidableEq Bool instDecidableEqBool) (f b) (f (!b))).toUInt64 == x
  let a ← pure (g (x == y) != f (g false)).toUInt64
  let b ← pure (decide (@Eq Bool (f true) (!(g false)))).toUInt64
  return a + b

def rangeBooleanPredicateEqualityStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => !b && a != seed
    a := a + UInt64.ofNat i
    if (f (a % 7 == 0) == g (a == seed)).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateEqualityContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (!(decide (f (UInt64.ofNat i % 3 == 0) ≠ f (a == seed)))).toUInt64 == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateEqualityOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let stop := count + (decide (f false = g true)).toUInt64
  let mut a := seed + (g false != f true).toUInt64
  for i in [:stop.toNat] do
    if (!(f (a % 7 == 0) == g (a == seed))).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (decide (g (f (a == seed)) ≠ f false)).toUInt64

def rangeBooleanPredicateEqualityOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (!(decide (f b = f (!b)))).toUInt64 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (g b != f b).toUInt64 == 1 && a != seed
    if (h (a % 5 == 0) == g (a == seed)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(decide (g (a == seed) ≠ f true))).toUInt64

def booleanPredicateAndOr (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  (f (x == y) && g false).toUInt64 + (g (x != 0) || f true).toUInt64 * 3

def booleanPredicateJunctionNot (x y : UInt64) : UInt64 :=
  let saved := x == y
  let f := fun b : Bool => !b || x == 0
  (!(f saved && !(f false || saved))).toUInt64 + (f true || !saved).toUInt64

def booleanPredicateJunctionMixed (x y : UInt64) : UInt64 :=
  let word := fun n : UInt64 => n % 3 == 0
  let flag := fun b : Bool => b && y != 0
  (word x && flag (x / y == 0)).toUInt64 + (flag true || word y).toUInt64 * 3

def booleanPredicateJunctionArgument (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  (f (g (x == 0) && f false)).toUInt64 + (!(g (f true || g false))).toUInt64

def booleanPredicateJunctionBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  let g := fun b : Bool => (f b || f (!b)).toUInt64 == x
  (g (x == y) && f (g false)).toUInt64 + (f true || !(g false)).toUInt64

def booleanPredicateJunctionId (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => b && x != y
  let g := fun b : Bool => !b || x == 0
  let a ← pure (f true && g false).toUInt64
  let b ← pure (!(g (f false) || f (g true))).toUInt64
  return a + b

def rangeBooleanPredicateJunctionStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => !b && a != seed
    a := a + UInt64.ofNat i
    if (f (a % 7 == 0) && g (a == seed)).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateJunctionContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (!(f (UInt64.ofNat i % 3 == 0) || f (a == seed))).toUInt64 == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateJunctionOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let stop := count + (f false || g true).toUInt64
  let mut a := seed + (g false && f true).toUInt64
  for i in [:stop.toNat] do
    if (!(f (a % 7 == 0) && g (a == seed))).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (g (f (a == seed)) || f false).toUInt64

def rangeBooleanPredicateJunctionOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (!(f b && f (!b))).toUInt64 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (g b || f b).toUInt64 == 1 && a != seed
    if (h (a % 5 == 0) || g (a == seed)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(g (a == seed) && f true)).toUInt64

def booleanPredicateCompose (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  (f (g (x == y))).toUInt64 + (g (f false)).toUInt64 * 3

def booleanPredicateComposeRepeat (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == y
  (f (f (f (x != 0)))).toUInt64 + (f (f false)).toUInt64 * 3

def booleanPredicateComposeNot (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && y != 0
  let g := fun b : Bool => b || x == 0
  (!(f (!(g (x / y == 0))))).toUInt64 + (g (!(!(f true)))).toUInt64

def booleanPredicateComposeCapture (x y : UInt64) : UInt64 :=
  let saved := x != 0
  let f := fun b : Bool => saved || b
  let y := y + 1
  let g := fun b : Bool => b && x == y
  (f (g (x == y))).toUInt64 + (g (f false)).toUInt64 * 3

def booleanPredicateComposeBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  let g := fun b : Bool => (!(f (f b))).toUInt64 == x
  (g (f (x == y))).toUInt64 + (!(g (f false))).toUInt64

def booleanPredicateComposeId (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => b && x != y
  let g := fun b : Bool => !b || x == 0
  let a ← pure (f (g true)).toUInt64
  let b ← pure (!(g (f false))).toUInt64
  return a + b

def rangeBooleanPredicateComposeStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => !b && a != seed
    a := a + UInt64.ofNat i
    if (f (g (a % 7 == 0))).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateComposeContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (!(f (!(f (UInt64.ofNat i % 3 == 0))))).toUInt64 == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateComposeOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let stop := count + (f (g false)).toUInt64
  let mut a := seed + (g (f true)).toUInt64
  for i in [:stop.toNat] do
    if (!(f (g (a % 7 == 0)))).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (g (f (a == seed))).toUInt64

def rangeBooleanPredicateComposeOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (!(f (f b))).toUInt64 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (g (f b)).toUInt64 == 1 && a != seed
    if (h (g (a % 5 == 0))).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(g (f (a == seed)))).toUInt64

def booleanPredicateNot (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  (!(f (x == y))).toUInt64 + (!(f false)).toUInt64 * 3

def booleanPredicateNotTwice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == 0
  (!(!(f (x != y)))).toUInt64 + (!(f true)).toUInt64

def booleanPredicateNotThrice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && y != 0
  (!(!(!(f (x / y == 0))))).toUInt64 + (f (x == y)).toUInt64

def booleanPredicateNotCapture (x y : UInt64) : UInt64 :=
  let saved := x != 0
  let f := fun b : Bool => saved || b
  let y := y + 1
  (!(f (x == y))).toUInt64 + (f false).toUInt64 * 3

def booleanPredicateNotNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  let g := fun b : Bool => (!(f b)).toUInt64 == x
  (!(g (x == y))).toUInt64 + (!(!(g false))).toUInt64

def booleanPredicateNotId (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => b && x != y
  let a ← pure (!(f true)).toUInt64
  let b ← pure (!(!(f false))).toUInt64
  return a + b

def rangeBooleanPredicateNotStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    a := a + UInt64.ofNat i
    if (!(f (a % 7 == 0))).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateNotContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (!(!(!(f (UInt64.ofNat i % 3 == 0))))).toUInt64 == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateNotOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let stop := count + (!(f false)).toUInt64
  let mut a := seed + (!(!(f true))).toUInt64
  for i in [:stop.toNat] do
    if (!(f (a % 7 == 0))).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(!(!(f (a == seed))))).toUInt64

def rangeBooleanPredicateNotOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (!(f b)).toUInt64 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (!(g b)).toUInt64 == 1 && a != seed
    if (!(h (a % 5 == 0))).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(g (a == seed))).toUInt64

def rangeOuterBooleanPredicateBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let stop := count + (f false).toUInt64
  let mut a := seed + (f (count == 0)).toUInt64
  for i in [:stop.toNat] do
    if (f (a % 7 == 0)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (f (a == seed)).toUInt64

def rangeOuterBooleanPredicateCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let shift := fun n : UInt64 => n + seed
  let f := fun b : Bool => flag && (b || shift seed % 7 == 0)
  let mut a := seed
  for i in [:count.toNat] do
    if (f (UInt64.ofNat i % 3 == 0)).toUInt64 != 0 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a + (f false).toUInt64

def rangeOuterBooleanPredicateNested (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b
  let g := fun b : Bool => (f b).toUInt64 == 0
  let mut a := seed + 1
  for i in [:count.toNat] do
    let h := fun b : Bool => (g b).toUInt64 == 1 && a != seed
    if (h (a % 5 == 0)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (g (a == seed)).toUInt64

def rangeOuterBooleanPredicateShadow (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let saved := (f (count == 0)).toUInt64
  let f := fun b : Bool => saved != 0 || b
  let mut a := seed
  for i in [:count.toNat] do
    if (f (UInt64.ofNat i % 3 == 0)).toUInt64 == 1 then continue
    a := a * 3 + (f (a == seed)).toUInt64
  return a

def rangeOuterBooleanPredicateUnused (count seed : UInt64) : UInt64 := Id.run do
  let _f := fun b : Bool => b && count / seed == 0
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeOuterBooleanPredicateScalarHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => if (f (n % 7 == 0)).toUInt64 == 1 then n + seed else n * 3
  let mut a := seed
  for i in [:count.toNat] do
    a := g (a + UInt64.ofNat i)
    if (f (a % 7 == 0)).toUInt64 == 1 then break
  return g a

def rangeOuterBooleanPredicateId (count seed : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => b || count == 0
  let initial ← pure (seed + (f false).toUInt64)
  let mut a := initial
  for i in [:count.toNat] do
    let converted ← pure (f (a == seed)).toUInt64
    if converted == 1 then break
    a := a + UInt64.ofNat i
  return a + (f (a == count)).toUInt64

def rangeOuterBooleanPredicateStride (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let first := (f (seed % 5 == 0)).toUInt64
  let mut a := seed
  for i in [first.toNat:count.toNat:3] do
    a := a + UInt64.ofNat i
    if (f (a % 7 == 0)).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    a := a + UInt64.ofNat i
    if (f (a % 7 == 0)).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (f (UInt64.ofNat i % 3 == 0)).toUInt64 != 0 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let saved := a
    let flag := a != 0
    let f := fun b : Bool => flag && (b || saved % 11 == 0)
    a := a + UInt64.ofNat i
    if (f (a == saved)).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateNested (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun b : Bool => !b
    let g := fun b : Bool => (f b).toUInt64 == 0
    if (g (a % 5 == 0)).toUInt64 == 1 then pure (.done (a + 1))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def rangeBooleanPredicateStepHelper (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : Bool → Id (Id Bool) := fun b => b && a != 0
    let finish := fun n : UInt64 =>
      if (f (n % 7 == 0)).toUInt64 == 1 then ForInStep.done (n + a) else .yield (n * 3)
    finish (a + UInt64.ofNat i)

def rangeBooleanPredicateUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _f := fun b : Bool => b && a / seed == 0
    pure (.yield (a + UInt64.ofNat i))

def booleanPredicateTwice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  (f (x == y)).toUInt64 + (f (x != 0)).toUInt64 * 3

def booleanPredicateCapture (x y : UInt64) : UInt64 :=
  let flag := x != 0
  let f := fun b : Bool => flag && (b || x == y)
  (f false).toUInt64 + (f (x != y)).toUInt64 * 3

def booleanPredicateWordCapture (x y : UInt64) : UInt64 :=
  let wordPredicate := fun n : UInt64 => n == y
  let f := fun b : Bool => b && wordPredicate x
  (f true).toUInt64 + (f (wordPredicate y)).toUInt64

def booleanPredicateNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  let g := fun b : Bool => (f b).toUInt64 == x
  (g (x == y)).toUInt64 + (g false).toUInt64 * 3

def booleanPredicateScalarCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == 0
  let g := fun n : UInt64 => (f (n == y)).toUInt64 + n
  g x + g y

def booleanPredicateShadow (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let saved := (f false).toUInt64
  let f := fun b : Bool => b && saved != 0
  (f (x != 0)).toUInt64 + saved

def booleanPredicateDependent (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => if _h : x < y then b else !b
  if (f (x == y)).toUInt64 == 1 then x + 7 else y - 3

def booleanPredicateId (x y : UInt64) : UInt64 :=
  let f : Bool → Id (Id Bool) := fun b => b && x != y
  (f true).toUInt64 + (f false).toUInt64 * 3

def booleanPredicateUnused (x y : UInt64) : UInt64 :=
  let _f := fun b : Bool => b && x / y == 0
  x - y

def booleanPredicateDo (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b
  let a ← pure (f (x == y)).toUInt64
  let b ← pure (f (x / y == 0)).toUInt64
  return a + b

def boolWordBooleanHelper (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => !flag
  (f (x == y)).toUInt64

def predicateInputRepeated (x y : UInt64) : UInt64 :=
  let f : Id UInt64 → Bool := fun n => (show UInt64 from n) == y
  if f x || f (x + 1) then x + 7 else y - 3

def predicateInputNested (x y : UInt64) : UInt64 :=
  let f : Id (Id UInt64) → Id (Id Bool) := fun n => (show UInt64 from n) == y
  let g : Id UInt64 → Bool := fun n => !(f (show UInt64 from n)) && f ((show UInt64 from n) + 1)
  (g x).toUInt64 + (g y).toUInt64 * 3

def predicateInputCapture (x y : UInt64) : UInt64 :=
  let flag := x != 0
  let shift := fun n : UInt64 => n + y
  let f : Id (Id (Id UInt64)) → Bool := fun n => flag && shift (show UInt64 from n) != x
  (f x).toUInt64 + (f y).toUInt64 * 7

def predicateInputShadow (x y : UInt64) : UInt64 :=
  let f : Id UInt64 → Bool := fun n => (show UInt64 from n) == x
  let saved := f y
  let f : Id (Id UInt64) → Bool := fun n => saved || (show UInt64 from n) != y
  if f x && f y then x - y else x + y

def predicateInputUnused (x y : UInt64) : UInt64 :=
  let _f : Id (Id UInt64) → Id Bool := fun n => (show UInt64 from n) / y == x
  x - y

def predicateInputDo (x y : UInt64) : UInt64 := Id.run do
  let f : Id UInt64 → Bool := fun n => (show UInt64 from n) != y
  let a ← pure (f x)
  let b ← pure (f (x + 1))
  if a && b then return x + y else return x - y

def rangePredicateInputStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Id UInt64 → Bool := fun n => (show UInt64 from n) % 7 == 0
    a := a + UInt64.ofNat i
    if f a || f (a + 1) then break
  return a

def rangePredicateInputStepCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Id (Id UInt64) → Id Bool := fun n => (show UInt64 from n) == a
    let g : Id UInt64 → Bool := fun n => !(f (show UInt64 from n)) && f ((show UInt64 from n) + 1)
    if g (UInt64.ofNat i) then continue
    a := a + (g a).toUInt64 + UInt64.ofNat i
  return a

def rangePredicateInputOuter (count seed : UInt64) : UInt64 := Id.run do
  let f : Id (Id UInt64) → Bool := fun n => (show UInt64 from n) % 5 == 0
  let first := (f seed).toUInt64
  let mut a := seed
  for i in [first.toNat:count.toNat:3] do
    a := a + UInt64.ofNat i
    if f a || f (a + 1) then break
  return a + (f a).toUInt64

def rangePredicateInputOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let f : Id UInt64 → Id (Id Bool) := fun n => flag && (show UInt64 from n) == seed
  let g := fun n : UInt64 => if (show Bool from f n) then n + 1 else n * 3
  let mut a := seed
  for i in [:count.toNat] do
    a := g (a + UInt64.ofNat i)
    if (show Bool from f a) then break
  return g a

def rangeOuterPredicateBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n == seed
  let stop := count + (f 0).toUInt64
  let mut a := seed + (f count).toUInt64
  for i in [:stop.toNat] do
    if f a || f (UInt64.ofNat i) then break
    a := a + UInt64.ofNat i + 1
  return a + (f a).toUInt64

def rangeOuterPredicateCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let shift := fun n : UInt64 => n + seed
  let f := fun n : UInt64 => flag && shift n % 7 == 0
  let mut a := seed
  for i in [:count.toNat] do
    if f a && !f (UInt64.ofNat i) then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a + (f seed).toUInt64

def rangeOuterPredicateNested (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n == seed
  let g := fun n : UInt64 => f n || f (n + 1)
  let mut a := seed + 1
  for i in [:count.toNat] do
    let h := fun n : UInt64 => g n && !f (n + a)
    if h a || h (UInt64.ofNat i) then break
    a := a + UInt64.ofNat i + 1
  return a + (g a).toUInt64

def rangeOuterPredicateShadow (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n == seed
  let saved := f count
  let f := fun n : UInt64 => saved || n % 3 == 0
  let mut a := seed
  for i in [:count.toNat] do
    if f (UInt64.ofNat i) then continue
    a := a * 3 + (f a).toUInt64
  return a

def rangeOuterPredicateUnused (count seed : UInt64) : UInt64 := Id.run do
  let _f := fun n : UInt64 => n / seed == count
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeOuterPredicateScalarHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n % 7 == 0
  let g := fun n : UInt64 => if f n then n + seed else n * 3
  let mut a := seed
  for i in [:count.toNat] do
    a := g (a + UInt64.ofNat i)
    if f a then break
  return g a

def rangeOuterPredicateId (count seed : UInt64) : UInt64 := Id.run do
  let f : UInt64 → Id (Id Bool) := fun n => n != seed
  let initial ← pure (if (show Bool from f count) then seed + 1 else seed)
  let mut a := initial
  for i in [:count.toNat] do
    let flag ← pure (f a && f (UInt64.ofNat i))
    if flag then break
    a := a + UInt64.ofNat i
  return a + (f a).toUInt64

def rangeOuterPredicateStride (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n % 5 == 0
  let first := (f seed).toUInt64
  let mut a := seed
  for i in [first.toNat:count.toNat:3] do
    a := a + UInt64.ofNat i
    if f a || f (a + 1) then break
  return a

def rangeReusableBooleanBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n % 7 == 0
    a := a + UInt64.ofNat i
    if f a || f (a + 1) then break
  return a

def rangeReusableBooleanContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n % 3 == 0
    if f (UInt64.ofNat i) && !f a then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeReusableBooleanCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let saved := a
    let flag := a != 0
    let shift := fun n : UInt64 => n + saved
    let f := fun n : UInt64 => flag && shift n % 11 == 0
    a := a + UInt64.ofNat i
    if f a || f saved then break
  return a

def rangeReusableBooleanNested (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun n : UInt64 => n % 5 == 0
    let g := fun n : UInt64 => !f n && f (n + 1)
    if g a || g (UInt64.ofNat i) then pure (.done (a + 1))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def rangeReusableBooleanStepHelper (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → Id Bool := fun n => n % 7 == 0
    let finish := fun n : UInt64 =>
      if f n && !f (n + 1) then ForInStep.done (n + a) else .yield (n * 3)
    finish (a + UInt64.ofNat i)

def rangeReusableBooleanUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _f := fun n : UInt64 => n / a == seed
    pure (.yield (a + UInt64.ofNat i))

def reusableBooleanTwice (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n == y
  if f x || f (x + 1) then x + 7 else y - 3

def reusableBooleanCapture (x y : UInt64) : UInt64 :=
  let flag := x != 0
  let shift := fun n : UInt64 => n + y
  let f := fun n : UInt64 => flag && shift n != x
  (f x).toUInt64 + (f y).toUInt64 * 3

def reusableBooleanNested (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n == y
  let g := fun n : UInt64 => !f n && f (n + 1)
  if g x then (f y).toUInt64 + x else (g y).toUInt64 + y

def reusableBooleanScalarCapture (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n != y
  let g := fun n : UInt64 => if f n then n + 1 else n * 3
  g x + g y

def reusableBooleanShadow (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n == x
  let saved := f y
  let f := fun n : UInt64 => saved || n != y
  if f x && f y then x - y else x + y

def reusableBooleanDependent (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => if _h : n < y then n != x else n == y
  if _h : f x then (f y).toUInt64 + x else (f (x + 1)).toUInt64 + y

def reusableBooleanId (x y : UInt64) : UInt64 :=
  let f : UInt64 → Id (Id Bool) := fun n => n == y
  (f x).toUInt64 + (f (x + 1)).toUInt64

def reusableBooleanUnused (x y : UInt64) : UInt64 :=
  let _f := fun n : UInt64 => n / y == x
  x - y

def reusableBooleanIgnoredArgument (x y : UInt64) : UInt64 :=
  let f := fun _n : UInt64 => x == y
  (f (x / y)).toUInt64 + (f (y / x)).toUInt64

def reusableBooleanDo (x y : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n != y
  let a ← pure (f x)
  let b ← pure (f (x + 1))
  if a && b then return x + y else return x - y

def namedBooleanWord (x y : UInt64) : UInt64 :=
  if (let f : UInt64 → Bool := fun n => n == y; f x) then x + 1 else y * 3

def namedBooleanBool (x y : UInt64) : UInt64 :=
  (let f : Bool → Bool := fun b => !b || x == y; f (x != 0)).toUInt64 + y

def namedBooleanCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let shift := fun z : UInt64 => z + y
  (let f : UInt64 → Bool := fun n => outer && shift n == x; f (x + y)).toUInt64

def namedBooleanNested (x y : UInt64) : UInt64 :=
  (let f : UInt64 → Bool := fun n =>
     let g : Bool → Bool := fun b => b && n != y
     g (n == x)
   f (x + y)).toUInt64 + x

def namedBooleanDependent (x y : UInt64) : UInt64 :=
  (let f : UInt64 → Bool := fun n => if _h : n < y then n != x else n == y
   f (x + 1)).toUInt64

def namedBooleanId (x y : UInt64) : UInt64 :=
  (let f : Id UInt64 → Id Bool := fun n =>
     let g : Id Bool → Id Bool := fun b => !b &&
       !(@BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) n 0)
     g (@BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) n y)
   f (x + y)).toUInt64

def namedBooleanUnused (x y : UInt64) : UInt64 :=
  (let f : UInt64 → Bool := fun _n => x != y; f (x / y)).toUInt64

def namedBooleanDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (let f : UInt64 → Bool := fun n => n == y; f (x + 1))
  let next ← pure (let g : Bool → Bool := fun b => b || x != 0; g flag)
  if next then return x + y else return x - y

def rangeNamedBooleanBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
    if (let f : UInt64 → Bool := fun n => n % 7 == 0; f a) then break
  return a

def rangeNamedBooleanContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f : Bool → Bool := fun b => !b; f (UInt64.ofNat i % 3 == 0)) then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeNamedBooleanCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let flag :=
      let f : UInt64 → Bool := fun n =>
        let g : Bool → Bool := fun b => b && a != seed
        g (n % 7 == 0)
      f (UInt64.ofNat i)
    if flag then pure (.done (a + UInt64.ofNat i))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def booleanApplyWord (x y : UInt64) : UInt64 :=
  if (fun z : UInt64 => z == y) x then x + 1 else y * 3

def booleanApplyBool (x y : UInt64) : UInt64 :=
  ((fun flag : Bool => !flag || x == y) (x != 0)).toUInt64 + y

def booleanApplyCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun z : UInt64 => z + y
  ((fun n : UInt64 => outer && f n == x) (x + y)).toUInt64

def booleanApplyNested (x y : UInt64) : UInt64 :=
  ((fun n : UInt64 =>
    (fun flag : Bool => flag && n != y) (n == x)) (x + y)).toUInt64 + x

def booleanApplyDependent (x y : UInt64) : UInt64 :=
  ((fun n : UInt64 => if _h : n < y then n != x else n == y) (x + 1)).toUInt64

def booleanApplyId (x y : UInt64) : UInt64 :=
  ((fun n : Id UInt64 =>
    (fun flag : Id Bool => !flag && !(@BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) n 0))
      (@BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) n y)) (x + y)).toUInt64

def booleanApplyUnused (x y : UInt64) : UInt64 :=
  ((fun _n : UInt64 => x != y) (x / y)).toUInt64

def booleanApplyDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure ((fun n : UInt64 => n == y) (x + 1))
  let next ← pure ((fun b : Bool => b || x != 0) flag)
  if next then return x + y else return x - y

def rangeBooleanApplyBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
    if (fun n : UInt64 => n % 7 == 0) a then break
  return a

def rangeBooleanApplyContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (fun flag : Bool => !flag) (UInt64.ofNat i % 3 == 0) then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanApplyCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let flag := (fun n : UInt64 =>
      (fun b : Bool => b && a != seed) (n % 7 == 0)) (UInt64.ofNat i)
    if flag then pure (.done (a + UInt64.ofNat i))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def savedReannotatedDecide (x y : UInt64) : UInt64 :=
  let flag := @decide (@Eq (Id UInt64) ((x + y) % 7) (0))
    (instDecidableEqUInt64 ((x + y) % 7) (0))
  if flag then x + 1 else y * 3

def savedReannotatedNested (x y : UInt64) : UInt64 :=
  let flag := @decide ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
  if !(flag && (x == y)) then x ^^^ y else x + y

def savedReannotatedChoice (x y : UInt64) : UInt64 :=
  let flag := @ite Bool
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (x != 0) (y == 0)
  if flag then x + 1 else y * 3

def savedReannotatedDependentChoice (x y : UInt64) : UInt64 :=
  let flag := @dite Bool
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (fun _ => let other := x == 0; other || y != 0) (fun _ => let other := y == 0; other && x != 0)
  if flag then x + 1 else y * 3

def savedReannotatedDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (@decide ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0)))))
  if flag then return x + 1 else return y * 3

def savedReannotatedHelper (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 =>
    let flag := @decide (@LE.le (Id (Id UInt64)) instLEUInt64 (z + 1) (y * 3))
      (UInt64.decLe (z + 1) (y * 3))
    if flag then z + 1 else z * 3
  f x + f y

def savedReannotatedCaptured (x y : UInt64) : UInt64 :=
  let flag := @decide ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
  let f := fun z : UInt64 => if flag then z + x else z * y
  f x + f y

def savedReannotatedUnused (x y : UInt64) : UInt64 :=
  let _flag := @decide ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
  x + y

def rangeSavedReannotated (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := @decide (@LT.lt (Id (Id UInt64)) instLTUInt64 (UInt64.ofNat i + 1) (seed % 7))
      (UInt64.decLt (UInt64.ofNat i + 1) (seed % 7))
    if flag then continue
    a := a + UInt64.ofNat i + 1
    if a % 5 == 0 then break
  return a

def rangeSavedReannotatedChoice (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let flag := @ite Bool
      ((@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) ∧ (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)))
      (@instDecidableAnd (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0))
        (UInt64.decLe (seed % 7) (UInt64.ofNat i + 1)) (@instDecidableNot (@Eq (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 5) (0))))
      (a == 0) (seed != 0)
    if flag then pure (.done (a + UInt64.ofNat i))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def rangeSavedReannotatedDependentChoice (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let flag := @dite Bool
      ((@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) ∧ (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)))
      (@instDecidableAnd (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0))
        (UInt64.decLe (seed % 7) (UInt64.ofNat i + 1)) (@instDecidableNot (@Eq (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 5) (0))))
      (fun _ => a == 0) (fun _ => seed != 0)
    if flag then pure (.done (a + UInt64.ofNat i))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def dependentReannotatedEq (x y : UInt64) : UInt64 :=
  @dite UInt64
    (@Eq (Id UInt64) ((x + y) % 7) (0))
    (instDecidableEqUInt64 ((x + y) % 7) (0))
    (fun _ => x + 1) (fun _ => y * 3)

def dependentReannotatedOrder (x y : UInt64) : UInt64 :=
  @dite UInt64
    (@GE.ge (Id (Id UInt64)) instLEUInt64 (x >>> y) (y + 1))
    (UInt64.decLe (y + 1) (x >>> y))
    (fun _ => x + 1) (fun _ => y * 3)

def dependentReannotatedCompound (x y : UInt64) : UInt64 :=
  @dite UInt64
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (fun _ => let f := fun z : UInt64 => z + x; f y) (fun _ => y - x)

def dependentReannotatedNested (x y : UInt64) : UInt64 :=
  @dite UInt64
    (@Eq (Id UInt64) ((x + y) % 7) (0))
    (instDecidableEqUInt64 ((x + y) % 7) (0))
    (fun _ => @dite UInt64
    (@GE.ge (Id (Id UInt64)) instLEUInt64 (x >>> y) (y + 1))
    (UInt64.decLe (y + 1) (x >>> y))
    (fun _ => x ^^^ y) (fun _ => x * 7)) (fun _ => @dite UInt64
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (fun _ => x + y) (fun _ => y - x))

def dependentReannotatedHelper (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 =>
    @dite UInt64
      ((@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3)) ∧ (@Ne (Id (Id UInt64)) (z % 5) (0)))
      (@instDecidableAnd (@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3)) (@Ne (Id (Id UInt64)) (z % 5) (0))
        (UInt64.decLt (z + 1) (y * 3)) (@instDecidableNot (@Eq (Id (Id UInt64)) (z % 5) (0)) (instDecidableEqUInt64 (z % 5) (0))))
      (fun _ => z + 1) (fun _ => z * 3)
  f x + f y

def dependentReannotatedDo (x y : UInt64) : UInt64 := Id.run do
  let value ← @dite (Id UInt64)
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (fun _ => pure (x + 1)) (fun _ => pure (y * 3))
  return value + y

def rangeDependentReannotated (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @dite (Id (ForInStep UInt64))
      (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 11))
      (UInt64.decLe (seed % 11) (UInt64.ofNat i + 1))
      (fun _ => pure (.done (a + UInt64.ofNat i))) (fun _ => pure (.yield (a * 3 + UInt64.ofNat i)))

def rangeDependentReannotatedCompound (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @dite (Id (ForInStep UInt64))
      ((@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) ∧ (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)))
      (@instDecidableAnd (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0))
        (UInt64.decLe (seed % 7) (UInt64.ofNat i + 1)) (@instDecidableNot (@Eq (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 5) (0))))
      (fun _ => let value := a + UInt64.ofNat i; pure (.done value)) (fun _ => let value := a * 3 + UInt64.ofNat i; pure (.yield value))

def reannotatedAnd (x y : UInt64) : UInt64 :=
  @ite UInt64
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableAnd (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (instDecidableEqUInt64 ((x + y) % 5) (0)))
    (x + 1) (y * 3)

def reannotatedOr (x y : UInt64) : UInt64 :=
  @ite UInt64
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) (x ^^^ y) (y + 3)) (instDecidableEqUInt64 (x ^^^ y) (y + 3))))
    (x + 1) (y * 3)

def reannotatedGuardNegation (x y : UInt64) : UInt64 :=
  @ite UInt64
    (Not (Not ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)))))
    (@instDecidableNot (Not ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)))) (@instDecidableNot ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))) (@instDecidableAnd (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (instDecidableEqUInt64 ((x + y) % 5) (0)))))
    (x + 1) (y * 3)

def reannotatedNestedGuard (x y : UInt64) : UInt64 :=
  @ite UInt64
    (((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))) ∧ (Not (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3))))
    (@instDecidableAnd ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))) (Not (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3)))
      (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (instDecidableEqUInt64 ((x + y) % 5) (0))) (@instDecidableNot (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3)) (@instDecidableNot (@Eq (Id (Id UInt64)) (x ^^^ y) (y + 3)) (instDecidableEqUInt64 (x ^^^ y) (y + 3)))))
    (x + 1) (y * 3)

def reannotatedGuardHelper (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 =>
    @ite UInt64
      ((@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3)) ∨ (@Ne (Id (Id UInt64)) (z % 5) (0)))
      (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3)) (@Ne (Id (Id UInt64)) (z % 5) (0))
        (UInt64.decLt (z + 1) (y * 3)) (@instDecidableNot (@Eq (Id (Id UInt64)) (z % 5) (0)) (instDecidableEqUInt64 (z % 5) (0))))
      (z + 1) (z * 3)
  f x + f y

def reannotatedGuardDo (x y : UInt64) : UInt64 := Id.run do
  let value ← @ite (Id UInt64)
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableAnd (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (instDecidableEqUInt64 ((x + y) % 5) (0)))
    (pure (x + 1)) (pure (y * 3))
  return value + y

def rangeReannotatedAnd (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      ((@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) ∧ (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)))
      (@instDecidableAnd (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0))
        (UInt64.decLe (seed % 7) (UInt64.ofNat i + 1)) (@instDecidableNot (@Eq (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 5) (0))))
      (pure (.done (a + UInt64.ofNat i))) (pure (.yield (a * 3 + UInt64.ofNat i)))

def rangeReannotatedOr (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      ((@GT.gt (Id UInt64) instLTUInt64 (UInt64.ofNat i + 1) (seed % 11)) ∨ (@Eq (Id (Id UInt64)) ((a + UInt64.ofNat i) % 7) (0)))
      (@instDecidableOr (@GT.gt (Id UInt64) instLTUInt64 (UInt64.ofNat i + 1) (seed % 11)) (@Eq (Id (Id UInt64)) ((a + UInt64.ofNat i) % 7) (0))
        (UInt64.decLt (seed % 11) (UInt64.ofNat i + 1)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 7) (0)))
      (pure (.done (a + UInt64.ofNat i))) (pure (.yield (a * 3 + UInt64.ofNat i)))

def reannotatedEq (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq (Id UInt64) ((x + y) % 7) 0)
    (instDecidableEqUInt64 ((x + y) % 7) 0) (x + 1) (y + 3)

def reannotatedNe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Ne (Id (Id UInt64)) (x - y) (y * 3))
    (@instDecidableNot (@Eq (Id (Id UInt64)) (x - y) (y * 3))
      (instDecidableEqUInt64 (x - y) (y * 3))) (x - y) (y + 1)

def reannotatedLt (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LT.lt (Id UInt64) instLTUInt64 (x / y) (y % 7))
    (UInt64.decLt (x / y) (y % 7)) (x * 3) (y + 7)

def reannotatedLe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LE.le (Id (Id UInt64)) instLEUInt64 (x &&& y) (y ||| 3))
    (UInt64.decLe (x &&& y) (y ||| 3)) (x ^^^ y) (y / x)

def reannotatedGt (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GT.gt (Id UInt64) instLTUInt64 (x <<< y) (y ^^^ 5))
    (UInt64.decLt (y ^^^ 5) (x <<< y)) (x + y) (y - x)

def reannotatedGe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GE.ge (Id (Id UInt64)) instLEUInt64 (x >>> y) (y * 7))
    (UInt64.decLe (y * 7) (x >>> y)) (x % y) (y * 7)

def reannotatedNegated (x y : UInt64) : UInt64 :=
  @ite UInt64 (Not (Not (@LE.le (Id UInt64) instLEUInt64 (x + 1) (y * 7))))
    (@instDecidableNot (Not (@LE.le (Id UInt64) instLEUInt64 (x + 1) (y * 7)))
      (@instDecidableNot (@LE.le (Id UInt64) instLEUInt64 (x + 1) (y * 7))
        (UInt64.decLe (x + 1) (y * 7)))) (x + 11) (y - 13)

def reannotatedHelper (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 =>
    @ite UInt64 (@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3))
      (UInt64.decLt (z + 1) (y * 3)) (z + 1) (z * 3)
  f x + f y

def reannotatedDo (x y : UInt64) : UInt64 := Id.run do
  let value ← @ite (Id UInt64) (@Eq (Id (Id UInt64)) ((x + y) % 7) 0)
    (instDecidableEqUInt64 ((x + y) % 7) 0) (pure (x + 1)) (pure (y * 3))
  return value + y

def rangeReannotatedOrder (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 11))
      (UInt64.decLe (seed % 11) (UInt64.ofNat i + 1))
      (pure (.done (a + UInt64.ofNat i)))
      (pure (.yield (a * 3 + UInt64.ofNat i)))

def rangeIdComparisonEvidenceAnnotations (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      (@LT.lt (Id UInt64) instLTUInt64 (UInt64.ofNat i) (seed % 7))
      (UInt64.decLt (UInt64.ofNat i) (seed % 7))
      (pure (.yield a))
      (@ite (Id (ForInStep UInt64))
        (@Eq (Id (Id UInt64)) ((a + UInt64.ofNat i + 1) % 5) 0)
        (instDecidableEqUInt64 ((a + UInt64.ofNat i + 1) % 5) 0)
        (pure (.done (a + UInt64.ofNat i + 1)))
        (pure (.yield (a + UInt64.ofNat i + 1))))


def idComparisonEq (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq (Id UInt64) x y) (instDecidableEqUInt64 x y) (x + 1) (y + 3)

def idComparisonNe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Ne (Id (Id UInt64)) x y)
    (@instDecidableNot (@Eq (Id (Id UInt64)) x y) (instDecidableEqUInt64 x y)) (x - y) (y + 1)

def idComparisonLt (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LT.lt (Id UInt64) instLTUInt64 x y) (UInt64.decLt x y) (x * 3) (y + 7)

def idComparisonLe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LE.le (Id (Id UInt64)) instLEUInt64 x y) (UInt64.decLe x y) (x ^^^ y) (y / x)

def idComparisonGt (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GT.gt (Id UInt64) instLTUInt64 x y) (UInt64.decLt y x) (x + y) (y - x)

def idComparisonGe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GE.ge (Id (Id UInt64)) instLEUInt64 x y) (UInt64.decLe y x) (x % y) (y * 7)

def rangeIdComparisonExit (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      (@LT.lt (Id UInt64) instLTUInt64 (UInt64.ofNat i) (seed % 7 : UInt64))
      (UInt64.decLt (UInt64.ofNat i) (seed % 7))
      (pure (.yield a))
      (@ite (Id (ForInStep UInt64))
        (@Eq (Id (Id UInt64)) ((a + UInt64.ofNat i + 1) % 5 : UInt64) (0 : UInt64))
        (instDecidableEqUInt64 ((a + UInt64.ofNat i + 1) % 5) 0)
        (pure (.done (a + UInt64.ofNat i + 1)))
        (pure (.yield (a + UInt64.ofNat i + 1))))

def idComparisonNegated (x y : UInt64) : UInt64 :=
  @ite UInt64 (Not (@LE.le (Id (Id (Id UInt64))) instLEUInt64 x y))
    (@instDecidableNot (@LE.le (Id (Id (Id UInt64))) instLEUInt64 x y) (UInt64.decLe x y))
    (x + 11) (y - 13)

def idComparisonCompound (x y : UInt64) : UInt64 :=
  @ite UInt64 ((@Eq (Id UInt64) x y) ∨ (@LT.lt (Id (Id UInt64)) instLTUInt64 x y))
    (@instDecidableOr (@Eq (Id UInt64) x y) (@LT.lt (Id (Id UInt64)) instLTUInt64 x y)
      (instDecidableEqUInt64 x y) (UInt64.decLt x y)) (x * 3) (y / x)

def idComparisonDependent (x y : UInt64) : UInt64 :=
  @dite UInt64 (@Eq (Id (Id UInt64)) x y) (instDecidableEqUInt64 x y)
    (fun _ => let f := fun z : UInt64 => z + x; f y)
    (fun _ => y - x)

def idComparisonDecide (x y : UInt64) : UInt64 :=
  let flag := @decide (@GE.ge (Id UInt64) instLEUInt64 x y) (UInt64.decLe y x)
  if flag then x + 17 else y + 19

def idComparisonChoice (x y : UInt64) : UInt64 :=
  let flag := @ite Bool (@Eq (Id UInt64) x y) (instDecidableEqUInt64 x y) (x != 0) (y == 0)
  if flag then x ^^^ y else x * 7

def idComparisonDo (x y : UInt64) : UInt64 := Id.run do
  let f := fun z : UInt64 =>
    @ite UInt64 (@LT.lt (Id UInt64) instLTUInt64 z y) (UInt64.decLt z y) (z + 1) (z * 3)
  let value ← @ite (Id UInt64) (@Eq (Id (Id UInt64)) x y) (instDecidableEqUInt64 x y)
    (pure (f x)) (pure (f (x + y)))
  return value + f y

def rangeIdComparisonDecide (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := @decide (@LT.lt (Id (Id UInt64)) instLTUInt64 (UInt64.ofNat i) (seed % 7 : UInt64))
      (UInt64.decLt (UInt64.ofNat i) (seed % 7))
    if flag then continue
    a := a + UInt64.ofNat i + 1
    if a % 5 == 0 then break
  return a

def rangeIdComparisonDependent (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @dite (Id (ForInStep UInt64)) (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i) (seed % 11 : UInt64))
      (UInt64.decLe (seed % 11) (UInt64.ofNat i))
      (fun _ => pure (.done (a + UInt64.ofNat i)))
      (fun _ => pure (.yield (a * 3 + UInt64.ofNat i)))

def rangeInputs : List (UInt64 × UInt64) :=
  [0, 1, 2, 7, 16, 31].flatMap fun count =>
    [0, 1, 0x8000000000000000, 0xffffffffffffffff].map fun seed => (count, seed)

def rangeCases : List (String × (UInt64 → UInt64 → UInt64)) :=
  [
   ("rangeBooleanPredicateLoopLetBreak", rangeBooleanPredicateLoopLetBreak),
   ("rangeBooleanPredicateLoopLetContinue", rangeBooleanPredicateLoopLetContinue),
   ("rangeBooleanPredicateLoopLetChoice", rangeBooleanPredicateLoopLetChoice),
   ("rangeBooleanPredicateLoopLetCapture", rangeBooleanPredicateLoopLetCapture),
   ("rangeBooleanPredicateOuterLetBounds", rangeBooleanPredicateOuterLetBounds),
   ("rangeBooleanPredicateOuterLetCapture", rangeBooleanPredicateOuterLetCapture),
   ("rangeBooleanPredicateOuterLetChoice", rangeBooleanPredicateOuterLetChoice),
   ("rangeBooleanPredicateOuterLetId", rangeBooleanPredicateOuterLetId),
   ("rangeBooleanPredicateConditionBreak", rangeBooleanPredicateConditionBreak),
   ("rangeBooleanPredicateConditionSkip", rangeBooleanPredicateConditionSkip),
   ("rangeBooleanPredicateConditionEq", rangeBooleanPredicateConditionEq),
   ("rangeBooleanPredicateConditionNe", rangeBooleanPredicateConditionNe),
   ("rangeBooleanPredicateConditionProof", rangeBooleanPredicateConditionProof),
   ("rangeBooleanPredicateConditionOuterBreak", rangeBooleanPredicateConditionOuterBreak),
   ("rangeBooleanPredicateConditionNestedStep", rangeBooleanPredicateConditionNestedStep),
   ("rangeBooleanPredicateConditionIdStep", rangeBooleanPredicateConditionIdStep),
   ("rangeBooleanPredicateLoopBindBreak", rangeBooleanPredicateLoopBindBreak),
   ("rangeBooleanPredicateLoopBindContinue", rangeBooleanPredicateLoopBindContinue),
   ("rangeBooleanPredicateLoopBindChoice", rangeBooleanPredicateLoopBindChoice),
   ("rangeBooleanPredicateLoopBindCapture", rangeBooleanPredicateLoopBindCapture),
   ("rangeBooleanPredicateOuterBindBounds", rangeBooleanPredicateOuterBindBounds),
   ("rangeBooleanPredicateOuterBindCapture", rangeBooleanPredicateOuterBindCapture),
   ("rangeBooleanPredicateOuterBindChoice", rangeBooleanPredicateOuterBindChoice),
   ("rangeBooleanPredicateOuterBindDirect", rangeBooleanPredicateOuterBindDirect),
   ("rangeNatAliasStep", rangeNatAliasStep),
   ("rangeNatAliasCondition", rangeNatAliasCondition),
   ("rangeNatAliasCapture", rangeNatAliasCapture),
   ("rangeNatAliasPredicateResult", rangeNatAliasPredicateResult),
   ("rangeBooleanBoundResultStep", rangeBooleanBoundResultStep),
   ("rangeBooleanBoundResultCondition", rangeBooleanBoundResultCondition),
   ("rangeBooleanBoundResultOuter", rangeBooleanBoundResultOuter),
   ("rangeBooleanBoundResultHelper", rangeBooleanBoundResultHelper),
   ("rangeBooleanWordBoundResultStep", rangeBooleanWordBoundResultStep),
   ("rangeBooleanWordBoundResultCondition", rangeBooleanWordBoundResultCondition),
   ("rangeBooleanWordBoundResultOuter", rangeBooleanWordBoundResultOuter),
   ("rangeBooleanWordBoundResultHelper", rangeBooleanWordBoundResultHelper),
   ("rangeBooleanResultBindStep", rangeBooleanResultBindStep),
   ("rangeBooleanResultBindCondition", rangeBooleanResultBindCondition),
   ("rangeBooleanResultBindOuter", rangeBooleanResultBindOuter),
   ("rangeBooleanResultBindHelper", rangeBooleanResultBindHelper),
   ("rangeSavedMixedStep", rangeSavedMixedStep),
   ("rangeSavedMixedContinue", rangeSavedMixedContinue),
   ("rangeSavedMixedOuter", rangeSavedMixedOuter),
   ("rangeSavedMixedHelper", rangeSavedMixedHelper),
   ("rangeCallMixedStep", rangeCallMixedStep),
   ("rangeCallMixedContinue", rangeCallMixedContinue),
   ("rangeCallMixedOuter", rangeCallMixedOuter),
   ("rangeCallMixedHelper", rangeCallMixedHelper),
   ("rangeExtendedMixedStep", rangeExtendedMixedStep),
   ("rangeExtendedMixedContinue", rangeExtendedMixedContinue),
   ("rangeExtendedMixedOuter", rangeExtendedMixedOuter),
   ("rangeExtendedMixedHelper", rangeExtendedMixedHelper),
   ("rangePropositionLetStep", rangePropositionLetStep),
   ("rangePropositionLetContinue", rangePropositionLetContinue),
   ("rangePropositionLetOuter", rangePropositionLetOuter),
   ("rangePropositionLetHelper", rangePropositionLetHelper),
   ("rangeDecisionLetStep", rangeDecisionLetStep),
   ("rangeDecisionLetContinue", rangeDecisionLetContinue),
   ("rangeDecisionLetOuter", rangeDecisionLetOuter),
   ("rangeDecisionLetHelper", rangeDecisionLetHelper),
   ("rangeLocalNotStep", rangeLocalNotStep),
   ("rangeLocalNotContinue", rangeLocalNotContinue),
   ("rangeLocalNotOuter", rangeLocalNotOuter),
   ("rangeLocalNotHelper", rangeLocalNotHelper),
   ("rangeBoolWordHelperRepeat", (fun (x y : UInt64) => (rangeBoolWordHelperRepeat x y).toUInt64)),
   ("rangeBoolWordHelperCount", (fun (x y : UInt64) => (rangeBoolWordHelperCount x y).toUInt64)),
   ("rangeBoolWordHelperInitial", (fun (x y : UInt64) => (rangeBoolWordHelperInitial x y).toUInt64)),
   ("rangeBoolWordHelperNested", (fun (x y : UInt64) => (rangeBoolWordHelperNested x y).toUInt64)),
   ("rangeBoolWordHelperFlag", (fun (x y : UInt64) => (rangeBoolWordHelperFlag x (y != 0)).toUInt64)),
   ("rangeBoolWordHelperExit", (fun (x y : UInt64) => (rangeBoolWordHelperExit x y).toUInt64)),
   ("rangeBoolWordHelperContinue", (fun (x y : UInt64) => (rangeBoolWordHelperContinue x y).toUInt64)),
   ("rangeBoolWordHelperStride", (fun (x y : UInt64) => (rangeBoolWordHelperStride x y).toUInt64)),
   ("rangeBoolWordHelperId", (fun (x y : UInt64) => (rangeBoolWordHelperId x y).toUInt64)),
   ("rangeBoolWordHelperShadow", (fun (x y : UInt64) => (rangeBoolWordHelperShadow x y).toUInt64)),
   ("rangeBoolBooleanHelperRepeat", (fun (x y : UInt64) => (rangeBoolBooleanHelperRepeat x y).toUInt64)),
   ("rangeBoolBooleanHelperCount", (fun (x y : UInt64) => (rangeBoolBooleanHelperCount x y).toUInt64)),
   ("rangeBoolBooleanHelperInitial", (fun (x y : UInt64) => (rangeBoolBooleanHelperInitial x y).toUInt64)),
   ("rangeBoolBooleanHelperNested", (fun (x y : UInt64) => (rangeBoolBooleanHelperNested x y).toUInt64)),
   ("rangeBoolBooleanHelperFlag", (fun (x y : UInt64) => (rangeBoolBooleanHelperFlag x (y != 0)).toUInt64)),
   ("rangeBoolBooleanHelperExit", (fun (x y : UInt64) => (rangeBoolBooleanHelperExit x y).toUInt64)),
   ("rangeBoolBooleanHelperContinue", (fun (x y : UInt64) => (rangeBoolBooleanHelperContinue x y).toUInt64)),
   ("rangeBoolBooleanHelperStride", (fun (x y : UInt64) => (rangeBoolBooleanHelperStride x y).toUInt64)),
   ("rangeBoolBooleanHelperId", (fun (x y : UInt64) => (rangeBoolBooleanHelperId x y).toUInt64)),
   ("rangeBoolBooleanHelperShadow", (fun (x y : UInt64) => (rangeBoolBooleanHelperShadow x y).toUInt64)),
   ("rangeBoolPredicateHelperRepeat", (fun (x y : UInt64) => (rangeBoolPredicateHelperRepeat x y).toUInt64)),
   ("rangeBoolPredicateHelperCount", (fun (x y : UInt64) => (rangeBoolPredicateHelperCount x y).toUInt64)),
   ("rangeBoolPredicateHelperNested", (fun (x y : UInt64) => (rangeBoolPredicateHelperNested x y).toUInt64)),
   ("rangeBoolPredicateHelperExit", (fun (x y : UInt64) => (rangeBoolPredicateHelperExit x y).toUInt64)),
   ("rangeBoolPredicateHelperId", (fun (x y : UInt64) => (rangeBoolPredicateHelperId x y).toUInt64)),
   ("rangeBoolBooleanPredicateHelperRepeat", (fun (x y : UInt64) => (rangeBoolBooleanPredicateHelperRepeat x y).toUInt64)),
   ("rangeBoolBooleanPredicateHelperFlag", (fun (x y : UInt64) => (rangeBoolBooleanPredicateHelperFlag x (y != 0)).toUInt64)),
   ("rangeBoolBooleanPredicateHelperNested", (fun (x y : UInt64) => (rangeBoolBooleanPredicateHelperNested x y).toUInt64)),
   ("rangeBoolBooleanPredicateHelperStride", (fun (x y : UInt64) => (rangeBoolBooleanPredicateHelperStride x y).toUInt64)),
   ("rangeBoolBooleanPredicateHelperId", (fun (x y : UInt64) => (rangeBoolBooleanPredicateHelperId x y).toUInt64)),
   ("rangeBoolHelperInputIdWord", (fun (x y : UInt64) => (rangeBoolHelperInputIdWord x y).toUInt64)),
   ("rangeBoolHelperInputIdBooleanWord", (fun (x y : UInt64) => (rangeBoolHelperInputIdBooleanWord x y).toUInt64)),
   ("rangeBoolHelperInputIdPredicate", (fun (x y : UInt64) => (rangeBoolHelperInputIdPredicate x y).toUInt64)),
   ("rangeBoolHelperInputIdBooleanPredicate", (fun (x y : UInt64) => (rangeBoolHelperInputIdBooleanPredicate x (y != 0)).toUInt64)),
   ("rangeBoolHelperInputIdRepeated", (fun (x y : UInt64) => (rangeBoolHelperInputIdRepeated x y).toUInt64)),
   ("rangeBoolHelperInputIdBound", (fun (x y : UInt64) => (rangeBoolHelperInputIdBound x y).toUInt64)),
   ("rangeBoolHelperInputIdExit", (fun (x y : UInt64) => (rangeBoolHelperInputIdExit x y).toUInt64)),
   ("rangeBoolHelperInputIdContinue", (fun (x y : UInt64) => (rangeBoolHelperInputIdContinue x y).toUInt64)),
   ("rangeBoolHelperInputIdMixed", (fun (x y : UInt64) => (rangeBoolHelperInputIdMixed x y).toUInt64)),
   ("rangeBoolHelperInputIdShadow", (fun (x y : UInt64) => (rangeBoolHelperInputIdShadow x y).toUInt64)),
   ("rangeBoolManyHelperBinaryRepeat", (fun (x y : UInt64) => (rangeBoolManyHelperBinaryRepeat x y).toUInt64)),
   ("rangeBoolManyHelperBinaryCount", (fun (x y : UInt64) => (rangeBoolManyHelperBinaryCount x y).toUInt64)),
   ("rangeBoolManyHelperTernaryInitial", (fun (x y : UInt64) => (rangeBoolManyHelperTernaryInitial x y).toUInt64)),
   ("rangeBoolManyHelperTernaryNested", (fun (x y : UInt64) => (rangeBoolManyHelperTernaryNested x y).toUInt64)),
   ("rangeBoolManyHelperFiveFlag", (fun (x y : UInt64) => (rangeBoolManyHelperFiveFlag x (y != 0)).toUInt64)),
   ("rangeBoolManyHelperBinaryExit", (fun (x y : UInt64) => (rangeBoolManyHelperBinaryExit x y).toUInt64)),
   ("rangeBoolManyHelperTernaryContinue", (fun (x y : UInt64) => (rangeBoolManyHelperTernaryContinue x y).toUInt64)),
   ("rangeBoolManyHelperFiveStride", (fun (x y : UInt64) => (rangeBoolManyHelperFiveStride x y).toUInt64)),
   ("rangeBoolManyHelperFiveId", (fun (x y : UInt64) => (rangeBoolManyHelperFiveId x y).toUInt64)),
   ("rangeBoolManyHelperBinaryShadow", (fun (x y : UInt64) => (rangeBoolManyHelperBinaryShadow x y).toUInt64)),
   ("rangeBoolUnitHelperRepeat", (fun (x y : UInt64) => (rangeBoolUnitHelperRepeat x y).toUInt64)),
   ("rangeBoolUnitHelperCount", (fun (x y : UInt64) => (rangeBoolUnitHelperCount x y).toUInt64)),
   ("rangeBoolUnitHelperInitial", (fun (x y : UInt64) => (rangeBoolUnitHelperInitial x y).toUInt64)),
   ("rangeBoolUnitHelperNested", (fun (x y : UInt64) => (rangeBoolUnitHelperNested x y).toUInt64)),
   ("rangeBoolUnitHelperFlag", (fun (x y : UInt64) => (rangeBoolUnitHelperFlag x (y != 0)).toUInt64)),
   ("rangeBoolUnitHelperExit", (fun (x y : UInt64) => (rangeBoolUnitHelperExit x y).toUInt64)),
   ("rangeBoolUnitHelperContinue", (fun (x y : UInt64) => (rangeBoolUnitHelperContinue x y).toUInt64)),
   ("rangeBoolUnitHelperStride", (fun (x y : UInt64) => (rangeBoolUnitHelperStride x y).toUInt64)),
   ("rangeBoolUnitHelperId", (fun (x y : UInt64) => (rangeBoolUnitHelperId x y).toUInt64)),
   ("rangeBoolUnitHelperShadow", (fun (x y : UInt64) => (rangeBoolUnitHelperShadow x y).toUInt64)),
   ("rangeBoolOuterConditionEqual", (fun (x y : UInt64) => (rangeBoolOuterConditionEqual x y).toUInt64)),
   ("rangeBoolOuterConditionOrder", (fun (x y : UInt64) => (rangeBoolOuterConditionOrder x y).toUInt64)),
   ("rangeBoolOuterConditionFlag", (fun (x y : UInt64) => (rangeBoolOuterConditionFlag x (y != 0)).toUInt64)),
   ("rangeBoolOuterConditionNested", (fun (x y : UInt64) => (rangeBoolOuterConditionNested x y).toUInt64)),
   ("rangeBoolOuterConditionHelper", (fun (x y : UInt64) => (rangeBoolOuterConditionHelper x y).toUInt64)),
   ("rangeBoolOuterConditionExit", (fun (x y : UInt64) => (rangeBoolOuterConditionExit x y).toUInt64)),
   ("rangeBoolOuterConditionContinue", (fun (x y : UInt64) => (rangeBoolOuterConditionContinue x y).toUInt64)),
   ("rangeBoolOuterConditionStride", (fun (x y : UInt64) => (rangeBoolOuterConditionStride x y).toUInt64)),
   ("rangeBoolOuterConditionId", (fun (x y : UInt64) => (rangeBoolOuterConditionId x y).toUInt64)),
   ("rangeBoolOuterConditionCapture", (fun (x y : UInt64) => (rangeBoolOuterConditionCapture x y).toUInt64)),
   ("rangeBoolMixedConditionScalarLeft", (fun (x y : UInt64) => (rangeBoolMixedConditionScalarLeft x y).toUInt64)),
   ("rangeBoolMixedConditionScalarRight", (fun (x y : UInt64) => (rangeBoolMixedConditionScalarRight x y).toUInt64)),
   ("rangeBoolMixedConditionFlag", (fun (x y : UInt64) => (rangeBoolMixedConditionFlag x (y != 0)).toUInt64)),
   ("rangeBoolMixedConditionNested", (fun (x y : UInt64) => (rangeBoolMixedConditionNested x y).toUInt64)),
   ("rangeBoolMixedConditionHelper", (fun (x y : UInt64) => (rangeBoolMixedConditionHelper x y).toUInt64)),
   ("rangeBoolMixedConditionBooleanHelper", (fun (x y : UInt64) => (rangeBoolMixedConditionBooleanHelper x y).toUInt64)),
   ("rangeBoolMixedConditionContinue", (fun (x y : UInt64) => (rangeBoolMixedConditionContinue x y).toUInt64)),
   ("rangeBoolMixedConditionStride", (fun (x y : UInt64) => (rangeBoolMixedConditionStride x y).toUInt64)),
   ("rangeBoolMixedConditionId", (fun (x y : UInt64) => (rangeBoolMixedConditionId x y).toUInt64)),
   ("rangeBoolMixedConditionCapture", (fun (x y : UInt64) => (rangeBoolMixedConditionCapture x y).toUInt64)),
   ("rangeBoolDirectWord", (fun (x y : UInt64) => (rangeBoolDirectWord x y).toUInt64)),
   ("rangeBoolDirectFlag", (fun (x y : UInt64) => (rangeBoolDirectFlag x (y != 0)).toUInt64)),
   ("rangeBoolDirectBooleanArgument", (fun (x y : UInt64) => (rangeBoolDirectBooleanArgument x y).toUInt64)),
   ("rangeBoolDirectWordCapture", (fun (x y : UInt64) => (rangeBoolDirectWordCapture x y).toUInt64)),
   ("rangeBoolDirectBooleanCapture", (fun (x y : UInt64) => (rangeBoolDirectBooleanCapture x y).toUInt64)),
   ("rangeBoolDirectNested", (fun (x y : UInt64) => (rangeBoolDirectNested x y).toUInt64)),
   ("rangeBoolDirectExit", (fun (x y : UInt64) => (rangeBoolDirectExit x y).toUInt64)),
   ("rangeBoolDirectContinue", (fun (x y : UInt64) => (rangeBoolDirectContinue x y).toUInt64)),
   ("rangeBoolDirectStride", (fun (x y : UInt64) => (rangeBoolDirectStride x y).toUInt64)),
   ("rangeBoolDirectId", (fun (x y : UInt64) => (rangeBoolDirectId x y).toUInt64)),
   ("rangeBoolWrappedCallWord", (fun (x y : UInt64) => (rangeBoolWrappedCallWord x y).toUInt64)),
   ("rangeBoolWrappedCallFlag", (fun (x y : UInt64) => (rangeBoolWrappedCallFlag x (y != 0)).toUInt64)),
   ("rangeBoolWrappedCallBooleanArgument", (fun (x y : UInt64) => (rangeBoolWrappedCallBooleanArgument x y).toUInt64)),
   ("rangeBoolWrappedCallWordCapture", (fun (x y : UInt64) => (rangeBoolWrappedCallWordCapture x y).toUInt64)),
   ("rangeBoolWrappedCallBooleanCapture", (fun (x y : UInt64) => (rangeBoolWrappedCallBooleanCapture x y).toUInt64)),
   ("rangeBoolWrappedCallNested", (fun (x y : UInt64) => (rangeBoolWrappedCallNested x y).toUInt64)),
   ("rangeBoolWrappedCallExit", (fun (x y : UInt64) => (rangeBoolWrappedCallExit x y).toUInt64)),
   ("rangeBoolWrappedCallContinue", (fun (x y : UInt64) => (rangeBoolWrappedCallContinue x y).toUInt64)),
   ("rangeBoolWrappedCallStride", (fun (x y : UInt64) => (rangeBoolWrappedCallStride x y).toUInt64)),
   ("rangeBoolWrappedCallId", (fun (x y : UInt64) => (rangeBoolWrappedCallId x y).toUInt64)),
   ("rangeBoolForwardedWord", (fun (x y : UInt64) => (rangeBoolForwardedWord x y).toUInt64)),
   ("rangeBoolForwardedFlag", (fun (x y : UInt64) => (rangeBoolForwardedFlag x (y != 0)).toUInt64)),
   ("rangeBoolForwardedBooleanArgument", (fun (x y : UInt64) => (rangeBoolForwardedBooleanArgument x y).toUInt64)),
   ("rangeBoolForwardedWordCapture", (fun (x y : UInt64) => (rangeBoolForwardedWordCapture x y).toUInt64)),
   ("rangeBoolForwardedBooleanCapture", (fun (x y : UInt64) => (rangeBoolForwardedBooleanCapture x y).toUInt64)),
   ("rangeBoolForwardedNested", (fun (x y : UInt64) => (rangeBoolForwardedNested x y).toUInt64)),
   ("rangeBoolForwardedExit", (fun (x y : UInt64) => (rangeBoolForwardedExit x y).toUInt64)),
   ("rangeBoolForwardedContinue", (fun (x y : UInt64) => (rangeBoolForwardedContinue x y).toUInt64)),
   ("rangeBoolForwardedStride", (fun (x y : UInt64) => (rangeBoolForwardedStride x y).toUInt64)),
   ("rangeBoolForwardedId", (fun (x y : UInt64) => (rangeBoolForwardedId x y).toUInt64)),
   ("rangeBoolConditionalCallSaved", (fun (x y : UInt64) => (rangeBoolConditionalCallSaved x y).toUInt64)),
   ("rangeBoolConditionalCallNested", (fun (x y : UInt64) => (rangeBoolConditionalCallNested x y).toUInt64)),
   ("rangeBoolConditionalCallExit", (fun (x y : UInt64) => (rangeBoolConditionalCallExit x y).toUInt64)),
   ("rangeBoolConditionalCallContinue", (fun (x y : UInt64) => (rangeBoolConditionalCallContinue x y).toUInt64)),
   ("rangeBoolConditionalCallCapture", (fun (x y : UInt64) => (rangeBoolConditionalCallCapture x y).toUInt64)),
   ("rangeBoolConditionalCallHelper", (fun (x y : UInt64) => (rangeBoolConditionalCallHelper x y).toUInt64)),
   ("rangeBoolConditionalCallFlag", (fun (x y : UInt64) => (rangeBoolConditionalCallFlag x (y != 0)).toUInt64)),
   ("rangeBoolConditionalCallStride", (fun (x y : UInt64) => (rangeBoolConditionalCallStride x y).toUInt64)),
   ("rangeBoolConditionalCallWord", (fun (x y : UInt64) => (rangeBoolConditionalCallWord x y).toUInt64)),
   ("rangeBoolConditionalCallId", (fun (x y : UInt64) => (rangeBoolConditionalCallId x y).toUInt64)),
   ("rangeBoolSavedCallWord", (fun (x y : UInt64) => (rangeBoolSavedCallWord x y).toUInt64)),
   ("rangeBoolSavedCallFlag", (fun (x y : UInt64) => (rangeBoolSavedCallFlag x (y != 0)).toUInt64)),
   ("rangeBoolSavedCallBooleanArgument", (fun (x y : UInt64) => (rangeBoolSavedCallBooleanArgument x y).toUInt64)),
   ("rangeBoolSavedCallWordCapture", (fun (x y : UInt64) => (rangeBoolSavedCallWordCapture x y).toUInt64)),
   ("rangeBoolSavedCallBooleanCapture", (fun (x y : UInt64) => (rangeBoolSavedCallBooleanCapture x y).toUInt64)),
   ("rangeBoolSavedCallNested", (fun (x y : UInt64) => (rangeBoolSavedCallNested x y).toUInt64)),
   ("rangeBoolSavedCallExit", (fun (x y : UInt64) => (rangeBoolSavedCallExit x y).toUInt64)),
   ("rangeBoolSavedCallContinue", (fun (x y : UInt64) => (rangeBoolSavedCallContinue x y).toUInt64)),
   ("rangeBoolSavedCallStride", (fun (x y : UInt64) => (rangeBoolSavedCallStride x y).toUInt64)),
   ("rangeBoolSavedCallId", (fun (x y : UInt64) => (rangeBoolSavedCallId x y).toUInt64)),
   ("rangeBoolWrappedChoiceWord", (fun (x y : UInt64) => (rangeBoolWrappedChoiceWord x y).toUInt64)),
   ("rangeBoolWrappedChoiceFlag", (fun (x y : UInt64) => (rangeBoolWrappedChoiceFlag x (y != 0)).toUInt64)),
   ("rangeBoolWrappedChoiceBooleanArgument", (fun (x y : UInt64) => (rangeBoolWrappedChoiceBooleanArgument x y).toUInt64)),
   ("rangeBoolWrappedChoiceWordCapture", (fun (x y : UInt64) => (rangeBoolWrappedChoiceWordCapture x y).toUInt64)),
   ("rangeBoolWrappedChoiceBooleanCapture", (fun (x y : UInt64) => (rangeBoolWrappedChoiceBooleanCapture x y).toUInt64)),
   ("rangeBoolWrappedChoiceNested", (fun (x y : UInt64) => (rangeBoolWrappedChoiceNested x y).toUInt64)),
   ("rangeBoolWrappedChoiceExit", (fun (x y : UInt64) => (rangeBoolWrappedChoiceExit x y).toUInt64)),
   ("rangeBoolWrappedChoiceContinue", (fun (x y : UInt64) => (rangeBoolWrappedChoiceContinue x y).toUInt64)),
   ("rangeBoolWrappedChoiceStride", (fun (x y : UInt64) => (rangeBoolWrappedChoiceStride x y).toUInt64)),
   ("rangeBoolWrappedChoiceId", (fun (x y : UInt64) => (rangeBoolWrappedChoiceId x y).toUInt64)),
   ("rangeBoolResultLet", (fun (x y : UInt64) => (rangeBoolResultLet x y).toUInt64)),
   ("rangeBoolResultDo", (fun (x y : UInt64) => (rangeBoolResultDo x y).toUInt64)),
   ("rangeBoolResultFlag", (fun (x y : UInt64) => (rangeBoolResultFlag x (y != 0)).toUInt64)),
   ("rangeBoolResultCapture", (fun (x y : UInt64) => (rangeBoolResultCapture x y).toUInt64)),
   ("rangeBoolResultSaved", (fun (x y : UInt64) => (rangeBoolResultSaved x y).toUInt64)),
   ("rangeBoolResultMixed", (fun (x y : UInt64) => (rangeBoolResultMixed x y).toUInt64)),
   ("rangeBoolResultExit", (fun (x y : UInt64) => (rangeBoolResultExit x y).toUInt64)),
   ("rangeBoolResultContinue", (fun (x y : UInt64) => (rangeBoolResultContinue x y).toUInt64)),
   ("rangeBoolResultStride", (fun (x y : UInt64) => (rangeBoolResultStride x y).toUInt64)),
   ("rangeBoolResultId", (fun (x y : UInt64) => (rangeBoolResultId x y).toUInt64)),
   ("rangeLetBool", rangeLetBool),
   ("rangeWordFromBoolLet", (fun (x y : UInt64) => rangeWordFromBoolLet x y)),
   ("rangeWordFromBoolDo", (fun (x y : UInt64) => rangeWordFromBoolDo x y)),
   ("rangeWordFromBoolFlag", (fun (x y : UInt64) => rangeWordFromBoolFlag x (y != 0))),
   ("rangeWordFromBoolHelper", (fun (x y : UInt64) => rangeWordFromBoolHelper x y)),
   ("rangeWordFromBoolConverted", (fun (x y : UInt64) => rangeWordFromBoolConverted x y)),
   ("rangeWordFromBoolMixed", (fun (x y : UInt64) => rangeWordFromBoolMixed x y)),
   ("rangeWordFromBoolExit", (fun (x y : UInt64) => rangeWordFromBoolExit x y)),
   ("rangeWordFromBoolContinue", (fun (x y : UInt64) => rangeWordFromBoolContinue x y)),
   ("rangeWordFromBoolStride", (fun (x y : UInt64) => rangeWordFromBoolStride x y)),
   ("rangeWordFromBoolId", (fun (x y : UInt64) => rangeWordFromBoolId x y)),
   ("rangeWordBoolSetupWord", (fun (x y : UInt64) => rangeWordBoolSetupWord x y)),
   ("rangeWordBoolSetupFlag", (fun (x y : UInt64) => rangeWordBoolSetupFlag x y)),
   ("rangeWordBoolSetupDo", (fun (x y : UInt64) => rangeWordBoolSetupDo x y)),
   ("rangeWordBoolSetupNested", (fun (x y : UInt64) => rangeWordBoolSetupNested x y)),
   ("rangeWordBoolSavedResult", (fun (x y : UInt64) => rangeWordBoolSavedResult x y)),
   ("rangeWordBoolShowResult", (fun (x y : UInt64) => rangeWordBoolShowResult x y)),
   ("rangeWordBoolSetupExit", (fun (x y : UInt64) => rangeWordBoolSetupExit x y)),
   ("rangeWordBoolSetupContinue", (fun (x y : UInt64) => rangeWordBoolSetupContinue x y)),
   ("rangeWordBoolSetupStride", (fun (x y : UInt64) => rangeWordBoolSetupStride x y)),
   ("rangeWordBoolSetupId", (fun (x y : UInt64) => rangeWordBoolSetupId x y)),
   ("rangeWordBoolHelperWord", (fun (x y : UInt64) => rangeWordBoolHelperWord x y)),
   ("rangeWordBoolHelperBoolean", (fun (x y : UInt64) => rangeWordBoolHelperBoolean x y)),
   ("rangeWordBoolHelperPredicate", (fun (x y : UInt64) => rangeWordBoolHelperPredicate x y)),
   ("rangeWordBoolHelperBooleanPredicate", (fun (x y : UInt64) => rangeWordBoolHelperBooleanPredicate x y)),
   ("rangeWordBoolHelperBinary", (fun (x y : UInt64) => rangeWordBoolHelperBinary x y)),
   ("rangeWordBoolHelperMany", (fun (x y : UInt64) => rangeWordBoolHelperMany x y)),
   ("rangeWordBoolHelperManyFive", (fun (x y : UInt64) => rangeWordBoolHelperManyFive x y)),
   ("rangeWordBoolHelperUnit", (fun (x y : UInt64) => rangeWordBoolHelperUnit x y)),
   ("rangeWordBoolHelperPunit", (fun (x y : UInt64) => rangeWordBoolHelperPunit x y)),
   ("rangeWordBoolHelperId", (fun (x y : UInt64) => rangeWordBoolHelperId x y)),
   ("rangeWordChooseLoops", (fun (x y : UInt64) => rangeWordChooseLoops x y)),
   ("rangeWordChooseScalarLeft", (fun (x y : UInt64) => rangeWordChooseScalarLeft x y)),
   ("rangeWordChooseScalarRight", (fun (x y : UInt64) => rangeWordChooseScalarRight x y)),
   ("rangeWordChooseNested", (fun (x y : UInt64) => rangeWordChooseNested x y)),
   ("rangeWordChooseBooleanLoop", (fun (x y : UInt64) => rangeWordChooseBooleanLoop x y)),
   ("rangeWordChooseExit", (fun (x y : UInt64) => rangeWordChooseExit x y)),
   ("rangeWordChooseContinue", (fun (x y : UInt64) => rangeWordChooseContinue x y)),
   ("rangeWordChooseStride", (fun (x y : UInt64) => rangeWordChooseStride x y)),
   ("rangeWordChooseHelpers", (fun (x y : UInt64) => rangeWordChooseHelpers x y)),
   ("rangeWordChooseId", (fun (x y : UInt64) => rangeWordChooseId x y)),
   ("rangeWordChooseSetupWord", (fun (x y : UInt64) => rangeWordChooseSetupWord x y)),
   ("rangeWordChooseSetupFlag", (fun (x y : UInt64) => rangeWordChooseSetupFlag x y)),
   ("rangeWordChooseSetupDo", (fun (x y : UInt64) => rangeWordChooseSetupDo x y)),
   ("rangeWordChooseSetupNested", (fun (x y : UInt64) => rangeWordChooseSetupNested x y)),
   ("rangeWordChooseSavedResult", (fun (x y : UInt64) => rangeWordChooseSavedResult x y)),
   ("rangeWordChooseShowResult", (fun (x y : UInt64) => rangeWordChooseShowResult x y)),
   ("rangeWordChooseSetupExit", (fun (x y : UInt64) => rangeWordChooseSetupExit x y)),
   ("rangeWordChooseSetupContinue", (fun (x y : UInt64) => rangeWordChooseSetupContinue x y)),
   ("rangeWordChooseSetupStride", (fun (x y : UInt64) => rangeWordChooseSetupStride x y)),
   ("rangeWordChooseSetupId", (fun (x y : UInt64) => rangeWordChooseSetupId x y)),
   ("rangeWordChooseHelperWord", (fun (x y : UInt64) => rangeWordChooseHelperWord x y)),
   ("rangeWordChooseHelperBoolean", (fun (x y : UInt64) => rangeWordChooseHelperBoolean x y)),
   ("rangeWordChooseHelperPredicate", (fun (x y : UInt64) => rangeWordChooseHelperPredicate x y)),
   ("rangeWordChooseHelperBooleanPredicate", (fun (x y : UInt64) => rangeWordChooseHelperBooleanPredicate x y)),
   ("rangeWordChooseHelperBinary", (fun (x y : UInt64) => rangeWordChooseHelperBinary x y)),
   ("rangeWordChooseHelperMany", (fun (x y : UInt64) => rangeWordChooseHelperMany x y)),
   ("rangeWordChooseHelperManyFive", (fun (x y : UInt64) => rangeWordChooseHelperManyFive x y)),
   ("rangeWordChooseHelperUnit", (fun (x y : UInt64) => rangeWordChooseHelperUnit x y)),
   ("rangeWordChooseHelperPunit", (fun (x y : UInt64) => rangeWordChooseHelperPunit x y)),
   ("rangeWordChooseHelperId", (fun (x y : UInt64) => rangeWordChooseHelperId x y)),
   ("rangeBoolTailHelperCapture", (fun (x y : UInt64) => (rangeBoolTailHelperCapture x y).toUInt64)),
   ("rangeBoolTailHelperBoolean", (fun (x y : UInt64) => (rangeBoolTailHelperBoolean x y).toUInt64)),
   ("rangeBoolTailHelperNestedId", (fun (x y : UInt64) => (rangeBoolTailHelperNestedId x y).toUInt64)),
   ("rangeWordStepReturnedHelper", (fun (x y : UInt64) => rangeWordStepReturnedHelper x y)),
   ("rangeBoolRelationStep", (fun (x y : UInt64) => rangeBoolRelationStep x y)),
   ("rangeBoolRelationExit", (fun (x y : UInt64) => rangeBoolRelationExit x y)),
   ("rangeBoolRelationContinue", (fun (x y : UInt64) => rangeBoolRelationContinue x y)),
   ("rangeBoolRelationTail", (fun (x y : UInt64) => (rangeBoolRelationTail x y).toUInt64)),
   ("rangePredicateOuterBodyWord", (fun (x y : UInt64) => rangePredicateOuterBodyWord x y)),
   ("rangePredicateOuterBodyBoolean", (fun (x y : UInt64) => rangePredicateOuterBodyBoolean x y)),
   ("rangePredicateOuterBodyUnused", (fun (x y : UInt64) => rangePredicateOuterBodyUnused x y)),
   ("rangePredicateOuterBodyBound", (fun (x y : UInt64) => rangePredicateOuterBodyBound x y)),
   ("rangePredicateOuterBodyInitial", (fun (x y : UInt64) => rangePredicateOuterBodyInitial x y)),
   ("rangePredicateOuterBodyTail", (fun (x y : UInt64) => rangePredicateOuterBodyTail x y)),
   ("rangePredicateOuterBodyCapture", (fun (x y : UInt64) => rangePredicateOuterBodyCapture x y)),
   ("rangePredicateOuterBodyWrapped", (fun (x y : UInt64) => rangePredicateOuterBodyWrapped x y)),
   ("rangePredicateOuterBodyNested", (fun (x y : UInt64) => rangePredicateOuterBodyNested x y)),
   ("rangePredicateOuterBodyId", (fun (x y : UInt64) => rangePredicateOuterBodyId x y)),
   ("rangePredicateBodyBreakWord", (fun (x y : UInt64) => rangePredicateBodyBreakWord x y)),
   ("rangePredicateBodyBreakBoolean", (fun (x y : UInt64) => rangePredicateBodyBreakBoolean x y)),
   ("rangePredicateBodyContinueWord", (fun (x y : UInt64) => rangePredicateBodyContinueWord x y)),
   ("rangePredicateBodyContinueBoolean", (fun (x y : UInt64) => rangePredicateBodyContinueBoolean x y)),
   ("rangePredicateBodyDependent", (fun (x y : UInt64) => rangePredicateBodyDependent x y)),
   ("rangePredicateBodyCapture", (fun (x y : UInt64) => rangePredicateBodyCapture x y)),
   ("rangePredicateBodyUnused", (fun (x y : UInt64) => rangePredicateBodyUnused x y)),
   ("rangePredicateBodyWrapped", (fun (x y : UInt64) => rangePredicateBodyWrapped x y)),
   ("rangePredicateBodyNested", (fun (x y : UInt64) => rangePredicateBodyNested x y)),
   ("rangePredicateBodyId", (fun (x y : UInt64) => rangePredicateBodyId x y)),
   ("rangePredicateBodyWordStep", (fun (x y : UInt64) => rangePredicateBodyWordStep x y)),
   ("rangePredicateBodyWordExit", (fun (x y : UInt64) => rangePredicateBodyWordExit x y)),
   ("rangePredicateBodyWordContinue", (fun (x y : UInt64) => rangePredicateBodyWordContinue x y)),
   ("rangePredicateBodyWordTail", (fun (x y : UInt64) => rangePredicateBodyWordTail x y)),
   ("rangeHelperBodyStep", (fun (x y : UInt64) => rangeHelperBodyStep x y)),
   ("rangeHelperBodyExit", (fun (x y : UInt64) => rangeHelperBodyExit x y)),
   ("rangeHelperBodyContinue", (fun (x y : UInt64) => rangeHelperBodyContinue x y)),
   ("rangeHelperBodyTail", (fun (x y : UInt64) => rangeHelperBodyTail x y)),
   ("rangePropositionHelperLetStep", (fun (x y : UInt64) => rangePropositionHelperLetStep x y)),
   ("rangePropositionHelperLetExit", (fun (x y : UInt64) => rangePropositionHelperLetExit x y)),
   ("rangePropositionHelperLetContinue", (fun (x y : UInt64) => rangePropositionHelperLetContinue x y)),
   ("rangePropositionHelperLetTail", (fun (x y : UInt64) => rangePropositionHelperLetTail x y)),
   ("rangeHelperRelationChoiceStep", (fun (x y : UInt64) => rangeHelperRelationChoiceStep x y)),
   ("rangeHelperRelationChoiceExit", (fun (x y : UInt64) => rangeHelperRelationChoiceExit x y)),
   ("rangeHelperRelationChoiceContinue", (fun (x y : UInt64) => rangeHelperRelationChoiceContinue x y)),
   ("rangeHelperRelationChoiceTail", (fun (x y : UInt64) => rangeHelperRelationChoiceTail x y)),
   ("rangeHelperPropositionChoiceStep", (fun (x y : UInt64) => rangeHelperPropositionChoiceStep x y)),
   ("rangeHelperPropositionChoiceExit", (fun (x y : UInt64) => rangeHelperPropositionChoiceExit x y)),
   ("rangeHelperPropositionChoiceContinue", (fun (x y : UInt64) => rangeHelperPropositionChoiceContinue x y)),
   ("rangeHelperPropositionChoiceTail", (fun (x y : UInt64) => rangeHelperPropositionChoiceTail x y)),
   ("rangeHelperChoiceStep", (fun (x y : UInt64) => rangeHelperChoiceStep x y)),
   ("rangeHelperChoiceExit", (fun (x y : UInt64) => rangeHelperChoiceExit x y)),
   ("rangeHelperChoiceContinue", (fun (x y : UInt64) => rangeHelperChoiceContinue x y)),
   ("rangeHelperChoiceTail", (fun (x y : UInt64) => rangeHelperChoiceTail x y)),
   ("rangeHelperEqualityStep", (fun (x y : UInt64) => rangeHelperEqualityStep x y)),
   ("rangeHelperEqualityExit", (fun (x y : UInt64) => rangeHelperEqualityExit x y)),
   ("rangeHelperEqualityContinue", (fun (x y : UInt64) => rangeHelperEqualityContinue x y)),
   ("rangeHelperEqualityTail", (fun (x y : UInt64) => rangeHelperEqualityTail x y)),
   ("rangeHelperJunctionStep", (fun (x y : UInt64) => rangeHelperJunctionStep x y)),
   ("rangeHelperJunctionExit", (fun (x y : UInt64) => rangeHelperJunctionExit x y)),
   ("rangeHelperJunctionContinue", (fun (x y : UInt64) => rangeHelperJunctionContinue x y)),
   ("rangeHelperJunctionTail", (fun (x y : UInt64) => rangeHelperJunctionTail x y)),
   ("rangeHelperNegationStep", (fun (x y : UInt64) => rangeHelperNegationStep x y)),
   ("rangeHelperNegationExit", (fun (x y : UInt64) => rangeHelperNegationExit x y)),
   ("rangeHelperNegationContinue", (fun (x y : UInt64) => rangeHelperNegationContinue x y)),
   ("rangeHelperNegationTail", (fun (x y : UInt64) => rangeHelperNegationTail x y)),
   ("rangeInnerWrapperStep", (fun (x y : UInt64) => rangeInnerWrapperStep x y)),
   ("rangeInnerWrapperExit", (fun (x y : UInt64) => rangeInnerWrapperExit x y)),
   ("rangeInnerWrapperContinue", (fun (x y : UInt64) => rangeInnerWrapperContinue x y)),
   ("rangeInnerWrapperTail", (fun (x y : UInt64) => rangeInnerWrapperTail x y)),
   ("rangeInnerHelperStep", (fun (x y : UInt64) => rangeInnerHelperStep x y)),
   ("rangeInnerHelperExit", (fun (x y : UInt64) => rangeInnerHelperExit x y)),
   ("rangeInnerHelperContinue", (fun (x y : UInt64) => rangeInnerHelperContinue x y)),
   ("rangeInnerHelperTail", (fun (x y : UInt64) => rangeInnerHelperTail x y)),
   ("rangeBoolLetRelationStep", (fun (x y : UInt64) => rangeBoolLetRelationStep x y)),
   ("rangeBoolLetRelationExit", (fun (x y : UInt64) => rangeBoolLetRelationExit x y)),
   ("rangeBoolLetRelationContinue", (fun (x y : UInt64) => rangeBoolLetRelationContinue x y)),
   ("rangeBoolLetRelationTail", (fun (x y : UInt64) => (rangeBoolLetRelationTail x y).toUInt64)),
   ("rangeBoolLetIdWord", (fun (x y : UInt64) => (rangeBoolLetIdWord x y).toUInt64)),
   ("rangeBoolLetIdWordLayers", (fun (x y : UInt64) => (rangeBoolLetIdWordLayers x y).toUInt64)),
   ("rangeBoolLetIdFlag", (fun (x y : UInt64) => (rangeBoolLetIdFlag x y).toUInt64)),
   ("rangeBoolLetIdFlagLayers", (fun (x y : UInt64) => (rangeBoolLetIdFlagLayers x y).toUInt64)),
   ("rangeBoolLetIdResult", (fun (x y : UInt64) => (rangeBoolLetIdResult x y).toUInt64)),
   ("rangeBoolLetIdResultLayers", (fun (x y : UInt64) => (rangeBoolLetIdResultLayers x y).toUInt64)),
   ("rangeBoolLetIdMixed", (fun (x y : UInt64) => (rangeBoolLetIdMixed x y).toUInt64)),
   ("rangeBoolLetIdExit", (fun (x y : UInt64) => (rangeBoolLetIdExit x y).toUInt64)),
   ("rangeBoolLetIdContinue", (fun (x y : UInt64) => (rangeBoolLetIdContinue x y).toUInt64)),
   ("rangeBoolLetIdInput", (fun (x y : UInt64) => (rangeBoolLetIdInput x (y != 0)).toUInt64)),
   ("rangeBoolFlagSetupLet", (fun (x y : UInt64) => (rangeBoolFlagSetupLet x y).toUInt64)),
   ("rangeBoolFlagSetupChain", (fun (x y : UInt64) => (rangeBoolFlagSetupChain x y).toUInt64)),
   ("rangeBoolFlagSetupBind", (fun (x y : UInt64) => (rangeBoolFlagSetupBind x y).toUInt64)),
   ("rangeBoolFlagSetupCondition", (fun (x y : UInt64) => (rangeBoolFlagSetupCondition x y).toUInt64)),
   ("rangeBoolFlagSetupExit", (fun (x y : UInt64) => (rangeBoolFlagSetupExit x y).toUInt64)),
   ("rangeBoolFlagSetupContinue", (fun (x y : UInt64) => (rangeBoolFlagSetupContinue x y).toUInt64)),
   ("rangeBoolFlagSetupStride", (fun (x y : UInt64) => (rangeBoolFlagSetupStride x y).toUInt64)),
   ("rangeBoolFlagSetupCapture", (fun (x y : UInt64) => (rangeBoolFlagSetupCapture x y).toUInt64)),
   ("rangeBoolFlagSetupInput", (fun (x y : UInt64) => (rangeBoolFlagSetupInput x (y != 0)).toUInt64)),
   ("rangeBoolFlagSetupId", (fun (x y : UInt64) => (rangeBoolFlagSetupId x (y != 0)).toUInt64)),
   ("rangeBoolWordSetupLet", (fun (x y : UInt64) => (rangeBoolWordSetupLet x y).toUInt64)),
   ("rangeBoolWordSetupChain", (fun (x y : UInt64) => (rangeBoolWordSetupChain x y).toUInt64)),
   ("rangeBoolWordSetupBind", (fun (x y : UInt64) => (rangeBoolWordSetupBind x y).toUInt64)),
   ("rangeBoolWordSetupCount", (fun (x y : UInt64) => (rangeBoolWordSetupCount x y).toUInt64)),
   ("rangeBoolWordSetupExit", (fun (x y : UInt64) => (rangeBoolWordSetupExit x y).toUInt64)),
   ("rangeBoolWordSetupContinue", (fun (x y : UInt64) => (rangeBoolWordSetupContinue x y).toUInt64)),
   ("rangeBoolWordSetupStride", (fun (x y : UInt64) => (rangeBoolWordSetupStride x y).toUInt64)),
   ("rangeBoolWordSetupCapture", (fun (x y : UInt64) => (rangeBoolWordSetupCapture x y).toUInt64)),
   ("rangeBoolWordSetupFlag", (fun (x y : UInt64) => (rangeBoolWordSetupFlag x (y != 0)).toUInt64)),
   ("rangeBoolWordSetupId", (fun (x y : UInt64) => (rangeBoolWordSetupId x y).toUInt64)),
   ("rangeBoolResultBindYield", (fun (x y : UInt64) => (rangeBoolResultBindYield x y).toUInt64)),
   ("rangeBoolResultBindExit", (fun (x y : UInt64) => (rangeBoolResultBindExit x y).toUInt64)),
   ("rangeBoolResultBindContinue", (fun (x y : UInt64) => (rangeBoolResultBindContinue x y).toUInt64)),
   ("rangeBoolResultBindStride", (fun (x y : UInt64) => (rangeBoolResultBindStride x y).toUInt64)),
   ("rangeBoolResultBindStepHelper", (fun (x y : UInt64) => (rangeBoolResultBindStepHelper x y).toUInt64)),
   ("rangeBoolResultBindCapture", (fun (x y : UInt64) => (rangeBoolResultBindCapture x y).toUInt64)),
   ("rangeBoolResultBindFlag", (fun (x y : UInt64) => (rangeBoolResultBindFlag x (y != 0)).toUInt64)),
   ("rangeBoolResultBindIdInputs", (fun (x y : UInt64) => (rangeBoolResultBindIdInputs x (y != 0)).toUInt64)),
   ("rangeBoolResultBindIdAction", (fun (x y : UInt64) => (rangeBoolResultBindIdAction x y).toUInt64)),
   ("rangeBoolResultBindNestedResult", (fun (x y : UInt64) => (rangeBoolResultBindNestedResult x y).toUInt64)),
   ("rangeBoolYield", (fun (x y : UInt64) => (rangeBoolYield x y).toUInt64)),
   ("rangeBoolExit", (fun (x y : UInt64) => (rangeBoolExit x y).toUInt64)),
   ("rangeBoolContinue", (fun (x y : UInt64) => (rangeBoolContinue x y).toUInt64)),
   ("rangeBoolStride", (fun (x y : UInt64) => (rangeBoolStride x y).toUInt64)),
   ("rangeBoolStepHelper", (fun (x y : UInt64) => (rangeBoolStepHelper x y).toUInt64)),
   ("rangeBoolCapture", (fun (x y : UInt64) => (rangeBoolCapture x y).toUInt64)),
   ("rangeBoolFlag", (fun (x y : UInt64) => (rangeBoolFlag x (y != 0)).toUInt64)),
   ("rangeBoolIdInputs", (fun (x y : UInt64) => (rangeBoolIdInputs x (y != 0)).toUInt64)),
   ("rangeBoolPure", (fun (x y : UInt64) => (rangeBoolPure x y).toUInt64)),
   ("rangeBoolRun", (fun (x y : UInt64) => (rangeBoolRun x y).toUInt64)),
   ("rangeInputIdYield", (fun (x y : UInt64) => Id.run (rangeInputIdYield x (y != 0)))),
   ("rangeInputIdExit", (fun (x y : UInt64) => Id.run (rangeInputIdExit x (y != 0)))),
   ("rangeInputIdContinue", (fun (x y : UInt64) => Id.run (rangeInputIdContinue x (y != 0)))),
   ("rangeInputIdCapture", (fun (x y : UInt64) => Id.run (rangeInputIdCapture x (y != 0)))),
   ("rangeFlagYield", (fun x y => rangeFlagYield x (y != 0))),
   ("rangeFlagExit", (fun x y => rangeFlagExit x (y != 0))),
   ("rangeFlagContinue", (fun x y => rangeFlagContinue x (y != 0))),
   ("rangeFlagsBoth", (fun x y => rangeFlagsBoth (x != 0) (y != 0))),
   ("rangeFlagOuter", (fun x y => rangeFlagOuter x (y != 0))),
   ("rangeFlagStepHelper", (fun x y => rangeFlagStepHelper x (y != 0))),
   ("rangeFlagAlias", (fun x y => rangeFlagAlias x (y != 0))),
   ("rangeFlagBind", (fun x y => Id.run (rangeFlagBind x (y != 0)))),
   ("rangeFlagCount", (fun x y => rangeFlagCount (x != 0) y)),
   ("rangeFlagResult", (fun x y => rangeFlagResult (x != 0) y)),
   ("rangePublicIdYield", (fun x y => Id.run (rangePublicIdYield x y))),
   ("rangePublicIdExit", (fun x y => Id.run (rangePublicIdExit x y))),
   ("rangePublicIdContinue", (fun x y => Id.run (rangePublicIdContinue x y))),
   ("rangePublicIdCapture", (fun x y => Id.run (rangePublicIdCapture x y))),
   ("rangeBooleanCallArgumentStep", rangeBooleanCallArgumentStep),
   ("rangeBooleanCallArgumentContinue", rangeBooleanCallArgumentContinue),
   ("rangeBooleanCallArgumentOuter", rangeBooleanCallArgumentOuter),
   ("rangeBooleanCallArgumentBind", rangeBooleanCallArgumentBind),
   ("rangeBooleanInputStep", rangeBooleanInputStep),
   ("rangeBooleanInputContinue", rangeBooleanInputContinue),
   ("rangeBooleanInputOuter", rangeBooleanInputOuter),
   ("rangeBooleanInputHelper", rangeBooleanInputHelper),
   ("rangeBooleanPredicateResultLocalBool", rangeBooleanPredicateResultLocalBool),
   ("rangeBooleanPredicateResultLocalWord", rangeBooleanPredicateResultLocalWord),
   ("rangeBooleanPredicateResultLocalNested", rangeBooleanPredicateResultLocalNested),
   ("rangeBooleanPredicateResultLocalWrapped", rangeBooleanPredicateResultLocalWrapped),
   ("rangeBooleanPredicateResultOuterBool", rangeBooleanPredicateResultOuterBool),
   ("rangeBooleanPredicateResultOuterWord", rangeBooleanPredicateResultOuterWord),
   ("rangeBooleanPredicateResultOuterNested", rangeBooleanPredicateResultOuterNested),
   ("rangeBooleanPredicateResultOuterWrapped", rangeBooleanPredicateResultOuterWrapped),
   ("rangeBooleanPredicateResultStep", rangeBooleanPredicateResultStep),
   ("rangeBooleanPredicateResultCondition", rangeBooleanPredicateResultCondition),
   ("rangeBooleanPredicateResultOuter", rangeBooleanPredicateResultOuter),
   ("rangeBooleanPredicateResultHelper", rangeBooleanPredicateResultHelper),
   ("rangeBooleanPredicateBindStep", rangeBooleanPredicateBindStep),
   ("rangeBooleanPredicateBindCondition", rangeBooleanPredicateBindCondition),
   ("rangeBooleanPredicateBindOuter", rangeBooleanPredicateBindOuter),
   ("rangeBooleanPredicateBindOuterCapture", rangeBooleanPredicateBindOuterCapture),
   ("rangeBooleanPredicateWrapperStep", rangeBooleanPredicateWrapperStep),
   ("rangeBooleanPredicateWrapperContinue", rangeBooleanPredicateWrapperContinue),
   ("rangeBooleanPredicateWrapperOuter", rangeBooleanPredicateWrapperOuter),
   ("rangeBooleanPredicateWrapperCapture", rangeBooleanPredicateWrapperCapture),
   ("rangeBooleanPredicateConditionStep", rangeBooleanPredicateConditionStep),
   ("rangeBooleanPredicateConditionContinue", rangeBooleanPredicateConditionContinue),
   ("rangeBooleanPredicateConditionOuter", rangeBooleanPredicateConditionOuter),
   ("rangeBooleanPredicateConditionOuterCapture", rangeBooleanPredicateConditionOuterCapture),
   ("rangeBooleanPredicateLetStep", rangeBooleanPredicateLetStep),
   ("rangeBooleanPredicateLetContinue", rangeBooleanPredicateLetContinue),
   ("rangeBooleanPredicateLetOuter", rangeBooleanPredicateLetOuter),
   ("rangeBooleanPredicateLetOuterCapture", rangeBooleanPredicateLetOuterCapture),
   ("rangeBooleanPredicatePropositionStep", rangeBooleanPredicatePropositionStep),
   ("rangeBooleanPredicatePropositionContinue", rangeBooleanPredicatePropositionContinue),
   ("rangeBooleanPredicatePropositionOuter", rangeBooleanPredicatePropositionOuter),
   ("rangeBooleanPredicatePropositionOuterCapture", rangeBooleanPredicatePropositionOuterCapture),
   ("rangeBooleanPredicateChoiceStep", rangeBooleanPredicateChoiceStep),
   ("rangeBooleanPredicateChoiceContinue", rangeBooleanPredicateChoiceContinue),
   ("rangeBooleanPredicateChoiceOuter", rangeBooleanPredicateChoiceOuter),
   ("rangeBooleanPredicateChoiceOuterCapture", rangeBooleanPredicateChoiceOuterCapture),
   ("rangeBooleanPredicateEqualityStep", rangeBooleanPredicateEqualityStep),
   ("rangeBooleanPredicateEqualityContinue", rangeBooleanPredicateEqualityContinue),
   ("rangeBooleanPredicateEqualityOuter", rangeBooleanPredicateEqualityOuter),
   ("rangeBooleanPredicateEqualityOuterCapture", rangeBooleanPredicateEqualityOuterCapture),
   ("rangeBooleanPredicateJunctionStep", rangeBooleanPredicateJunctionStep),
   ("rangeBooleanPredicateJunctionContinue", rangeBooleanPredicateJunctionContinue),
   ("rangeBooleanPredicateJunctionOuter", rangeBooleanPredicateJunctionOuter),
   ("rangeBooleanPredicateJunctionOuterCapture", rangeBooleanPredicateJunctionOuterCapture),
   ("rangeBooleanPredicateComposeStep", rangeBooleanPredicateComposeStep),
   ("rangeBooleanPredicateComposeContinue", rangeBooleanPredicateComposeContinue),
   ("rangeBooleanPredicateComposeOuter", rangeBooleanPredicateComposeOuter),
   ("rangeBooleanPredicateComposeOuterCapture", rangeBooleanPredicateComposeOuterCapture),
   ("rangeBooleanPredicateNotStep", rangeBooleanPredicateNotStep),
   ("rangeBooleanPredicateNotContinue", rangeBooleanPredicateNotContinue),
   ("rangeBooleanPredicateNotOuter", rangeBooleanPredicateNotOuter),
   ("rangeBooleanPredicateNotOuterCapture", rangeBooleanPredicateNotOuterCapture),
   ("rangeOuterBooleanPredicateBounds", rangeOuterBooleanPredicateBounds),
   ("rangeOuterBooleanPredicateCapture", rangeOuterBooleanPredicateCapture),
   ("rangeOuterBooleanPredicateNested", rangeOuterBooleanPredicateNested),
   ("rangeOuterBooleanPredicateShadow", rangeOuterBooleanPredicateShadow),
   ("rangeOuterBooleanPredicateUnused", rangeOuterBooleanPredicateUnused),
   ("rangeOuterBooleanPredicateScalarHelper", rangeOuterBooleanPredicateScalarHelper),
   ("rangeOuterBooleanPredicateId", rangeOuterBooleanPredicateId),
   ("rangeOuterBooleanPredicateStride", rangeOuterBooleanPredicateStride),
   ("rangeBooleanPredicateBreak", rangeBooleanPredicateBreak),
   ("rangeBooleanPredicateContinue", rangeBooleanPredicateContinue),
   ("rangeBooleanPredicateCapture", rangeBooleanPredicateCapture),
   ("rangeBooleanPredicateNested", rangeBooleanPredicateNested),
   ("rangeBooleanPredicateStepHelper", rangeBooleanPredicateStepHelper),
   ("rangeBooleanPredicateUnused", rangeBooleanPredicateUnused),
   ("rangePredicateInputStep", rangePredicateInputStep),
   ("rangePredicateInputStepCapture", rangePredicateInputStepCapture),
   ("rangePredicateInputOuter", rangePredicateInputOuter),
   ("rangePredicateInputOuterCapture", rangePredicateInputOuterCapture),

   ("rangeOuterPredicateBounds", rangeOuterPredicateBounds),
   ("rangeOuterPredicateCapture", rangeOuterPredicateCapture),
   ("rangeOuterPredicateNested", rangeOuterPredicateNested),
   ("rangeOuterPredicateShadow", rangeOuterPredicateShadow),
   ("rangeOuterPredicateUnused", rangeOuterPredicateUnused),
   ("rangeOuterPredicateScalarHelper", rangeOuterPredicateScalarHelper),
   ("rangeOuterPredicateId", rangeOuterPredicateId),
   ("rangeOuterPredicateStride", rangeOuterPredicateStride),

   ("rangeReusableBooleanBreak", rangeReusableBooleanBreak),
   ("rangeReusableBooleanContinue", rangeReusableBooleanContinue),
   ("rangeReusableBooleanCapture", rangeReusableBooleanCapture),
   ("rangeReusableBooleanNested", rangeReusableBooleanNested),
   ("rangeReusableBooleanStepHelper", rangeReusableBooleanStepHelper),
   ("rangeReusableBooleanUnused", rangeReusableBooleanUnused),
("rangeIndexed", rangeIndexed), ("rangeIndexFree", rangeIndexFree),
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
   ("rangeDecideOuter", rangeDecideOuter),
   ("rangeBoolWordYield", rangeBoolWordYield),
   ("rangeBoolWordBreak", rangeBoolWordBreak),
   ("rangeBoolWordContinue", rangeBoolWordContinue),
   ("rangeBoolWordJoined", rangeBoolWordJoined),
   ("rangeBoolWordCapture", rangeBoolWordCapture),
   ("rangeBoolWordBounds", rangeBoolWordBounds),
   ("rangeBoolWordStep", rangeBoolWordStep),
   ("rangeBoolWordOuter", rangeBoolWordOuter),
   ("rangeBoolEqYield", rangeBoolEqYield),
   ("rangeBoolEqBreak", rangeBoolEqBreak),
   ("rangeBoolEqContinue", rangeBoolEqContinue),
   ("rangeBoolEqJoined", rangeBoolEqJoined),
   ("rangeBoolEqCapture", rangeBoolEqCapture),
   ("rangeBoolEqBounds", rangeBoolEqBounds),
   ("rangeBoolEqStep", rangeBoolEqStep),
   ("rangeBoolEqOuter", rangeBoolEqOuter),
   ("rangeBoolPropYield", rangeBoolPropYield),
   ("rangeBoolPropBreak", rangeBoolPropBreak),
   ("rangeBoolPropContinue", rangeBoolPropContinue),
   ("rangeBoolPropJoined", rangeBoolPropJoined),
   ("rangeBoolPropCapture", rangeBoolPropCapture),
   ("rangeBoolPropBounds", rangeBoolPropBounds),
   ("rangeBoolPropStep", rangeBoolPropStep),
   ("rangeBoolPropOuter", rangeBoolPropOuter),
   ("rangeLocalDecideYield", rangeLocalDecideYield),
   ("rangeLocalDecideJoined", rangeLocalDecideJoined),
   ("rangeLocalDecideContinue", rangeLocalDecideContinue),
   ("rangeLocalDecideCapture", rangeLocalDecideCapture),
   ("rangeLocalDecideBounds", rangeLocalDecideBounds),
   ("rangeLocalDecideStep", rangeLocalDecideStep),
   ("rangeLocalDecideOuter", rangeLocalDecideOuter),
   ("rangeLocalDecideUnused", rangeLocalDecideUnused),
   ("rangeRelationChoiceYield", rangeRelationChoiceYield),
   ("rangeRelationChoiceJoined", rangeRelationChoiceJoined),
   ("rangeRelationChoiceContinue", rangeRelationChoiceContinue),
   ("rangeRelationChoiceCapture", rangeRelationChoiceCapture),
   ("rangeRelationChoiceBounds", rangeRelationChoiceBounds),
   ("rangeRelationChoiceStep", rangeRelationChoiceStep),
   ("rangeRelationChoiceOuter", rangeRelationChoiceOuter),
   ("rangeRelationChoiceUnused", rangeRelationChoiceUnused),
   ("rangeDependentChoiceYield", rangeDependentChoiceYield),
   ("rangeDependentChoiceJoined", rangeDependentChoiceJoined),
   ("rangeDependentChoiceContinue", rangeDependentChoiceContinue),
   ("rangeDependentChoiceCapture", rangeDependentChoiceCapture),
   ("rangeDependentChoiceBounds", rangeDependentChoiceBounds),
   ("rangeDependentChoiceStep", rangeDependentChoiceStep),
   ("rangeDependentChoiceOuter", rangeDependentChoiceOuter),
   ("rangeDependentChoiceUnused", rangeDependentChoiceUnused),
   ("rangeBoolLetYield", rangeBoolLetYield),
   ("rangeBoolLetJoined", rangeBoolLetJoined),
   ("rangeBoolLetContinue", rangeBoolLetContinue),
   ("rangeBoolLetCapture", rangeBoolLetCapture),
   ("rangeBoolLetBounds", rangeBoolLetBounds),
   ("rangeBoolLetStep", rangeBoolLetStep),
   ("rangeBoolLetOuter", rangeBoolLetOuter),
   ("rangeBoolLetUnused", rangeBoolLetUnused),
   ("rangeBoolWordLetYield", rangeBoolWordLetYield),
   ("rangeBoolWordLetJoined", rangeBoolWordLetJoined),
   ("rangeBoolWordLetContinue", rangeBoolWordLetContinue),
   ("rangeBoolWordLetCapture", rangeBoolWordLetCapture),
   ("rangeBoolWordLetBounds", rangeBoolWordLetBounds),
   ("rangeBoolWordLetStep", rangeBoolWordLetStep),
   ("rangeBoolWordLetOuter", rangeBoolWordLetOuter),
   ("rangeBoolWordLetUnused", rangeBoolWordLetUnused),
   ("rangeAnnotatedLetYield", rangeAnnotatedLetYield),
   ("rangeAnnotatedLetJoined", rangeAnnotatedLetJoined),
   ("rangeAnnotatedLetContinue", rangeAnnotatedLetContinue),
   ("rangeAnnotatedLetCapture", rangeAnnotatedLetCapture),
   ("rangeAnnotatedLetBounds", rangeAnnotatedLetBounds),
   ("rangeAnnotatedLetStep", rangeAnnotatedLetStep),
   ("rangeAnnotatedLetOuter", rangeAnnotatedLetOuter),
   ("rangeAnnotatedLetUnused", rangeAnnotatedLetUnused),
   ("rangeNestedIdYield", rangeNestedIdYield),
   ("rangeNestedIdJoined", rangeNestedIdJoined),
   ("rangeNestedIdContinue", rangeNestedIdContinue),
   ("rangeNestedIdCapture", rangeNestedIdCapture),
   ("rangeNestedIdBounds", rangeNestedIdBounds),
   ("rangeNestedIdStep", rangeNestedIdStep),
   ("rangeNestedIdOuter", rangeNestedIdOuter),
   ("rangeNestedIdUnused", rangeNestedIdUnused),
   ("rangeIdLetYield", rangeIdLetYield),
   ("rangeIdLetJoined", rangeIdLetJoined),
   ("rangeIdLetContinue", rangeIdLetContinue),
   ("rangeIdLetCapture", rangeIdLetCapture),
   ("rangeIdLetBounds", rangeIdLetBounds),
   ("rangeIdLetStep", rangeIdLetStep),
   ("rangeIdLetOuter", rangeIdLetOuter),
   ("rangeIdLetUnused", rangeIdLetUnused),
   ("rangeIdArithmeticYield", rangeIdArithmeticYield),
   ("rangeIdArithmeticContinue", rangeIdArithmeticContinue),
   ("rangeIdArithmeticBounds", rangeIdArithmeticBounds),
   ("rangeIdArithmeticStep", rangeIdArithmeticStep),
   ("rangeIdComparisonExit", rangeIdComparisonExit),
   ("rangeIdComparisonDecide", rangeIdComparisonDecide),
   ("rangeIdComparisonDependent", rangeIdComparisonDependent),
   ("rangeReannotatedOrder", rangeReannotatedOrder),
   ("rangeIdComparisonEvidenceAnnotations", rangeIdComparisonEvidenceAnnotations),
   ("rangeReannotatedAnd", rangeReannotatedAnd),
   ("rangeReannotatedOr", rangeReannotatedOr),
   ("rangeDependentReannotated", rangeDependentReannotated),
   ("rangeDependentReannotatedCompound", rangeDependentReannotatedCompound),
   ("rangeSavedReannotated", rangeSavedReannotated),
   ("rangeSavedReannotatedChoice", rangeSavedReannotatedChoice),
   ("rangeSavedReannotatedDependentChoice", rangeSavedReannotatedDependentChoice),
   ("rangeBooleanApplyBreak", rangeBooleanApplyBreak),
   ("rangeBooleanApplyContinue", rangeBooleanApplyContinue),
   ("rangeBooleanApplyCapture", rangeBooleanApplyCapture),
   ("rangeNamedBooleanBreak", rangeNamedBooleanBreak),
   ("rangeNamedBooleanContinue", rangeNamedBooleanContinue),
   ("rangeNamedBooleanCapture", rangeNamedBooleanCapture)]

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

def cases : List (String × (UInt64 → UInt64 → UInt64)) :=
  [
   ("natAliasLiteral", natAliasLiteral),
   ("natAliasOverflow", natAliasOverflow),
   ("natAliasChoice", natAliasChoice),
   ("natAliasHelper", natAliasHelper),
   ("natAliasDo", natAliasDo),
   ("natAliasPredicate", natAliasPredicate),
   ("booleanBoundResultValue", booleanBoundResultValue),
   ("booleanBoundResultBody", booleanBoundResultBody),
   ("booleanBoundResultNested", booleanBoundResultNested),
   ("booleanBoundResultCapture", booleanBoundResultCapture),
   ("booleanBoundResultApplication", booleanBoundResultApplication),
   ("booleanBoundResultNamed", booleanBoundResultNamed),
   ("booleanWordBoundResultValue", booleanWordBoundResultValue),
   ("booleanWordBoundResultBody", booleanWordBoundResultBody),
   ("booleanWordBoundResultNested", booleanWordBoundResultNested),
   ("booleanWordBoundResultCapture", booleanWordBoundResultCapture),
   ("booleanWordBoundResultApplication", booleanWordBoundResultApplication),
   ("booleanWordBoundResultNamed", booleanWordBoundResultNamed),
   ("booleanResultBindBool", booleanResultBindBool),
   ("booleanResultBindWord", booleanResultBindWord),
   ("booleanResultBindNested", booleanResultBindNested),
   ("booleanResultBindCapture", booleanResultBindCapture),
   ("booleanResultBindUnused", booleanResultBindUnused),
   ("booleanResultBindCondition", booleanResultBindCondition),
   ("savedMixedLeft", savedMixedLeft),
   ("savedMixedRight", savedMixedRight),
   ("savedMixedPair", savedMixedPair),
   ("savedMixedNegation", savedMixedNegation),
   ("savedMixedDecision", savedMixedDecision),
   ("savedMixedHelper", savedMixedHelper),
   ("callMixedBool", callMixedBool),
   ("callMixedWord", callMixedWord),
   ("callMixedPair", callMixedPair),
   ("callMixedNegation", callMixedNegation),
   ("callMixedDecision", callMixedDecision),
   ("callMixedHelper", callMixedHelper),
   ("extendedMixedJunction", extendedMixedJunction),
   ("extendedMixedChoice", extendedMixedChoice),
   ("extendedMixedLet", extendedMixedLet),
   ("extendedMixedBind", extendedMixedBind),
   ("extendedMixedWrapped", extendedMixedWrapped),
   ("extendedMixedRelation", extendedMixedRelation),
   ("propositionLetNested", propositionLetNested),
   ("propositionLetWord", propositionLetWord),
   ("propositionLetDecision", propositionLetDecision),
   ("propositionLetDependent", propositionLetDependent),
   ("propositionLetUnused", propositionLetUnused),
   ("propositionLetHelper", propositionLetHelper),
   ("decisionLetUnused", decisionLetUnused),
   ("decisionLetLeft", decisionLetLeft),
   ("decisionLetRight", decisionLetRight),
   ("decisionLetDependent", decisionLetDependent),
   ("decisionLetSaved", decisionLetSaved),
   ("decisionLetHelper", decisionLetHelper),
   ("localNotFlag", localNotFlag),
   ("localNotCall", localNotCall),
   ("localNotNested", localNotNested),
   ("localNotDecision", localNotDecision),
   ("localNotLet", localNotLet),
   ("localNotHelper", localNotHelper),
   ("publicInputIdWord", (fun (x y : UInt64) => Id.run (publicInputIdWord x y))),
   ("publicInputIdFlag", (fun (x y : UInt64) => Id.run (publicInputIdFlag (x != 0) y))),
   ("publicInputIdBoth", (fun (x y : UInt64) => Id.run (publicInputIdBoth (x != 0) y))),
   ("publicInputIdResult", (fun (x y : UInt64) => (publicInputIdResult x (y != 0)).toUInt64)),
   ("publicInputIdCapture", (fun (x y : UInt64) => (publicInputIdCapture (x != 0) y).toUInt64)),
   ("publicInputIdBind", (fun (x y : UInt64) => (publicInputIdBind (x != 0) y).toUInt64)),
   ("publicBoolHelpersNested", (fun (x y : UInt64) => (publicBoolHelpersNested (x != 0) y).toUInt64)),
   ("publicBoolHelpersRepeated", (fun (x y : UInt64) => (publicBoolHelpersRepeated (x != 0) y).toUInt64)),
   ("publicBoolHelpersWrapped", (fun (x y : UInt64) => (publicBoolHelpersWrapped (x != 0) y).toUInt64)),
   ("publicBoolHelpersInputId", (fun (x y : UInt64) => (publicBoolHelpersInputId x (y != 0)).toUInt64)),
   ("publicBoolHelpersWord", (fun (x y : UInt64) => (publicBoolHelpersWord (x != 0) y).toUInt64)),
   ("publicBoolHelpersMany", (fun (x y : UInt64) => (publicBoolHelpersMany x y).toUInt64)),
   ("publicBoolHelpersUnit", (fun (x y : UInt64) => (publicBoolHelpersUnit (x != 0) y).toUInt64)),
   ("publicBoolHelpersShadow", (fun (x y : UInt64) => (publicBoolHelpersShadow (x != 0) y).toUInt64)),
   ("publicBoolHelpersSaved", (fun (x y : UInt64) => (publicBoolHelpersSaved (x != 0) y).toUInt64)),
   ("publicBoolHelpersUnused", (fun (x y : UInt64) => (publicBoolHelpersUnused (x != 0) y).toUInt64)),
   ("booleanHelperReturnWord", (fun (x y : UInt64) => booleanHelperReturnWord x y)),
   ("booleanHelperReturnBoolean", (fun (x y : UInt64) => booleanHelperReturnBoolean x y)),
   ("booleanHelperReturnNested", (fun (x y : UInt64) => booleanHelperReturnNested x y)),
   ("booleanHelperReturnCondition", (fun (x y : UInt64) => booleanHelperReturnCondition x y)),
   ("booleanHelperReturnCaptured", (fun (x y : UInt64) => booleanHelperReturnCaptured x y)),
   ("booleanHelperReturnIgnored", (fun (x y : UInt64) => booleanHelperReturnIgnored x y)),
   ("booleanPropRelationDecision", (fun (x y : UInt64) => (booleanPropRelationDecision (x != 0) (y != 0)).toUInt64)),
   ("booleanPropRelationMixed", (fun (x y : UInt64) => booleanPropRelationMixed (x != 0) (y != 0))),
   ("booleanPropRelationNegated", (fun (x y : UInt64) => (booleanPropRelationNegated (x != 0) (y != 0)).toUInt64)),
   ("booleanPropRelationWords", (fun (x y : UInt64) => booleanPropRelationWords x y)),
   ("booleanPropRelationHelpers", (fun (x y : UInt64) => (booleanPropRelationHelpers x y).toUInt64)),
   ("booleanPropRelationLet", (fun (x y : UInt64) => booleanPropRelationLet x y)),
   ("predicateBodyWordRepeated", (fun (x y : UInt64) => predicateBodyWordRepeated x y)),
   ("predicateBodyWordBoolean", (fun (x y : UInt64) => predicateBodyWordBoolean x y)),
   ("predicateBodyWordUnused", (fun (x y : UInt64) => predicateBodyWordUnused x y)),
   ("predicateBodyWordCapture", (fun (x y : UInt64) => predicateBodyWordCapture x y)),
   ("predicateBodyWordProposition", (fun (x y : UInt64) => predicateBodyWordProposition x y)),
   ("predicateBodyWordDo", (fun (x y : UInt64) => predicateBodyWordDo x y)),
   ("booleanHelperBodyNested", (fun (x y : UInt64) => booleanHelperBodyNested x y)),
   ("booleanHelperBodyWrapped", (fun (x y : UInt64) => booleanHelperBodyWrapped x y)),
   ("booleanHelperBodyMixed", (fun (x y : UInt64) => booleanHelperBodyMixed x y)),
   ("booleanHelperBodyCaptures", (fun (x y : UInt64) => booleanHelperBodyCaptures x y)),
   ("booleanHelperBodyUnused", (fun (x y : UInt64) => booleanHelperBodyUnused x y)),
   ("booleanHelperBodyChoice", (fun (x y : UInt64) => booleanHelperBodyChoice x y)),
   ("propositionHelperLetCompound", (fun (x y : UInt64) => propositionHelperLetCompound x y)),
   ("propositionHelperLetBoolean", (fun (x y : UInt64) => propositionHelperLetBoolean x y)),
   ("propositionHelperLetDecision", (fun (x y : UInt64) => propositionHelperLetDecision x y)),
   ("propositionHelperLetDependent", (fun (x y : UInt64) => propositionHelperLetDependent x y)),
   ("propositionHelperLetUnused", (fun (x y : UInt64) => propositionHelperLetUnused x y)),
   ("propositionHelperLetNested", (fun (x y : UInt64) => propositionHelperLetNested x y)),
   ("booleanHelperRelationChoiceLeft", (fun (x y : UInt64) => booleanHelperRelationChoiceLeft x y)),
   ("booleanHelperRelationChoiceRight", (fun (x y : UInt64) => booleanHelperRelationChoiceRight x y)),
   ("booleanHelperRelationChoiceFalse", (fun (x y : UInt64) => booleanHelperRelationChoiceFalse x y)),
   ("booleanHelperRelationChoiceDependent", (fun (x y : UInt64) => booleanHelperRelationChoiceDependent x y)),
   ("booleanHelperRelationChoiceTrue", (fun (x y : UInt64) => booleanHelperRelationChoiceTrue x y)),
   ("booleanHelperRelationChoiceNested", (fun (x y : UInt64) => booleanHelperRelationChoiceNested x y)),
   ("booleanHelperPropositionChoiceWord", (fun (x y : UInt64) => booleanHelperPropositionChoiceWord x y)),
   ("booleanHelperPropositionChoiceLe", (fun (x y : UInt64) => booleanHelperPropositionChoiceLe x y)),
   ("booleanHelperPropositionChoiceCompound", (fun (x y : UInt64) => booleanHelperPropositionChoiceCompound x y)),
   ("booleanHelperPropositionChoiceDependent", (fun (x y : UInt64) => booleanHelperPropositionChoiceDependent x y)),
   ("booleanHelperPropositionChoiceNegated", (fun (x y : UInt64) => booleanHelperPropositionChoiceNegated x y)),
   ("booleanHelperPropositionChoiceLet", (fun (x y : UInt64) => booleanHelperPropositionChoiceLet x y)),
   ("booleanHelperChoiceCondition", (fun (x y : UInt64) => booleanHelperChoiceCondition x y)),
   ("booleanHelperChoiceYes", (fun (x y : UInt64) => booleanHelperChoiceYes x y)),
   ("booleanHelperChoiceNo", (fun (x y : UInt64) => booleanHelperChoiceNo x y)),
   ("booleanHelperChoiceDependent", (fun (x y : UInt64) => booleanHelperChoiceDependent x y)),
   ("booleanHelperChoiceNested", (fun (x y : UInt64) => booleanHelperChoiceNested x y)),
   ("booleanHelperChoiceUnused", (fun (x y : UInt64) => booleanHelperChoiceUnused x y)),
   ("booleanHelperEqualityLeft", (fun (x y : UInt64) => booleanHelperEqualityLeft x y)),
   ("booleanHelperEqualityRight", (fun (x y : UInt64) => booleanHelperEqualityRight x y)),
   ("booleanHelperEqualityBoth", (fun (x y : UInt64) => booleanHelperEqualityBoth x y)),
   ("booleanHelperEqualityDependent", (fun (x y : UInt64) => booleanHelperEqualityDependent x y)),
   ("booleanHelperEqualityNested", (fun (x y : UInt64) => booleanHelperEqualityNested x y)),
   ("booleanHelperEqualityUnused", (fun (x y : UInt64) => booleanHelperEqualityUnused x y)),
   ("booleanHelperJunctionLeft", (fun (x y : UInt64) => booleanHelperJunctionLeft x y)),
   ("booleanHelperJunctionRight", (fun (x y : UInt64) => booleanHelperJunctionRight x y)),
   ("booleanHelperJunctionBoth", (fun (x y : UInt64) => booleanHelperJunctionBoth x y)),
   ("booleanHelperJunctionDependent", (fun (x y : UInt64) => booleanHelperJunctionDependent x y)),
   ("booleanHelperJunctionNested", (fun (x y : UInt64) => booleanHelperJunctionNested x y)),
   ("booleanHelperJunctionUnused", (fun (x y : UInt64) => booleanHelperJunctionUnused x y)),
   ("booleanHelperNegationWord", (fun (x y : UInt64) => booleanHelperNegationWord x y)),
   ("booleanHelperNegationBoolean", (fun (x y : UInt64) => booleanHelperNegationBoolean x y)),
   ("booleanHelperNegationDependent", (fun (x y : UInt64) => booleanHelperNegationDependent x y)),
   ("booleanHelperNegationNested", (fun (x y : UInt64) => booleanHelperNegationNested x y)),
   ("booleanHelperNegationUnused", (fun (x y : UInt64) => booleanHelperNegationUnused x y)),
   ("booleanHelperNegationIdResult", (fun (x y : UInt64) => booleanHelperNegationIdResult x y)),
   ("booleanInnerWrapperWord", (fun (x y : UInt64) => booleanInnerWrapperWord x y)),
   ("booleanInnerWrapperBoolean", (fun (x y : UInt64) => booleanInnerWrapperBoolean x y)),
   ("booleanInnerWrapperDependent", (fun (x y : UInt64) => booleanInnerWrapperDependent x y)),
   ("booleanInnerWrapperNested", (fun (x y : UInt64) => booleanInnerWrapperNested x y)),
   ("booleanInnerWrapperUnused", (fun (x y : UInt64) => booleanInnerWrapperUnused x y)),
   ("booleanInnerWrapperIdResult", (fun (x y : UInt64) => booleanInnerWrapperIdResult x y)),
   ("booleanInnerHelperWord", (fun (x y : UInt64) => booleanInnerHelperWord x y)),
   ("booleanInnerHelperBoolean", (fun (x y : UInt64) => booleanInnerHelperBoolean x y)),
   ("booleanInnerHelperDependent", (fun (x y : UInt64) => booleanInnerHelperDependent x y)),
   ("booleanInnerHelperNested", (fun (x y : UInt64) => booleanInnerHelperNested x y)),
   ("booleanInnerHelperUnused", (fun (x y : UInt64) => booleanInnerHelperUnused x y)),
   ("booleanInnerHelperIdResult", (fun (x y : UInt64) => booleanInnerHelperIdResult x y)),
   ("booleanPropLetRelationWord", (fun (x y : UInt64) => booleanPropLetRelationWord x y)),
   ("booleanPropLetRelationDecision", (fun (x y : UInt64) => (booleanPropLetRelationDecision x y).toUInt64)),
   ("booleanPropLetRelationDependent", (fun (x y : UInt64) => (booleanPropLetRelationDependent x y).toUInt64)),
   ("booleanPropLetRelationNested", (fun (x y : UInt64) => (booleanPropLetRelationNested x y).toUInt64)),
   ("booleanPropLetRelationHelper", (fun (x y : UInt64) => booleanPropLetRelationHelper x y)),
   ("booleanPropLetRelationUnused", (fun (x y : UInt64) => booleanPropLetRelationUnused x y)),
   ("publicFlagWord", (fun x y => publicFlagWord (x != 0) y)),
   ("publicWordFlag", (fun x y => publicWordFlag x (y != 0))),
   ("publicFlagsWord", (fun x y => publicFlagsWord (x != 0) (y != 0))),
   ("publicFlagResult", (fun x y => (publicFlagResult (x != 0) y).toUInt64)),
   ("publicWordFlagResult", (fun x y => (publicWordFlagResult x (y != 0)).toUInt64)),
   ("publicFlagsResult", (fun x y => (publicFlagsResult (x != 0) (y != 0)).toUInt64)),
   ("publicFlagLet", (fun x y => publicFlagLet (x != 0) y)),
   ("publicFlagBind", (fun x y => Id.run (publicFlagBind x (y != 0)))),
   ("publicFlagCapture", (fun x y => (publicFlagCapture (x != 0) y).toUInt64)),
   ("publicFlagsDecision", (fun x y => (publicFlagsDecision (x != 0) (y != 0)).toUInt64)),
   ("publicIdWord", (fun x y => Id.run (publicIdWord x y))),
   ("publicIdNested", (fun x y => Id.run (publicIdNested x y))),
   ("publicIdBind", (fun x y => Id.run (publicIdBind x y))),
   ("publicIdBool", (fun x y => (publicIdBool x y).toUInt64)),
   ("publicIdBoolNested", (fun x y => (publicIdBoolNested x y).toUInt64)),
   ("publicIdBoolHelper", (fun x y => (publicIdBoolHelper x y).toUInt64)),
   ("publicBooleanTrue", fun x y => (publicBooleanTrue x y).toUInt64),
   ("publicBooleanCompare", fun x y => (publicBooleanCompare x y).toUInt64),
   ("publicBooleanChoice", fun x y => (publicBooleanChoice x y).toUInt64),
   ("publicBooleanDependent", fun x y => (publicBooleanDependent x y).toUInt64),
   ("publicBooleanLet", fun x y => (publicBooleanLet x y).toUInt64),
   ("publicBooleanDo", fun x y => (publicBooleanDo x y).toUInt64),
   ("publicBooleanNamed", fun x y => (publicBooleanNamed x y).toUInt64),
   ("publicBooleanCaptured", fun x y => (publicBooleanCaptured x y).toUInt64),
   ("publicBooleanDecision", fun x y => (publicBooleanDecision x y).toUInt64),
   ("publicBooleanWrapped", fun x y => (publicBooleanWrapped x y).toUInt64),
   ("booleanCallArgumentNested", booleanCallArgumentNested),
   ("booleanCallArgumentWord", booleanCallArgumentWord),
   ("booleanCallArgumentChoice", booleanCallArgumentChoice),
   ("booleanCallArgumentBind", booleanCallArgumentBind),
   ("booleanCallArgumentCapture", booleanCallArgumentCapture),
   ("booleanCallArgumentDecision", booleanCallArgumentDecision),
   ("booleanInputWord", booleanInputWord),
   ("booleanInputPredicate", booleanInputPredicate),
   ("booleanInputNested", booleanInputNested),
   ("booleanInputUnused", booleanInputUnused),
   ("booleanInputDecision", booleanInputDecision),
   ("booleanInputBind", booleanInputBind),
   ("booleanPredicateResultBool", booleanPredicateResultBool),
   ("booleanPredicateResultWord", booleanPredicateResultWord),
   ("booleanPredicateResultNested", booleanPredicateResultNested),
   ("booleanPredicateResultCapture", booleanPredicateResultCapture),
   ("booleanPredicateResultUnused", booleanPredicateResultUnused),
   ("booleanPredicateResultWrapped", booleanPredicateResultWrapped),
   ("booleanPredicateBind", booleanPredicateBind),
   ("booleanPredicateBindNested", booleanPredicateBindNested),
   ("booleanPredicateBindChoice", booleanPredicateBindChoice),
   ("booleanPredicateBindCapture", booleanPredicateBindCapture),
   ("booleanPredicateBindUnused", booleanPredicateBindUnused),
   ("booleanPredicateBindBody", booleanPredicateBindBody),
   ("booleanPredicateWrapper", booleanPredicateWrapper),
   ("booleanPredicateWrapperNested", booleanPredicateWrapperNested),
   ("booleanPredicateWrapperLet", booleanPredicateWrapperLet),
   ("booleanPredicateWrapperCondition", booleanPredicateWrapperCondition),
   ("booleanPredicateWrapperArgument", booleanPredicateWrapperArgument),
   ("booleanPredicateWrapperBody", booleanPredicateWrapperBody),
   ("booleanPredicateCondition", booleanPredicateCondition),
   ("booleanPredicateConditionRelations", booleanPredicateConditionRelations),
   ("booleanPredicateConditionDependent", booleanPredicateConditionDependent),
   ("booleanPredicateConditionNested", booleanPredicateConditionNested),
   ("booleanPredicateConditionCapture", booleanPredicateConditionCapture),
   ("booleanPredicateConditionBody", booleanPredicateConditionBody),
   ("booleanPredicateLet", booleanPredicateLet),
   ("booleanPredicateLetNested", booleanPredicateLetNested),
   ("booleanPredicateLetChoice", booleanPredicateLetChoice),
   ("booleanPredicateLetCapture", booleanPredicateLetCapture),
   ("booleanPredicateLetUnused", booleanPredicateLetUnused),
   ("booleanPredicateLetBody", booleanPredicateLetBody),
   ("booleanPredicateProposition", booleanPredicateProposition),
   ("booleanPredicatePropositionDependent", booleanPredicatePropositionDependent),
   ("booleanPredicatePropositionNested", booleanPredicatePropositionNested),
   ("booleanPredicatePropositionArgument", booleanPredicatePropositionArgument),
   ("booleanPredicatePropositionCapture", booleanPredicatePropositionCapture),
   ("booleanPredicatePropositionBody", booleanPredicatePropositionBody),
   ("booleanPredicateChoice", booleanPredicateChoice),
   ("booleanPredicateChoiceDependent", booleanPredicateChoiceDependent),
   ("booleanPredicateChoiceNested", booleanPredicateChoiceNested),
   ("booleanPredicateChoiceArgument", booleanPredicateChoiceArgument),
   ("booleanPredicateChoiceBranches", booleanPredicateChoiceBranches),
   ("booleanPredicateChoiceBody", booleanPredicateChoiceBody),
   ("booleanPredicateEqual", booleanPredicateEqual),
   ("booleanPredicateDecideEqual", booleanPredicateDecideEqual),
   ("booleanPredicateEqualityNot", booleanPredicateEqualityNot),
   ("booleanPredicateEqualityMixed", booleanPredicateEqualityMixed),
   ("booleanPredicateEqualityArgument", booleanPredicateEqualityArgument),
   ("booleanPredicateEqualityBody", booleanPredicateEqualityBody),
   ("booleanPredicateAndOr", booleanPredicateAndOr),
   ("booleanPredicateJunctionNot", booleanPredicateJunctionNot),
   ("booleanPredicateJunctionMixed", booleanPredicateJunctionMixed),
   ("booleanPredicateJunctionArgument", booleanPredicateJunctionArgument),
   ("booleanPredicateJunctionBody", booleanPredicateJunctionBody),
   ("booleanPredicateJunctionId", booleanPredicateJunctionId),
   ("booleanPredicateCompose", booleanPredicateCompose),
   ("booleanPredicateComposeRepeat", booleanPredicateComposeRepeat),
   ("booleanPredicateComposeNot", booleanPredicateComposeNot),
   ("booleanPredicateComposeCapture", booleanPredicateComposeCapture),
   ("booleanPredicateComposeBody", booleanPredicateComposeBody),
   ("booleanPredicateComposeId", booleanPredicateComposeId),
   ("booleanPredicateNot", booleanPredicateNot),
   ("booleanPredicateNotTwice", booleanPredicateNotTwice),
   ("booleanPredicateNotThrice", booleanPredicateNotThrice),
   ("booleanPredicateNotCapture", booleanPredicateNotCapture),
   ("booleanPredicateNotNested", booleanPredicateNotNested),
   ("booleanPredicateNotId", booleanPredicateNotId),
   ("booleanPredicateTwice", booleanPredicateTwice),
   ("booleanPredicateCapture", booleanPredicateCapture),
   ("booleanPredicateWordCapture", booleanPredicateWordCapture),
   ("booleanPredicateNested", booleanPredicateNested),
   ("booleanPredicateScalarCapture", booleanPredicateScalarCapture),
   ("booleanPredicateShadow", booleanPredicateShadow),
   ("booleanPredicateDependent", booleanPredicateDependent),
   ("booleanPredicateId", booleanPredicateId),
   ("booleanPredicateUnused", booleanPredicateUnused),
   ("booleanPredicateDo", booleanPredicateDo),
   ("boolWordBooleanHelper", boolWordBooleanHelper),
   ("predicateInputRepeated", predicateInputRepeated),
   ("predicateInputNested", predicateInputNested),
   ("predicateInputCapture", predicateInputCapture),
   ("predicateInputShadow", predicateInputShadow),
   ("predicateInputUnused", predicateInputUnused),
   ("predicateInputDo", predicateInputDo),
("wrapping", wrapping), ("quotient", quotient), ("remainder", remainder),
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
   ("decideUnused", decideUnused),
   ("boolWordDirect", boolWordDirect),
   ("boolWordCaptured", boolWordCaptured),
   ("boolWordAction", boolWordAction),
   ("boolWordLiterals", boolWordLiterals),
   ("boolWordChoice", boolWordChoice),
   ("boolWordNested", boolWordNested),
   ("boolWordDependent", boolWordDependent),
   ("boolWordUnused", boolWordUnused),
   ("boolEqDirect", boolEqDirect),
   ("boolEqCalls", boolEqCalls),
   ("boolEqConditional", boolEqConditional),
   ("boolEqCapture", boolEqCapture),
   ("boolEqLiterals", boolEqLiterals),
   ("boolEqChoices", boolEqChoices),
   ("boolEqNested", boolEqNested),
   ("boolEqDo", boolEqDo),
   ("boolPropEqual", boolPropEqual),
   ("boolPropUnequal", boolPropUnequal),
   ("boolPropLiterals", boolPropLiterals),
   ("boolPropDependent", boolPropDependent),
   ("boolPropTruth", boolPropTruth),
   ("boolPropChoices", boolPropChoices),
   ("boolPropDo", boolPropDo),
   ("boolPropEarly", boolPropEarly),
   ("localDecideEqual", localDecideEqual),
   ("localDecideTruth", localDecideTruth),
   ("localDecideImplicit", localDecideImplicit),
   ("localDecideNested", localDecideNested),
   ("localDecideLiterals", localDecideLiterals),
   ("localDecideCapture", localDecideCapture),
   ("localDecideDo", localDecideDo),
   ("localDecideChoices", localDecideChoices),
   ("relationChoiceEqual", relationChoiceEqual),
   ("relationChoiceUnequal", relationChoiceUnequal),
   ("relationChoiceNested", relationChoiceNested),
   ("relationChoiceCapture", relationChoiceCapture),
   ("relationChoiceLiterals", relationChoiceLiterals),
   ("relationChoiceDo", relationChoiceDo),
   ("relationChoiceTruth", relationChoiceTruth),
   ("relationChoiceUnused", relationChoiceUnused),
   ("dependentChoiceEqual", dependentChoiceEqual),
   ("dependentChoiceProposition", dependentChoiceProposition),
   ("dependentChoiceNested", dependentChoiceNested),
   ("dependentChoiceCapture", dependentChoiceCapture),
   ("dependentChoiceLiterals", dependentChoiceLiterals),
   ("dependentChoiceDo", dependentChoiceDo),
   ("dependentChoiceTruth", dependentChoiceTruth),
   ("dependentChoiceUnused", dependentChoiceUnused),
   ("boolLetNested", boolLetNested),
   ("boolLetCapture", boolLetCapture),
   ("boolLetShadow", boolLetShadow),
   ("boolLetUnused", boolLetUnused),
   ("boolLetDependent", boolLetDependent),
   ("boolLetHelper", boolLetHelper),
   ("boolLetDo", boolLetDo),
   ("boolLetNegated", boolLetNegated),
   ("boolWordLetOriginal", boolWordLetOriginal),
   ("boolWordLetMixed", boolWordLetMixed),
   ("boolWordLetShadow", boolWordLetShadow),
   ("boolWordLetHelper", boolWordLetHelper),
   ("boolWordLetDependent", boolWordLetDependent),
   ("boolWordLetUnused", boolWordLetUnused),
   ("boolWordLetDo", boolWordLetDo),
   ("boolWordLetNegated", boolWordLetNegated),
   ("annotatedLetBoolean", annotatedLetBoolean),
   ("annotatedLetWord", annotatedLetWord),
   ("annotatedLetNested", annotatedLetNested),
   ("annotatedLetHelper", annotatedLetHelper),
   ("annotatedLetUnused", annotatedLetUnused),
   ("annotatedLetDo", annotatedLetDo),
   ("annotatedLetNegated", annotatedLetNegated),
   ("annotatedLetShadow", annotatedLetShadow),
   ("nestedIdOperators", nestedIdOperators),
   ("nestedIdBinding", nestedIdBinding),
   ("nestedIdNested", nestedIdNested),
   ("nestedIdHelper", nestedIdHelper),
   ("nestedIdDo", nestedIdDo),
   ("nestedIdDependent", nestedIdDependent),
   ("nestedIdUnused", nestedIdUnused),
   ("nestedIdShadow", nestedIdShadow),
   ("idLetWord", idLetWord),
   ("idLetBoolean", idLetBoolean),
   ("idLetLiteral", idLetLiteral),
   ("idLetHelper", idLetHelper),
   ("idLetShadow", idLetShadow),
   ("idLetOverflow", idLetOverflow),
   ("idLetUnused", idLetUnused),
   ("idLetDo", idLetDo),
   ("idArithmeticLeft", idArithmeticLeft),
   ("idArithmeticRight", idArithmeticRight),
   ("idArithmeticBoth", idArithmeticBoth),
   ("idArithmeticBitwise", idArithmeticBitwise),
   ("idArithmeticDivision", idArithmeticDivision),
   ("idArithmeticShifts", idArithmeticShifts),
   ("idArithmeticHelper", idArithmeticHelper),
   ("idArithmeticDo", idArithmeticDo),
   ("idComparisonEq", idComparisonEq),
   ("idComparisonNe", idComparisonNe),
   ("idComparisonLt", idComparisonLt),
   ("idComparisonLe", idComparisonLe),
   ("idComparisonGt", idComparisonGt),
   ("idComparisonGe", idComparisonGe),
   ("idComparisonNegated", idComparisonNegated),
   ("idComparisonCompound", idComparisonCompound),
   ("idComparisonDependent", idComparisonDependent),
   ("idComparisonDecide", idComparisonDecide),
   ("idComparisonChoice", idComparisonChoice),
   ("idComparisonDo", idComparisonDo),
   ("reannotatedEq", reannotatedEq),
   ("reannotatedNe", reannotatedNe),
   ("reannotatedLt", reannotatedLt),
   ("reannotatedLe", reannotatedLe),
   ("reannotatedGt", reannotatedGt),
   ("reannotatedGe", reannotatedGe),
   ("reannotatedNegated", reannotatedNegated),
   ("reannotatedHelper", reannotatedHelper),
   ("reannotatedDo", reannotatedDo),
   ("reannotatedAnd", reannotatedAnd),
   ("reannotatedOr", reannotatedOr),
   ("reannotatedGuardNegation", reannotatedGuardNegation),
   ("reannotatedNestedGuard", reannotatedNestedGuard),
   ("reannotatedGuardHelper", reannotatedGuardHelper),
   ("reannotatedGuardDo", reannotatedGuardDo),
   ("dependentReannotatedEq", dependentReannotatedEq),
   ("dependentReannotatedOrder", dependentReannotatedOrder),
   ("dependentReannotatedCompound", dependentReannotatedCompound),
   ("dependentReannotatedNested", dependentReannotatedNested),
   ("dependentReannotatedHelper", dependentReannotatedHelper),
   ("dependentReannotatedDo", dependentReannotatedDo),
   ("savedReannotatedDecide", savedReannotatedDecide),
   ("savedReannotatedNested", savedReannotatedNested),
   ("savedReannotatedChoice", savedReannotatedChoice),
   ("savedReannotatedDependentChoice", savedReannotatedDependentChoice),
   ("savedReannotatedDo", savedReannotatedDo),
   ("savedReannotatedHelper", savedReannotatedHelper),
   ("savedReannotatedCaptured", savedReannotatedCaptured),
   ("savedReannotatedUnused", savedReannotatedUnused),
   ("booleanApplyWord", booleanApplyWord),
   ("booleanApplyBool", booleanApplyBool),
   ("booleanApplyCapture", booleanApplyCapture),
   ("booleanApplyNested", booleanApplyNested),
   ("booleanApplyDependent", booleanApplyDependent),
   ("booleanApplyId", booleanApplyId),
   ("booleanApplyUnused", booleanApplyUnused),
   ("booleanApplyDo", booleanApplyDo),
   ("reusableBooleanTwice", reusableBooleanTwice),
   ("reusableBooleanCapture", reusableBooleanCapture),
   ("reusableBooleanNested", reusableBooleanNested),
   ("reusableBooleanScalarCapture", reusableBooleanScalarCapture),
   ("reusableBooleanShadow", reusableBooleanShadow),
   ("reusableBooleanDependent", reusableBooleanDependent),
   ("reusableBooleanId", reusableBooleanId),
   ("reusableBooleanUnused", reusableBooleanUnused),
   ("reusableBooleanIgnoredArgument", reusableBooleanIgnoredArgument),
   ("reusableBooleanDo", reusableBooleanDo),
   ("namedBooleanWord", namedBooleanWord),
   ("namedBooleanBool", namedBooleanBool),
   ("namedBooleanCapture", namedBooleanCapture),
   ("namedBooleanNested", namedBooleanNested),
   ("namedBooleanDependent", namedBooleanDependent),
   ("namedBooleanId", namedBooleanId),
   ("namedBooleanUnused", namedBooleanUnused),
   ("namedBooleanDo", namedBooleanDo)]

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
