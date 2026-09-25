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
   ("rangeBoolNotFunction", rangeBoolNotFunction)]

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
   ("boolNotProposition", boolNotProposition)]

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
