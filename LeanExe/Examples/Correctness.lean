namespace LeanExe.Examples.Correctness

def shortOrSkipsTrap : UInt64 :=
  if true || ((Array.replicate 1 (0 : UInt64))[5]! == 0) then 1 else 0

def shortAndSkipsTrap : UInt64 :=
  if false && ((Array.replicate 1 (0 : UInt64))[5]! == 0) then 1 else 0

def divByZero : UInt64 :=
  (5 : UInt64) / 0

def modByZero : UInt64 :=
  (5 : UInt64) % 0

def overflow : UInt64 :=
  (18446744073709551615 : UInt64) + 1

def underflow : UInt64 :=
  (0 : UInt64) - 1

def natSubSaturates : Nat :=
  (0 : Nat) - 1

def natSubNormal : Nat :=
  (5 : Nat) - 3

def natAddNormal : Nat :=
  (5 : Nat) + 3

def natMulNormal : Nat :=
  (7 : Nat) * 6

def natDivModNormal (x : Nat) : Nat :=
  (x / 3) * 10 + (x % 3)

def natDivModZero (x : Nat) : Nat :=
  (x / 0) * 10 + (x % 0)

def natAddOverflow : Nat :=
  (18446744073709551615 : Nat) + 1

def natMulOverflow : Nat :=
  (9223372036854775808 : Nat) * 2

def natSuccPred (x : Nat) : Nat :=
  Nat.succ x + Nat.pred x

def natSuccOverflow : Nat :=
  Nat.succ 18446744073709551615

def bitwiseOrXor : UInt64 :=
  UInt64.xor (UInt64.lor (10 : UInt64) (12 : UInt64)) (UInt64.land (10 : UInt64) (12 : UInt64))

def bitwiseNotation : UInt64 :=
  ((10 : UInt64) ||| (12 : UInt64)) ^^^ ((10 : UInt64) &&& (12 : UInt64))

def complementNotation : UInt64 :=
  (~~~(0 : UInt64)) &&& (255 : UInt64)

def u8Complement : Nat :=
  (~~~(0 : UInt8)).toNat

def shiftMasking : UInt64 :=
  UInt64.shiftLeft (1 : UInt64) (65 : UInt64) +
    UInt64.shiftRight (8 : UInt64) (65 : UInt64) * (10 : UInt64)

def shiftNotation : UInt64 :=
  ((1 : UInt64) <<< (65 : UInt64)) +
    (((8 : UInt64) >>> (65 : UInt64)) * (10 : UInt64))

def uint8ShiftNotation : Nat :=
  (((1 : UInt8) <<< (8 : UInt8)).toNat) * 100 +
    (((1 : UInt8) <<< (9 : UInt8)).toNat) * 10 +
    (((128 : UInt8) >>> (1 : UInt8)).toNat)

def uint8DirectShift : Nat :=
  (UInt8.shiftLeft (129 : UInt8) (1 : UInt8)).toNat * 1000 +
    (UInt8.shiftRight (255 : UInt8) (8 : UInt8)).toNat

def uint64OfNatValue (n : Nat) : UInt64 :=
  UInt64.ofNat (n + 1)

def uint64OfHugeNat : UInt64 :=
  UInt64.ofNat 18446744073709551616

def natToUInt64Value (n : Nat) : UInt64 :=
  Nat.toUInt64 (n + 1)

def natToUInt64Huge : UInt64 :=
  Nat.toUInt64 18446744073709551616

def wrappedUInt8Literal : Nat :=
  (300 : UInt8).toNat

def uint64ToUInt8Wrap : Nat :=
  (UInt64.toUInt8 (300 : UInt64)).toNat

def uint8ToUInt64Value : UInt64 :=
  UInt8.toUInt64 (255 : UInt8) + 1

def wrappedUInt32Literal : Nat :=
  (4294967296 : UInt32).toNat

def uint32AddWrap : Nat :=
  (((4294967295 : UInt32) + 1).toNat)

def uint32BitwiseShift : Nat :=
  (((1 : UInt32) <<< (33 : UInt32)).toNat) * 10 +
    (((8 : UInt32) >>> (33 : UInt32)).toNat)

def uint32Complement : Nat :=
  (~~~(0 : UInt32)).toNat

def uint32MinMax : Nat :=
  (min (4000000000 : UInt32) (3 : UInt32)).toNat * 10 +
    (max (4000000000 : UInt32) (3 : UInt32)).toNat

def uint32Comparisons : UInt64 :=
  if (4000000000 : UInt32) > (3 : UInt32) &&
      (3 : UInt32) <= (3 : UInt32) &&
      ((3 : UInt32) == (3 : UInt32)) then
    1
  else
    0

def uint32DivMod : Nat :=
  (((4000000000 : UInt32) / (3 : UInt32)).toNat) * 10 +
    (((4000000000 : UInt32) % (3 : UInt32)).toNat)

def uint32DivModZero : Nat :=
  (((7 : UInt32) / 0).toNat) * 10 + (((7 : UInt32) % 0).toNat)

def uint32ToUInt64Value : UInt64 :=
  UInt32.toUInt64 (4294967295 : UInt32) + 1

def uint64ToUInt32Wrap : Nat :=
  (UInt64.toUInt32 (4294967297 : UInt64)).toNat

def uint8ToUInt32Value : Nat :=
  (UInt8.toUInt32 (255 : UInt8) + (1 : UInt32)).toNat

def uint32ToUInt8Wrap : Nat :=
  (UInt32.toUInt8 (300 : UInt32)).toNat

def uint8OfNatValue (n : Nat) : Nat :=
  (UInt8.ofNat (n + 1)).toNat

def uint8AddWrap : Nat :=
  (((255 : UInt8) + 1).toNat)

def uint8SubWrap : Nat :=
  (((0 : UInt8) - 1).toNat)

def uint8MulWrap : Nat :=
  (((16 : UInt8) * 17).toNat)

def uint8DivModZero : Nat :=
  (((7 : UInt8) / 0).toNat) * 10 + (((7 : UInt8) % 0).toNat)

def nestedShadow (x : UInt64) : UInt64 :=
  let x := x + 1
  let y := (let x := x + 2; x * 10)
  x + y

def unusedScalarLetSkipsTrap : UInt64 :=
  let _unused := (Array.replicate 1 (0 : UInt64))[5]!
  1

def letUsedOnlyInUnusedProductField : UInt64 :=
  (let x := (Array.replicate 1 (0 : UInt64))[5]!
   (x, (7 : UInt64))).2

def ignoreUInt64 (_x : UInt64) : UInt64 :=
  1

def ignoredCallArgSkipsTrap : UInt64 :=
  ignoreUInt64 ((Array.replicate 1 (0 : UInt64))[5]!)

def useOnlyUnusedProductField (x : UInt64) : UInt64 :=
  (x, (7 : UInt64)).2

def callArgUsedOnlyInUnusedProductField : UInt64 :=
  useOnlyUnusedProductField ((Array.replicate 1 (0 : UInt64))[5]!)

def combine (left right : UInt64) : UInt64 :=
  left * (100 : UInt64) + right

def callArgLets (x : UInt64) : UInt64 :=
  combine (let y := x + 1; y) (let z := x + 2; z)

def productLet : UInt64 :=
  let pair := ((1 : UInt64), (2 : UInt64))
  pair.1 * (10 : UInt64) + pair.2

def nestedProduct : UInt64 :=
  let pair := (((1 : UInt64), (2 : UInt64)), ((3 : UInt64), (4 : UInt64)))
  pair.1.2 * (100 : UInt64) + pair.2.1

def productSkipsUnusedField : UInt64 :=
  let pair := ((Array.replicate 1 (0 : UInt64))[5]!, (7 : UInt64))
  pair.2

def productBranch (flag : UInt64) : UInt64 :=
  let pair :=
    if flag == 0 then
      ((1 : UInt64), (2 : UInt64))
    else
      ((3 : UInt64), (4 : UInt64))
  pair.1 * (10 : UInt64) + pair.2

def productMatchDestructure : UInt64 :=
  match ((1 : UInt64), (2 : UInt64)) with
  | (left, right) => left * (10 : UInt64) + right

def productMatchUsesFirstOnly : UInt64 :=
  match ((7 : UInt64), (Array.replicate 0 (0 : UInt64)).back!) with
  | (left, _right) => left

def productMatchCondition : UInt64 :=
  if (
    match ((2 : Nat), (5 : Nat)) with
    | (left, right) => left < right
  )
  then
    1
  else
    0

def productMatchNested : UInt64 :=
  let pair :=
    match (((1 : UInt64), (2 : UInt64)), ((3 : UInt64), (4 : UInt64))) with
    | (left, right) => (left.2, right.1)
  pair.1 * (10 : UInt64) + pair.2

def makePairHelper (x : UInt64) : UInt64 × UInt64 :=
  (x, x + 1)

def productHelperResult : UInt64 :=
  let pair := makePairHelper 4
  pair.1 * (10 : UInt64) + pair.2

def productFirstHelper (pair : UInt64 × UInt64) : UInt64 :=
  pair.1

def productHelperParamSkipsTrap : UInt64 :=
  productFirstHelper ((7 : UInt64), (Array.replicate 0 (0 : UInt64)).back!)

def unitArgHelper (_value : Unit) : UInt64 :=
  11

def unitResultHelper : Unit :=
  ()

def unitProductSecond : UInt64 :=
  let pair := ((), (7 : UInt64))
  pair.2

def unitHelperCall : UInt64 :=
  unitArgHelper ()

def unitResultIgnored : UInt64 :=
  let value := unitResultHelper
  let pair := (value, (12 : UInt64))
  pair.2

def arrayUpdateRead : UInt64 :=
  let a := Array.replicate 2 (0 : UInt64)
  let b := a.set! 0 1
  let c := b.set! 1 (b[0]! + a[0]!)
  c[0]! * (100 : UInt64) + c[1]! * (10 : UInt64) + a[0]!

def arraySizeAfterSet : Nat :=
  let a := Array.replicate 3 (0 : UInt64)
  let b := a.set! 1 9
  b.size

def arrayPushRead : UInt64 :=
  let a := (Array.replicate 2 (0 : UInt64)).set! 0 5
  let b := a.push 7
  if b.size == 3 && a.size == 2 then
    b[0]! * (100 : UInt64) + b[2]!
  else
    0

def nonzeroReplicateRead : UInt64 :=
  let a := Array.replicate 3 (7 : UInt64)
  if a.size == 3 then
    a[0]! * (10 : UInt64) + a[2]!
  else
    0

def arrayPopRead : UInt64 :=
  let a := (Array.replicate 2 (4 : UInt64)).push 9
  let b := a.pop
  let c := (Array.replicate 0 (7 : UInt64)).pop
  if a.size == 3 && b.size == 2 && c.size == 0 then
    b[0]! * (10 : UInt64) + b[1]!
  else
    0

def arrayAppendRead : UInt64 :=
  let a := ((Array.replicate 2 (0 : UInt64)).set! 0 11).set! 1 22
  let b := ((Array.replicate 2 (0 : UInt64)).set! 0 33).set! 1 44
  let c := a.append b
  if a.size == 2 && b.size == 2 && c.size == 4 then
    c[0]! * (1000000 : UInt64) + c[1]! * (10000 : UInt64) +
      c[2]! * (100 : UInt64) + c[3]!
  else
    0

def arrayAppendEmptySides : UInt64 :=
  let empty := Array.replicate 0 (99 : UInt64)
  let values := ((Array.replicate 2 (0 : UInt64)).set! 0 7).set! 1 8
  let leftEmpty := empty.append values
  let rightEmpty := values.append empty
  if leftEmpty.size == 2 && rightEmpty.size == 2 then
    leftEmpty[0]! * (1000 : UInt64) + leftEmpty[1]! * (100 : UInt64) +
      rightEmpty[0]! * (10 : UInt64) + rightEmpty[1]!
  else
    0

def arrayExtractRead : UInt64 :=
  let a := ((((Array.replicate 4 (0 : UInt64)).set! 0 10).set! 1 20).set! 2 30).set! 3 40
  let b := a.extract 1 3
  if a.size == 4 && b.size == 2 then
    b[0]! * (10 : UInt64) + b[1]!
  else
    0

def arrayExtractClamps : UInt64 :=
  let a := ((((Array.replicate 4 (0 : UInt64)).set! 0 10).set! 1 20).set! 2 30).set! 3 40
  let b := a.extract 2 10
  let c := a.extract 5 10
  let d := a.extract 3 1
  if b.size == 2 && c.isEmpty && d.isEmpty then
    b[0]! * (10 : UInt64) + b[1]!
  else
    0

def arrayLiteralRead : UInt64 :=
  let a : Array UInt64 := #[10, 20, 30]
  if a.size == 3 then
    a[0]! * (100 : UInt64) + a[2]!
  else
    0

def arrayEmptyLiteral : UInt64 :=
  let a : Array UInt64 := #[]
  if a.isEmpty then 1 else 0

def arrayEmptyConstructors : UInt64 :=
  let a : Array UInt64 := Array.empty
  let b : Array UInt64 := Array.mkEmpty 10
  let c : Array UInt64 := Array.emptyWithCapacity 20
  if a.isEmpty && b.isEmpty && c.isEmpty then 1 else 0

def arrayEmptyCapacitySkipsTrap : UInt64 :=
  let capacity := ((Array.replicate 0 (0 : UInt64)).back!).toNat
  let a : Array UInt64 := Array.emptyWithCapacity capacity
  if a.isEmpty then 1 else 0

def arraySingletonRead : UInt64 :=
  let a := Array.singleton (42 : UInt64)
  if a.size == 1 then a[0]! else 0

def arrayIsEmptyValues : UInt64 :=
  let empty := Array.replicate 0 (0 : UInt64)
  let filled := Array.replicate 1 (0 : UInt64)
  if empty.isEmpty && !filled.isEmpty then 1 else 0

def arrayBackRead : UInt64 :=
  ((Array.replicate 2 (4 : UInt64)).push 9).back!

def arrayBackEmptyTrap : UInt64 :=
  (Array.replicate 0 (4 : UInt64)).back!

def arrayGetDRead (i : Nat) : UInt64 :=
  (Array.replicate 2 (7 : UInt64)).getD i 99

def arrayGetDSkipsDefaultTrap : UInt64 :=
  (Array.replicate 1 (5 : UInt64)).getD 0 ((Array.replicate 0 (0 : UInt64)).back!)

def arrayGetQuestionRead (i : Nat) : UInt64 :=
  match (Array.replicate 2 (7 : UInt64))[i]? with
  | some value => value + 1
  | none => 99

def arrayGetQuestionGetDSkipsDefaultTrap : UInt64 :=
  ((Array.replicate 1 (5 : UInt64))[0]?).getD ((Array.replicate 0 (0 : UInt64)).back!)

def arrayGetQuestionNoneSkipsPayloadTrap : UInt64 :=
  match (Array.replicate 0 (0 : UInt64))[0]? with
  | some value => value
  | none => 5

def productArrayAlias : UInt64 :=
  let a := (Array.replicate 2 (0 : UInt64)).set! 0 11
  let pair := (a, a.set! 0 22)
  pair.2[0]! * (100 : UInt64) + pair.1[0]!

def recLetFuel : Nat → UInt64 → UInt64 → UInt64
  | 0, left, right => combine left right
  | fuel + 1, left, right =>
      recLetFuel fuel (let next := left + 1; next) (let next := right + 2; next)

def recLetDemo : UInt64 :=
  recLetFuel 4 1 10

def recExitFuel : Nat → UInt64 → UInt64 → UInt64
  | 0, left, right => combine left right
  | fuel + 1, left, right =>
      if left == 3 then
        combine left right
      else
        recExitFuel fuel (left + 1) (right + 2)

def recExitDemo : UInt64 :=
  recExitFuel 10 1 10

def recThenBranchFuel : Nat → UInt64 → UInt64
  | 0, acc => acc
  | fuel + 1, acc =>
      if acc < (3 : UInt64) then
        recThenBranchFuel fuel (acc + 1)
      else
        acc + 10

def recThenBranchExitDemo : UInt64 :=
  recThenBranchFuel 10 0

def recThenBranchFuelDemo : UInt64 :=
  recThenBranchFuel 2 0

def recProductFuel : Nat → UInt64 → UInt64
  | 0, acc => acc
  | fuel + 1, acc =>
      recProductFuel fuel (let pair := (acc + 1, acc + 2); pair.2)

def recProductDemo : UInt64 :=
  recProductFuel 5 0

def recIgnoreTrapArgFuel : Nat → UInt64 → UInt64
  | 0, _value => 7
  | fuel + 1, value => recIgnoreTrapArgFuel fuel value

def recursiveDemandedFuelGet : UInt64 :=
  recIgnoreTrapArgFuel ((Array.replicate 1 (0 : UInt64))[0]!).toNat 99

def rejectRecursiveIgnoredTrapArg : UInt64 :=
  recIgnoreTrapArgFuel 0 ((Array.replicate 1 (0 : UInt64))[5]!)

def hiddenTrap : UInt64 :=
  (Array.replicate 1 (0 : UInt64))[5]!

def rejectRecursiveIgnoredHiddenTrapArg : UInt64 :=
  recIgnoreTrapArgFuel 0 hiddenTrap

def optionSomeMatch : UInt64 :=
  match (some (7 : UInt64) : Option UInt64) with
  | none => 0
  | some value => value + 1

def optionSomeFirstMatch : UInt64 :=
  match (some (7 : UInt64) : Option UInt64) with
  | some value => value + 1
  | none => 0

def optionNoneMatchSkipsSomeArm : UInt64 :=
  match (none : Option UInt64) with
  | none => 5
  | some _value => (Array.replicate 1 (0 : UInt64))[5]!

def optionSomeMatchSkipsUnusedPayload : UInt64 :=
  match (some ((Array.replicate 1 (0 : UInt64))[5]!) : Option UInt64) with
  | none => 0
  | some _value => 9

def optionLet : UInt64 :=
  let found : Option UInt64 := some 9
  match found with
  | none => 0
  | some value => value * 2

def optionBranch (flag : UInt64) : UInt64 :=
  let found : Option UInt64 :=
    if flag == 0 then
      none
    else
      some 33
  match found with
  | none => 11
  | some value => value + 1

def optionIncrementHelper (x : UInt64) : Option UInt64 :=
  if x == 0 then none else some (x + 1)

def optionHelperResult : UInt64 :=
  match optionIncrementHelper 5 with
  | some value => value
  | none => 0

def optionHelperNone : UInt64 :=
  match optionIncrementHelper 0 with
  | some value => value
  | none => 9

def optionParamGetDHelper (value : Option UInt64) : UInt64 :=
  value.getD 9

def optionHelperParam : UInt64 :=
  optionParamGetDHelper (some 3)

def exceptOkMatch : UInt64 :=
  match (Except.ok (7 : UInt64) : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok value => value + 1

def exceptOkFirstMatch : UInt64 :=
  match (Except.ok (7 : UInt64) : Except UInt64 UInt64) with
  | Except.ok value => value + 1
  | Except.error code => code

def exceptErrorMatch : UInt64 :=
  match (Except.error (4 : UInt64) : Except UInt64 UInt64) with
  | Except.error code => code + 10
  | Except.ok value => value

def exceptErrorSkipsUnusedPayloadTrap : UInt64 :=
  match (Except.error ((Array.replicate 0 (0 : UInt64)).back!) : Except UInt64 UInt64) with
  | Except.error _code => 7
  | Except.ok value => value

def exceptMatchCondition : UInt64 :=
  if (
    match (Except.ok (5 : UInt64) : Except UInt64 UInt64) with
    | Except.error _code => false
    | Except.ok value => value > 3
  )
  then
    1
  else
    0

def exceptProductPayload : UInt64 :=
  match (Except.ok ((1 : UInt64), (2 : UInt64)) : Except UInt64 (UInt64 × UInt64)) with
  | Except.error code => code
  | Except.ok pair => pair.1 * (10 : UInt64) + pair.2

def exceptMapOk : UInt64 :=
  match Except.map (fun value : UInt64 => value + 1)
      (Except.ok (5 : UInt64) : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok value => value

def exceptMapErrorSkipsFunctionTrap : UInt64 :=
  match Except.map (fun _value : UInt64 => (Array.replicate 0 (0 : UInt64)).back!)
      (Except.error (7 : UInt64) : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok value => value

def exceptMapProduct : UInt64 :=
  match Except.map (fun value : UInt64 => (value, value + 1))
      (Except.ok (1 : UInt64) : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok pair => pair.1 * (10 : UInt64) + pair.2

def exceptBindOk : UInt64 :=
  match Except.bind (Except.ok (5 : UInt64) : Except UInt64 UInt64)
      (fun value => Except.ok (value + 1)) with
  | Except.error code => code
  | Except.ok value => value

def exceptBindErrorSkipsFunctionTrap : UInt64 :=
  match Except.bind (Except.error (7 : UInt64) : Except UInt64 UInt64)
      (fun _value => Except.ok ((Array.replicate 0 (0 : UInt64)).back!)) with
  | Except.error code => code
  | Except.ok value => value

def exceptBindFunctionError : UInt64 :=
  match Except.bind (Except.ok (5 : UInt64) : Except UInt64 UInt64)
      (fun _value => Except.error (9 : UInt64)) with
  | Except.error code => code
  | Except.ok value => value

def exceptBindProduct : UInt64 :=
  match Except.bind (Except.ok (1 : UInt64) : Except UInt64 UInt64)
      (fun value => Except.ok (value, value + 1)) with
  | Except.error code => code
  | Except.ok pair => pair.1 * (10 : UInt64) + pair.2

def exceptIncrementHelper (x : UInt64) : Except UInt64 UInt64 :=
  if x == 0 then Except.error 9 else Except.ok (x + 1)

def exceptHelperResult : UInt64 :=
  match exceptIncrementHelper 5 with
  | Except.error code => code
  | Except.ok value => value

def exceptHelperError : UInt64 :=
  match exceptIncrementHelper 0 with
  | Except.error code => code
  | Except.ok value => value

def exceptParamHelper (value : Except UInt64 UInt64) : UInt64 :=
  match value with
  | Except.error code => code
  | Except.ok item => item + 1

def exceptHelperParam : UInt64 :=
  exceptParamHelper (Except.ok 3)

def exceptToOptionOk : UInt64 :=
  match Except.toOption (Except.ok (5 : UInt64) : Except UInt64 UInt64) with
  | some value => value + 1
  | none => 0

def exceptToOptionErrorSkipsPayloadTrap : UInt64 :=
  if (Except.toOption
      (Except.error ((Array.replicate 0 (0 : UInt64)).back!) : Except UInt64 UInt64)).isNone then
    1
  else
    0

def optionGetDNone : UInt64 :=
  (none : Option UInt64).getD 7

def optionGetDSomeSkipsDefaultTrap : UInt64 :=
  (some (5 : UInt64)).getD ((Array.replicate 0 (0 : UInt64)).back!)

def optionGetDProduct : UInt64 :=
  let pair := (some ((1 : UInt64), (2 : UInt64))).getD ((3 : UInt64), (4 : UInt64))
  pair.1 * (10 : UInt64) + pair.2

def optionOrElseNone : UInt64 :=
  match ((none : Option UInt64) <|> some 7) with
  | some value => value
  | none => 0

def optionOrElseDirectSomeSkipsFallbackTrap : UInt64 :=
  match Option.orElse (some (5 : UInt64))
      (fun _ => some ((Array.replicate 0 (0 : UInt64)).back!)) with
  | some value => value
  | none => 0

def optionOrElseProduct : UInt64 :=
  match Option.orElse (none : Option (UInt64 × UInt64))
      (fun _ => some ((1 : UInt64), (2 : UInt64))) with
  | some pair => pair.1 * (10 : UInt64) + pair.2
  | none => 0

def optionIsSomeSkipsPayloadTrap : UInt64 :=
  if (some ((Array.replicate 0 (0 : UInt64)).back!) : Option UInt64).isSome then
    1
  else
    0

def optionIsNoneValues : UInt64 :=
  let missing : Option UInt64 := none
  let present : Option UInt64 := some 5
  if missing.isNone && !present.isNone then
    7
  else
    0

def optionElimSomeSkipsDefaultTrap : UInt64 :=
  Option.elim (some (5 : UInt64)) ((Array.replicate 0 (0 : UInt64)).back!)
    (fun value => value + 1)

def optionElimNoneSkipsSomeArmTrap : UInt64 :=
  Option.elim (none : Option UInt64) (7 : UInt64)
    (fun _value => (Array.replicate 0 (0 : UInt64)).back!)

def optionElimProduct : UInt64 :=
  let pair := Option.elim (some (1 : UInt64)) ((3 : UInt64), (4 : UInt64))
    (fun value => (value, value + 1))
  pair.1 * (10 : UInt64) + pair.2

def optionMapSome : UInt64 :=
  match Option.map (fun value : UInt64 => value + 1) (some (5 : UInt64)) with
  | none => 0
  | some value => value

def optionMapNoneSkipsFunctionTrap : UInt64 :=
  match Option.map (fun _value : UInt64 => (Array.replicate 0 (0 : UInt64)).back!)
      (none : Option UInt64) with
  | none => 7
  | some value => value

def optionMapProduct : UInt64 :=
  match Option.map (fun value : UInt64 => (value, value + 1)) (some (1 : UInt64)) with
  | none => 0
  | some pair => pair.1 * (10 : UInt64) + pair.2

def optionFilterSomeKeep : UInt64 :=
  match Option.filter (fun value : UInt64 => value > 3) (some 5) with
  | some value => value
  | none => 0

def optionFilterSomeDrop : UInt64 :=
  if (Option.filter (fun value : UInt64 => value > 3) (some 2)).isNone then
    1
  else
    0

def optionFilterNoneSkipsPredicateTrap : UInt64 :=
  match Option.filter (fun _value : UInt64 => (Array.replicate 0 (0 : UInt64)).back! == 0)
      (none : Option UInt64) with
  | some value => value
  | none => 7

def optionFilterIgnoresPayloadTrap : UInt64 :=
  if (Option.filter (fun _value : UInt64 => false)
      (some ((Array.replicate 0 (0 : UInt64)).back!))).isNone then
    1
  else
    0

def optionBindSome : UInt64 :=
  match Option.bind (some (5 : UInt64)) (fun value => some (value + 1)) with
  | none => 0
  | some value => value

def optionBindNoneSkipsFunctionTrap : UInt64 :=
  match Option.bind (none : Option UInt64)
      (fun _value => some ((Array.replicate 0 (0 : UInt64)).back!)) with
  | none => 7
  | some value => value

def optionBindFunctionNone : UInt64 :=
  match Option.bind (some (5 : UInt64)) (fun _value => (none : Option UInt64)) with
  | none => 9
  | some value => value

def optionBindProduct : UInt64 :=
  match Option.bind (some (1 : UInt64)) (fun value => some (value, value + 1)) with
  | none => 0
  | some pair => pair.1 * (10 : UInt64) + pair.2

def natComparisons (x : Nat) : UInt64 :=
  if x < 3 then
    10
  else if x <= 5 then
    20
  else
    30

def u64Comparisons (x : UInt64) : UInt64 :=
  if x < 3 then
    10
  else if x <= 5 then
    20
  else
    30

def greaterComparisons (x : UInt64) : UInt64 :=
  if x > 5 then
    30
  else if x >= 3 then
    20
  else
    10

def bneScalars (x : UInt64) : UInt64 :=
  if x != (3 : UInt64) then 1 else 2

def bneAsBool (x : Nat) : Bool :=
  x != 3

def bneBool : UInt64 :=
  if true != false then 1 else 0

def boolXorValues (left right : Bool) : Bool :=
  Bool.xor left right

def boolMatchScalar (flag : Bool) : UInt64 :=
  match flag with
  | false => 10
  | true => 20

def boolMatchTrueFirstScalar (flag : Bool) : UInt64 :=
  match flag with
  | true => 20
  | false => 10

def boolMatchTrueFirstSkipsFalseTrap : UInt64 :=
  match true with
  | true => 7
  | false => (Array.replicate 0 (0 : UInt64)).back!

def boolMatchSkipsTrap : UInt64 :=
  match false with
  | false => 7
  | true => (Array.replicate 1 (0 : UInt64))[5]!

def boolMatchCondition (flag : Bool) : UInt64 :=
  if (
    match flag with
    | false => true
    | true => false
  )
  then
    1
  else
    2

def boolMatchProduct (flag : Bool) : UInt64 :=
  let pair :=
    match flag with
    | false => ((1 : UInt64), (2 : UInt64))
    | true => ((3 : UInt64), (4 : UInt64))
  pair.1 * (10 : UInt64) + pair.2

def decideNatLt (x : Nat) : UInt64 :=
  if decide (x < 3) then 1 else 2

def decideUInt64Ge (x : UInt64) : Bool :=
  decide (x >= 3)

def propEqNat (x : Nat) : UInt64 :=
  if x = 3 then 1 else 2

def decideEqUInt64 (x : UInt64) : Bool :=
  decide (x = 3)

def propEqBoolSkipsTrap : UInt64 :=
  if (true || ((Array.replicate 1 (0 : UInt64))[5]! == 0)) = true then
    1
  else
    0

def propAndNat (x : Nat) : UInt64 :=
  if x > 1 ∧ x < 5 then 1 else 2

def propOrNat (x : Nat) : UInt64 :=
  if x < 2 ∨ x > 5 then 1 else 2

def propNotNat (x : Nat) : UInt64 :=
  if ¬ x < 3 then 1 else 2

def propOrSkipsTrap : UInt64 :=
  if True ∨ ((Array.replicate 1 (0 : UInt64))[5]! = 0) then 1 else 0

def propAndSkipsTrap : UInt64 :=
  if False ∧ ((Array.replicate 1 (0 : UInt64))[5]! = 0) then 1 else 0

def dependentIfNat (x : Nat) : UInt64 :=
  if _h : x < 3 then 1 else 2

def dependentIfSkipsElseTrap : UInt64 :=
  if _h : (1 : Nat) < 3 then
    7
  else
    (Array.replicate 0 (0 : UInt64)).back!

def dependentIfSkipsThenTrap : UInt64 :=
  if _h : (3 : Nat) < 1 then
    (Array.replicate 0 (0 : UInt64)).back!
  else
    8

def dependentIfProduct (x : Nat) : UInt64 :=
  let pair :=
    if _h : x < 3 then
      ((1 : UInt64), (2 : UInt64))
    else
      ((3 : UInt64), (4 : UInt64))
  pair.1 * (10 : UInt64) + pair.2

def natMatchZero (x : Nat) : UInt64 :=
  match x with
  | 0 => 10
  | _ + 1 => 20

def natMatchSuccFirst (x : Nat) : UInt64 :=
  match x with
  | n + 1 => UInt64.ofNat n + 30
  | 0 => 10

def natMatchZeroSkipsSuccTrap : UInt64 :=
  match 0 with
  | 0 => 7
  | _ + 1 => (Array.replicate 0 (0 : UInt64)).back!

def natMatchSuccSkipsZeroTrap : UInt64 :=
  match 2 with
  | 0 => (Array.replicate 0 (0 : UInt64)).back!
  | n + 1 => UInt64.ofNat n

def natMatchBoolCondition (x : Nat) : UInt64 :=
  if (match x with | 0 => true | _ + 1 => false) then 1 else 2

def natMatchProduct (x : Nat) : UInt64 :=
  let pair :=
    match x with
    | 0 => ((1 : UInt64), (2 : UInt64))
    | n + 1 => (UInt64.ofNat n, (9 : UInt64))
  pair.1 * (10 : UInt64) + pair.2

def natMinMax (x y : Nat) : Nat :=
  min x y * 10 + max x y

def u64MinMax (x y : UInt64) : UInt64 :=
  min x y * (10 : UInt64) + max x y

def u8MinMax : Nat :=
  (min (250 : UInt8) (3 : UInt8)).toNat * 10 +
    (max (250 : UInt8) (3 : UInt8)).toNat

def rejectProductReturn : UInt64 × UInt64 :=
  let pair := ((1 : UInt64), (2 : UInt64))
  pair

def rejectProductParam (pair : UInt64 × UInt64) : UInt64 :=
  pair.1

def rejectOptionReturn : Option UInt64 :=
  some 1

def rejectOptionParam (value : Option UInt64) : UInt64 :=
  match value with
  | none => 0
  | some item => item

def rejectExceptReturn : Except UInt64 UInt64 :=
  Except.ok 1

def rejectExceptParam (value : Except UInt64 UInt64) : UInt64 :=
  match value with
  | Except.error code => code
  | Except.ok item => item

def rejectUnitReturn : Unit :=
  ()

def rejectUnitParam (_value : Unit) : UInt64 :=
  1

def rejectByteArrayReturn (input : ByteArray) : ByteArray :=
  input

def rejectUInt8Param (b : UInt8) : Bool :=
  b == (0 : UInt8)

def rejectUInt8Return : UInt8 :=
  42

def rejectUInt32Param (x : UInt32) : Nat :=
  x.toNat

def rejectUInt32Return : UInt32 :=
  42

def alloc : UInt64 :=
  1

def rejectHugeNatLiteral : Nat :=
  18446744073709551616

def rejectHigherOrder (f : UInt64 → UInt64) : UInt64 :=
  f 1

def rejectIO : IO UInt64 :=
  pure 1

end LeanExe.Examples.Correctness
