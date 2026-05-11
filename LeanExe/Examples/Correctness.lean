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

def optionGetBangNoneTrap : UInt64 :=
  (none : Option UInt64).get!

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

def uint64ToNatValue (x : UInt64) : Nat :=
  UInt64.toNat (x + 1)

def uint64ToNatMethodMax : Nat :=
  (18446744073709551615 : UInt64).toNat

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

structure Point where
  x : UInt64
  y : UInt64

structure TaggedPoint where
  point : Point
  tag : UInt64

structure ArrayBox where
  values : Array UInt64
  count : UInt64

structure PointArrayBox where
  values : Array Point
  count : UInt64

structure CheckedPoint where
  value : UInt64
  ok : value = value

def structureProjection : UInt64 :=
  let point : Point := { x := (Array.replicate 0 (0 : UInt64)).back!, y := 7 }
  point.y

def structureUpdateProjection : UInt64 :=
  let point : Point := { x := 1, y := 2 }
  let updated := { point with y := 9 }
  updated.x * (10 : UInt64) + updated.y

def makePointHelper (x : UInt64) : Point :=
  { x := x + 1, y := x + 2 }

def structureHelperResult : UInt64 :=
  let point := makePointHelper 4
  point.x * (10 : UInt64) + point.y

def structureReturn (x : UInt64) : Point :=
  { x := x + 1, y := x + 2 }

def structureBranchReturn (flag : UInt64) : Point :=
  if flag == 0 then
    { x := 1, y := 2 }
  else
    { x := 3, y := 4 }

def nestedStructureReturn : TaggedPoint :=
  { point := { x := 1, y := 2 }, tag := 3 }

def structureArrayReturn : ArrayBox :=
  { values := #[4, 5], count := 2 }

def structurePointArrayReturn : PointArrayBox :=
  { values := #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point)], count := 2 }

def structureMatchDestructure : UInt64 :=
  match ({ x := 1, y := 2 } : Point) with
  | { x, y } => x * (10 : UInt64) + y

def structureMatchUsesFirstOnly : UInt64 :=
  match ({ x := 7, y := (Array.replicate 0 (0 : UInt64)).back! } : Point) with
  | { x, y := _ } => x

def structureMatchCondition : UInt64 :=
  if (
    match ({ x := 2, y := 5 } : Point) with
    | { x, y } => x < y
  )
  then
    1
  else
    0

def proofStructureProjection : UInt64 :=
  let point : CheckedPoint := { value := 9, ok := rfl }
  point.value + 1

def proofStructureReturn : CheckedPoint :=
  { value := 9, ok := rfl }

def proofStructureMatch : UInt64 :=
  match ({ value := 8, ok := rfl } : CheckedPoint) with
  | { value, ok := _ } => value

def structureParam (point : Point) : UInt64 :=
  point.x * 10 + point.y

def proofStructureParam (point : CheckedPoint) : UInt64 :=
  point.value + 1

inductive Status where
  | ok : UInt64 -> Status
  | error : UInt64 -> Status

inductive Mode where
  | idle : Mode
  | busy : Mode
  | done : Mode

inductive CheckedStatus where
  | checked : (value : UInt64) -> value = value -> CheckedStatus
  | failed : UInt64 -> CheckedStatus

def statusOkMatch : UInt64 :=
  match Status.ok 8 with
  | .ok value => value
  | .error code => code + 100

def statusErrorMatch : UInt64 :=
  match Status.error 9 with
  | .ok value => value + 100
  | .error code => code

def statusSourceOrderIndependentMatch : UInt64 :=
  match Status.error 11 with
  | .error code => code
  | .ok value => value + 100

def statusSkipsUnusedPayloadTrap : UInt64 :=
  match Status.ok ((Array.replicate 0 (0 : UInt64)).back!) with
  | .ok _ => 7
  | .error _ => 8

def statusMatchCondition : UInt64 :=
  if (
    match Status.ok 2 with
    | .ok value => value == 2
    | .error _ => false
  )
  then
    1
  else
    0

def makeStatusHelper (x : UInt64) : Status :=
  Status.ok (x + 1)

def statusHelperResult : UInt64 :=
  match makeStatusHelper 4 with
  | .ok value => value
  | .error code => code

def statusBranchReturn (flag : UInt64) : Status :=
  if flag == 0 then
    Status.ok 5
  else
    Status.error 9

def modeMatch : UInt64 :=
  match Mode.busy with
  | .idle => 1
  | .busy => 2
  | .done => 3

def modeReturn (flag : UInt64) : Mode :=
  if flag == 0 then
    Mode.idle
  else
    Mode.done

def checkedStatusMatch : UInt64 :=
  match CheckedStatus.checked 8 rfl with
  | .checked value _ => value
  | .failed code => code

def checkedStatusReturn : CheckedStatus :=
  CheckedStatus.checked 9 rfl

def statusParam (status : Status) : UInt64 :=
  match status with
  | .ok value => value + 10
  | .error code => code + 20

def statusLeftScore (status : Status) : UInt64 :=
  match status with
  | .ok value => value
  | .error code => code + 100

def statusRightScore (status : Status) : UInt64 :=
  match status with
  | .ok value => value + 100
  | .error code => code

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

def idRunLet : UInt64 := Id.run do
  let x := (1 : UInt64)
  return x + 1

def idRunSkipsUnusedLetTrap : UInt64 := Id.run do
  let _x := (Array.replicate 0 (0 : UInt64)).back!
  return 7

def idRunCondition : UInt64 :=
  if Id.run do return true then 1 else 0

def idRunBind : UInt64 := Id.run do
  let x ← pure (1 : UInt64)
  return x + 1

def idRunBindSkipsUnusedTrap : UInt64 := Id.run do
  let _x ← pure ((Array.replicate 0 (0 : UInt64)).back!)
  return 7

def idRunBindProduct : UInt64 := Id.run do
  let pair ← pure (((1 : UInt64), (2 : UInt64)) : UInt64 × UInt64)
  return pair.1 * (10 : UInt64) + pair.2

def idRunBindOption : UInt64 := Id.run do
  let value ← pure (some (5 : UInt64))
  return value.getD 0

def idRunBindExcept : UInt64 := Id.run do
  let value ← pure (Except.ok (5 : UInt64) : Except UInt64 UInt64)
  return match value with
  | Except.error code => code
  | Except.ok item => item + 1

def idRunMut : UInt64 := Id.run do
  let mut x := (1 : UInt64)
  x := x + 1
  return x

def idFunctionUInt64 (x : UInt64) : UInt64 :=
  id (x + 1)

def idFunctionProductSecond : UInt64 :=
  (id ((Array.replicate 0 (0 : UInt64)).back!, (7 : UInt64))).2

def arrayUpdateRead : UInt64 :=
  let a := Array.replicate 2 (0 : UInt64)
  let b := a.set! 0 1
  let c := b.set! 1 (b[0]! + a[0]!)
  c[0]! * (100 : UInt64) + c[1]! * (10 : UInt64) + a[0]!

def arraySizeAfterSet : Nat :=
  let a := Array.replicate 3 (0 : UInt64)
  let b := a.set! 1 9
  b.size

def arrayProofSetRead : UInt64 :=
  let b := (#[1, 2] : Array UInt64).set 1 (9 : UInt64)
  b[0]! * (10 : UInt64) + b[1]!

def arraySetIfInBoundsRead : UInt64 :=
  let b := (#[1, 2] : Array UInt64).setIfInBounds 1 (9 : UInt64)
  b[0]! * (10 : UInt64) + b[1]!

def arraySetIfInBoundsSkipsValueTrap : UInt64 :=
  let a := (#[7] : Array UInt64)
  let b := a.setIfInBounds 5 ((Array.replicate 0 (0 : UInt64)).back!)
  b[0]!

def arrayModifyInBounds : UInt64 :=
  let a := ((Array.replicate 2 (0 : UInt64)).set! 0 4).set! 1 7
  let b := a.modify 1 (fun value => value + 3)
  b[0]! * (100 : UInt64) + b[1]! * (10 : UInt64) + a[1]!

def arrayModifyOutOfBoundsSkipsFunctionTrap : UInt64 :=
  let a := (Array.replicate 1 (7 : UInt64))
  let b := a.modify 5 (fun _value => (Array.replicate 0 (0 : UInt64)).back!)
  b[0]!

def arrayInsertIdxIfInBoundsMiddle : UInt64 :=
  let a := ((Array.replicate 2 (0 : UInt64)).set! 0 1).set! 1 3
  let b := a.insertIdxIfInBounds 1 (2 : UInt64)
  if a.size == 2 && b.size == 3 then
    b[0]! * (1000 : UInt64) + b[1]! * (100 : UInt64) + b[2]! * (10 : UInt64) + a[1]!
  else
    0

def arrayInsertIdxIfInBoundsEnd : UInt64 :=
  let a := ((Array.replicate 2 (0 : UInt64)).set! 0 4).set! 1 5
  let b := a.insertIdxIfInBounds 2 (9 : UInt64)
  if a.size == 2 && b.size == 3 then
    b[0]! * (100 : UInt64) + b[1]! * (10 : UInt64) + b[2]!
  else
    0

def arrayInsertIdxIfInBoundsSkipsValueTrap : UInt64 :=
  let a := Array.replicate 1 (7 : UInt64)
  let b := a.insertIdxIfInBounds 5 ((Array.replicate 0 (0 : UInt64)).back!)
  b[0]!

def arrayEraseIdxIfInBoundsMiddle : UInt64 :=
  let a := (((Array.replicate 3 (0 : UInt64)).set! 0 1).set! 1 2).set! 2 3
  let b := a.eraseIdxIfInBounds 1
  if a.size == 3 && b.size == 2 then
    b[0]! * (100 : UInt64) + b[1]! * (10 : UInt64) + a[1]!
  else
    0

def arrayEraseIdxIfInBoundsLast : UInt64 :=
  let a := (((Array.replicate 3 (0 : UInt64)).set! 0 4).set! 1 5).set! 2 6
  let b := a.eraseIdxIfInBounds 2
  if a.size == 3 && b.size == 2 then
    b[0]! * (10 : UInt64) + b[1]!
  else
    0

def arrayEraseIdxIfInBoundsOutOfBounds : UInt64 :=
  let a := ((Array.replicate 2 (0 : UInt64)).set! 0 7).set! 1 8
  let b := a.eraseIdxIfInBounds 5
  if b.size == 2 then
    b[0]! * (10 : UInt64) + b[1]!
  else
    0

def arraySwapIfInBoundsEnds : UInt64 :=
  let a :=
    ((((Array.replicate 4 (0 : UInt64)).set! 0 1).set! 1 2).set! 2 3).set! 3 4
  let b := a.swapIfInBounds 0 3
  if a.size == 4 && b.size == 4 then
    b[0]! * (1000 : UInt64) + b[1]! * (100 : UInt64) +
      b[2]! * (10 : UInt64) + b[3]!
  else
    0

def arraySwapIfInBoundsSameIndex : UInt64 :=
  let a := ((Array.replicate 2 (0 : UInt64)).set! 0 5).set! 1 6
  let b := a.swapIfInBounds 1 1
  if b.size == 2 then
    b[0]! * (10 : UInt64) + b[1]!
  else
    0

def arraySwapIfInBoundsOutOfBounds : UInt64 :=
  let a := (((Array.replicate 3 (0 : UInt64)).set! 0 7).set! 1 8).set! 2 9
  let b := a.swapIfInBounds 0 3
  if b.size == 3 then
    b[0]! * (100 : UInt64) + b[1]! * (10 : UInt64) + b[2]!
  else
    0

def arrayReverseRead : UInt64 :=
  let a := (((Array.replicate 3 (0 : UInt64)).set! 0 1).set! 1 2).set! 2 3
  let b := a.reverse
  if a.size == 3 && b.size == 3 then
    b[0]! * (100 : UInt64) + b[1]! * (10 : UInt64) + b[2]!
  else
    0

def arrayReverseSmall : UInt64 :=
  let empty := Array.replicate 0 (0 : UInt64)
  let single := Array.replicate 1 (7 : UInt64)
  if empty.reverse.isEmpty && single.reverse.size == 1 then
    single.reverse[0]!
  else
    0

def arrayProofInsertIdxRead : UInt64 :=
  let b := (#[1, 3] : Array UInt64).insertIdx 1 (2 : UInt64)
  if b.size == 3 then
    b[0]! * (100 : UInt64) + b[1]! * (10 : UInt64) + b[2]!
  else
    0

def arrayInsertIdxBangRead : UInt64 :=
  let b := (#[1, 3] : Array UInt64).insertIdx! 1 (2 : UInt64)
  if b.size == 3 then
    b[0]! * (100 : UInt64) + b[1]! * (10 : UInt64) + b[2]!
  else
    0

def arrayInsertIdxBangTrap : UInt64 :=
  let b := (#[1] : Array UInt64).insertIdx! 2 (9 : UInt64)
  b[0]!

def arrayProofEraseIdxRead : UInt64 :=
  let b := (#[1, 2, 3] : Array UInt64).eraseIdx 1
  if b.size == 2 then
    b[0]! * (10 : UInt64) + b[1]!
  else
    0

def arrayEraseIdxBangRead : UInt64 :=
  let b := (#[1, 2, 3] : Array UInt64).eraseIdx! 1
  if b.size == 2 then
    b[0]! * (10 : UInt64) + b[1]!
  else
    0

def arrayEraseIdxBangTrap : UInt64 :=
  let b := (#[1] : Array UInt64).eraseIdx! 5
  b[0]!

def arrayProofSwapRead : UInt64 :=
  let b := (#[1, 2, 3] : Array UInt64).swap 0 2
  if b.size == 3 then
    b[0]! * (100 : UInt64) + b[1]! * (10 : UInt64) + b[2]!
  else
    0

def arraySwapAtRead : UInt64 :=
  let pair := (#[1, 2] : Array UInt64).swapAt 1 (9 : UInt64)
  pair.1 * (100 : UInt64) + pair.2[1]!

def arraySwapAtFirstSkipsValueTrap : UInt64 :=
  ((#[1, 2] : Array UInt64).swapAt 1 ((Array.replicate 0 (0 : UInt64)).back!)).1

def arraySwapAtLetFirstSkipsValueTrap : UInt64 :=
  let pair := (#[1, 2] : Array UInt64).swapAt 1 ((Array.replicate 0 (0 : UInt64)).back!)
  pair.1

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

def arrayAppendNotationRead : UInt64 :=
  let left := ((Array.replicate 2 (0 : UInt64)).set! 0 1).set! 1 2
  let right := ((Array.replicate 2 (0 : UInt64)).set! 0 3).set! 1 4
  let both := left ++ right
  if both.size == 4 then
    both[0]! * (1000 : UInt64) + both[1]! * (100 : UInt64) +
      both[2]! * (10 : UInt64) + both[3]!
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

def arrayMapRead : UInt64 :=
  let a := (#[1, 2, 3] : Array UInt64).map (fun x => x * (2 : UInt64))
  a[0]! * (100 : UInt64) + a[1]! * (10 : UInt64) + a[2]!

def arrayMapAliasRead : UInt64 :=
  let a := (#[1, 2] : Array UInt64)
  let b := a.map (fun x => x + (10 : UInt64))
  a[0]! * (100 : UInt64) + b[0]!

def arrayMapEmptySkipsFunctionTrap : Nat :=
  ((#[] : Array UInt64).map (fun _ => (Array.replicate 0 (0 : UInt64)).back!)).size

def arrayUInt8Read : Nat :=
  let a : Array UInt8 := #[(1 : UInt8), (300 : UInt8)]
  a[0]!.toNat * 1000 + a[1]!.toNat

def arrayUInt8SetRead : Nat :=
  let a : Array UInt8 := #[(1 : UInt8)]
  let b := a.set! 0 (300 : UInt8)
  b[0]!.toNat

def arrayUInt8GetQuestion : Nat :=
  match (#[(5 : UInt8)] : Array UInt8)[0]? with
  | none => 99
  | some value => value.toNat

def arrayUInt32MapRead : Nat :=
  let a : Array UInt32 := #[(4294967295 : UInt32), (2 : UInt32)]
  let b := a.map (fun value => value + 1)
  b[0]!.toNat + b[1]!.toNat

def arrayBoolRead : UInt64 :=
  let a : Array Bool := #[true, false]
  if a[0]! && !a[1]! then
    1
  else
    0

def arrayNatRead : Nat :=
  let a : Array Nat := (#[1, 2] : Array Nat).push 3
  a[0]! * 100 + a[2]!

def arrayStructureLiteralRead : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point)]
  match a[0]? with
  | none => 0
  | some first =>
      match a[1]? with
      | none => 0
      | some second =>
          first.x * (1000 : UInt64) + first.y * (100 : UInt64) +
            second.x * (10 : UInt64) + second.y

def arrayStructureSetRead : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point)]
  let b := a.set! 0 ({ x := 9, y := 8 } : Point)
  match b[0]? with
  | some point => point.x * (10 : UInt64) + point.y
  | none => 0

def arrayStructurePushRead : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point)]
  let b := a.push ({ x := 3, y := 4 } : Point)
  match b[1]? with
  | some point => point.x * (10 : UInt64) + point.y
  | none => 0

def arrayStructurePopRead : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point)]
  let b := a.pop
  match b[0]? with
  | some point => point.x * (10 : UInt64) + point.y
  | none => 0

def arrayStructureAppendRead : UInt64 :=
  let left : Array Point := #[({ x := 1, y := 2 } : Point)]
  let right : Array Point := #[({ x := 3, y := 4 } : Point)]
  let both := left.append right
  match both[0]? with
  | none => 0
  | some first =>
      match both[1]? with
      | none => 0
      | some second =>
          first.x * (1000 : UInt64) + first.y * (100 : UInt64) +
            second.x * (10 : UInt64) + second.y

def arrayStructureExtractRead : UInt64 :=
  let a : Array Point :=
    #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point), ({ x := 5, y := 6 } : Point)]
  let b := a.extract 1 3
  match b[0]? with
  | none => 0
  | some first =>
      match b[1]? with
      | none => 0
      | some second =>
          first.x * (1000 : UInt64) + first.y * (100 : UInt64) +
            second.x * (10 : UInt64) + second.y

def arrayStructureInsertRead : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point), ({ x := 5, y := 6 } : Point)]
  let b := a.insertIdxIfInBounds 1 ({ x := 3, y := 4 } : Point)
  if a.size == 2 && b.size == 3 then
    match b[0]? with
    | none => 0
    | some first =>
        match b[1]? with
        | none => 0
        | some second =>
            match b[2]? with
            | none => 0
            | some third =>
                first.x * (100000 : UInt64) + first.y * (10000 : UInt64) +
                  second.x * (1000 : UInt64) + second.y * (100 : UInt64) +
                  third.x * (10 : UInt64) + third.y
  else
    0

def arrayStructureInsertSkipsValueTrap : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point)]
  let b :=
    a.insertIdxIfInBounds 5
      ({ x := (Array.replicate 0 (0 : UInt64)).back!, y := 9 } : Point)
  match b[0]? with
  | none => 0
  | some point => point.x * (10 : UInt64) + point.y

def arrayStructureEraseRead : UInt64 :=
  let a : Array Point :=
    #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point), ({ x := 5, y := 6 } : Point)]
  let b := a.eraseIdxIfInBounds 1
  if a.size == 3 && b.size == 2 then
    match b[0]? with
    | none => 0
    | some first =>
        match b[1]? with
        | none => 0
        | some second =>
            first.x * (1000 : UInt64) + first.y * (100 : UInt64) +
              second.x * (10 : UInt64) + second.y
  else
    0

def arrayStructureSwapRead : UInt64 :=
  let a : Array Point :=
    #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point), ({ x := 5, y := 6 } : Point)]
  let b := a.swapIfInBounds 0 2
  if b.size == 3 then
    match b[0]? with
    | none => 0
    | some first =>
        match b[1]? with
        | none => 0
        | some second =>
            match b[2]? with
            | none => 0
            | some third =>
                first.x * (100000 : UInt64) + first.y * (10000 : UInt64) +
                  second.x * (1000 : UInt64) + second.y * (100 : UInt64) +
                  third.x * (10 : UInt64) + third.y
  else
    0

def arrayStructureReverseRead : UInt64 :=
  let a : Array Point :=
    #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point), ({ x := 5, y := 6 } : Point)]
  let b := a.reverse
  if b.size == 3 then
    match b[0]? with
    | none => 0
    | some first =>
        match b[1]? with
        | none => 0
        | some second =>
            match b[2]? with
            | none => 0
            | some third =>
                first.x * (100000 : UInt64) + first.y * (10000 : UInt64) +
                  second.x * (1000 : UInt64) + second.y * (100 : UInt64) +
                  third.x * (10 : UInt64) + third.y
  else
    0

def arrayStructureGetDRead : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point)]
  let point := a.getD 5 ({ x := 7, y := 8 } : Point)
  point.x * (10 : UInt64) + point.y

def arrayStructureGetDSkipsDefaultTrap : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point)]
  let point := a.getD 0 ({ x := (Array.replicate 0 (0 : UInt64)).back!, y := 9 } : Point)
  point.x * (10 : UInt64) + point.y

def arrayStructureModifyRead : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point)]
  let b := a.modify 1 (fun point => ({ x := point.x + 1, y := point.y + 1 } : Point))
  match b[1]? with
  | none => 0
  | some point => point.x * (10 : UInt64) + point.y

def arrayStructureModifyOutOfBoundsSkipsFunctionTrap : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point)]
  let b :=
    a.modify 5
      (fun _point => ({ x := (Array.replicate 0 (0 : UInt64)).back!, y := 9 } : Point))
  match b[0]? with
  | none => 0
  | some point => point.x * (10 : UInt64) + point.y

def arrayStructureReplicateRead : UInt64 :=
  let a := Array.replicate 3 ({ x := 1, y := 2 } : Point)
  if a.size == 3 then
    match a[0]? with
    | none => 0
    | some first =>
        match a[2]? with
        | none => 0
        | some last =>
            first.x * (1000 : UInt64) + first.y * (100 : UInt64) +
              last.x * (10 : UInt64) + last.y
  else
    0

def arrayStructureSafeGet : UInt64 :=
  match (#[({ x := 4, y := 5 } : Point)] : Array Point)[0]? with
  | none => 99
  | some point => point.x * (10 : UInt64) + point.y

def arrayStatusLiteralMatch : UInt64 :=
  let a : Array Status := #[Status.ok 5, Status.error 7]
  let left := Option.elim a[0]? 0 (fun status => statusLeftScore status)
  let right := Option.elim a[1]? 0 (fun status => statusRightScore status)
  left * (10 : UInt64) + right

def arrayStatusSwapMatch : UInt64 :=
  let a : Array Status := #[Status.ok 5, Status.error 7]
  let b := a.swapIfInBounds 0 1
  let left := Option.elim b[0]? 0 (fun status => statusLeftScore status)
  let right := Option.elim b[1]? 0 (fun status => statusRightScore status)
  left * (10 : UInt64) + right

def arrayStatusReverseMatch : UInt64 :=
  let a : Array Status := #[Status.ok 5, Status.error 7]
  let b := a.reverse
  let left := Option.elim b[0]? 0 (fun status => statusLeftScore status)
  let right := Option.elim b[1]? 0 (fun status => statusRightScore status)
  left * (10 : UInt64) + right

def arrayStatusModifyMatch : UInt64 :=
  let a : Array Status := #[Status.ok 5]
  let b :=
    a.modify 0 (fun status =>
      match status with
      | Status.ok value => Status.error (value + 2)
      | Status.error code => Status.ok code)
  Option.elim b[0]? 0 (fun status => statusLeftScore status)

def arrayStatusReplicateMatch : UInt64 :=
  let a := Array.replicate 2 (Status.error 7)
  let left := Option.elim a[0]? 0 (fun status => statusLeftScore status)
  let right := Option.elim a[1]? 0 (fun status => statusRightScore status)
  left * (10 : UInt64) + right

def arrayOptionLiteralMatch : UInt64 :=
  let a : Array (Option UInt64) := #[some 5, none]
  let left :=
    match a[0]! with
    | some value => value
    | none => 99
  let right :=
    match a[1]! with
    | some value => value + 100
    | none => 7
  left * (10 : UInt64) + right

def arrayLiteralRead : UInt64 :=
  let a : Array UInt64 := #[10, 20, 30]
  if a.size == 3 then
    a[0]! * (100 : UInt64) + a[2]!
  else
    0

def arrayGetProof : UInt64 :=
  let a : Array UInt64 := #[10, 20, 30]
  a[0]

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

def arrayProofBackRead : UInt64 :=
  (#[4, 9] : Array UInt64).back

def arrayBackQuestionRead : UInt64 :=
  match ((Array.replicate 2 (4 : UInt64)).push 9).back? with
  | some value => value
  | none => 0

def arrayBackQuestionEmpty : UInt64 :=
  match (Array.replicate 0 (4 : UInt64)).back? with
  | some value => value
  | none => 7

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

def exceptMapError : UInt64 :=
  match Except.mapError (fun code : UInt64 => code + 1)
      (Except.error (5 : UInt64) : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok value => value

def exceptMapErrorOkSkipsFunctionTrap : UInt64 :=
  match Except.mapError (fun _code : UInt64 => (Array.replicate 0 (0 : UInt64)).back!)
      (Except.ok (7 : UInt64) : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok value => value

def exceptMapErrorProduct : UInt64 :=
  match Except.mapError (fun code : UInt64 => (code, code + 1))
      (Except.error (1 : UInt64) : Except UInt64 UInt64) with
  | Except.error pair => pair.1 * (10 : UInt64) + pair.2
  | Except.ok value => value

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

def exceptIsOkOkSkipsPayloadTrap : UInt64 :=
  if Except.isOk
      (Except.ok ((Array.replicate 0 (0 : UInt64)).back!) : Except UInt64 UInt64) then
    1
  else
    0

def exceptIsOkError : UInt64 :=
  if Except.isOk (Except.error (7 : UInt64) : Except UInt64 UInt64) then
    0
  else
    1

def exceptIsOkAsBool : Bool :=
  Except.isOk (Except.ok (5 : UInt64) : Except UInt64 UInt64)

def exceptOrElseError : UInt64 :=
  match ((Except.error (7 : UInt64) : Except UInt64 UInt64) <|> Except.ok 5) with
  | Except.error code => code
  | Except.ok value => value

def exceptOrElseOkSkipsFallbackTrap : UInt64 :=
  match ((Except.ok (5 : UInt64) : Except UInt64 UInt64) <|>
      Except.ok ((Array.replicate 0 (0 : UInt64)).back!)) with
  | Except.error code => code
  | Except.ok value => value

def exceptOrElseFallbackError : UInt64 :=
  match ((Except.error (7 : UInt64) : Except UInt64 UInt64) <|> Except.error 9) with
  | Except.error code => code
  | Except.ok value => value

def optionGetDNone : UInt64 :=
  (none : Option UInt64).getD 7

def optionGetDSomeSkipsDefaultTrap : UInt64 :=
  (some (5 : UInt64)).getD ((Array.replicate 0 (0 : UInt64)).back!)

def optionGetDProduct : UInt64 :=
  let pair := (some ((1 : UInt64), (2 : UInt64))).getD ((3 : UInt64), (4 : UInt64))
  pair.1 * (10 : UInt64) + pair.2

def optionGetBangSome : UInt64 :=
  (some (5 : UInt64)).get! + 1

def optionGetBangProduct : UInt64 :=
  let pair := (some ((1 : UInt64), (2 : UInt64))).get!
  pair.1 * (10 : UInt64) + pair.2

def optionGetBangCondition : UInt64 :=
  if (some true).get! then 1 else 0

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

def optionAnySome : UInt64 :=
  if (some (5 : UInt64)).any (fun value => value > 3) then 1 else 0

def optionAnyNoneSkipsPredicateTrap : UInt64 :=
  if (none : Option UInt64).any (fun _value => (Array.replicate 0 (0 : UInt64)).back! == 0) then
    0
  else
    7

def optionAllSomeFalse : UInt64 :=
  if (some (2 : UInt64)).all (fun value => value > 3) then 0 else 7

def optionAllNoneSkipsPredicateTrap : UInt64 :=
  if (none : Option UInt64).all (fun _value => (Array.replicate 0 (0 : UInt64)).back! == 0) then
    7
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

def natBoolComparisons (x : Nat) : UInt64 :=
  if Nat.blt x 3 then
    10
  else if Nat.ble x 5 then
    20
  else
    30

def natBltAsBool (x : Nat) : Bool :=
  Nat.blt x 3

def natBeqAsBool (x : Nat) : Bool :=
  Nat.beq x 3

def natBeqCondition (x : Nat) : UInt64 :=
  if Nat.beq x 3 then 1 else 2

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

def boolToNatValue (flag : Bool) : Nat :=
  flag.toNat + 1

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

def optionReturn (flag : UInt64) : Option UInt64 :=
  if flag == 0 then
    none
  else
    some (flag + 4)

def optionPointReturn (flag : UInt64) : Option Point :=
  if flag == 0 then
    none
  else
    some { x := flag, y := flag + 1 }

def optionParam (value : Option UInt64) : UInt64 :=
  match value with
  | none => 0
  | some item => item

def optionPointParam (value : Option Point) : UInt64 :=
  match value with
  | none => 0
  | some point => point.x + point.y

def exceptReturn (flag : UInt64) : Except UInt64 UInt64 :=
  if flag == 0 then
    Except.error 7
  else
    Except.ok (flag + 4)

def exceptPointReturn (flag : UInt64) : Except UInt64 Point :=
  if flag == 0 then
    Except.error 7
  else
    Except.ok { x := flag, y := flag + 1 }

def exceptParam (value : Except UInt64 UInt64) : UInt64 :=
  match value with
  | Except.error code => code
  | Except.ok item => item

def exceptUnitErrorOk : UInt64 :=
  match (Except.ok (1 : UInt64) : Except Unit UInt64) with
  | Except.error _ => 0
  | Except.ok item => item

def exceptUnitErrorError : UInt64 :=
  match (Except.error () : Except Unit UInt64) with
  | Except.error _ => 7
  | Except.ok item => item

def exceptUnitErrorBind : UInt64 :=
  match Except.bind (Except.ok (4 : UInt64) : Except Unit UInt64)
      (fun value => Except.ok (value + 1)) with
  | Except.error _ => 0
  | Except.ok item => item

def rejectUnitReturn : Unit :=
  ()

def rejectUnitParam (_value : Unit) : UInt64 :=
  1

def rejectByteArrayReturn (input : ByteArray) : ByteArray :=
  input

def rejectNestedArrayReturn : Array (Array UInt64) :=
  #[#[1, 2]]

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

def rejectIdForLoop : UInt64 := Id.run do
  let mut acc := (0 : UInt64)
  for _i in [0:3] do
    acc := acc + 1
  return acc

end LeanExe.Examples.Correctness
