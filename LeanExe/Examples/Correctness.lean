import Init.Data.ByteArray.Extra
import LeanExe.Ascii.Decimal
import LeanExe.Runtime

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

def productEquality : UInt64 :=
  if (((1 : UInt64), (2 : UInt64)) == ((1 : UInt64), (2 : UInt64))) then
    1
  else
    0

def productInequality : UInt64 :=
  if (((1 : UInt64), (2 : UInt64)) != ((1 : UInt64), (3 : UInt64))) then
    1
  else
    0

def productEqualityShortCircuit : UInt64 :=
  if (((1 : UInt64), (Array.replicate 0 (0 : UInt64)).back!) ==
      ((2 : UInt64), (0 : UInt64))) then
    0
  else
    1

structure Point where
  x : UInt64
  y : UInt64

structure EqPoint where
  x : UInt64
  y : UInt64
deriving BEq, DecidableEq

structure EqTaggedPoint where
  point : EqPoint
  tag : UInt64
deriving BEq, DecidableEq

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

structure Box (α : Type) where
  value : α

structure PairBox (α β : Type) where
  left : α
  right : β

structure CheckedBox (α : Type) where
  value : α
  ok : True

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

def structureEquality : UInt64 :=
  if (({ x := 1, y := 2 } : EqPoint) == ({ x := 1, y := 2 } : EqPoint)) then
    1
  else
    0

def structureInequality : UInt64 :=
  if (({ x := 1, y := 2 } : EqPoint) != ({ x := 1, y := 3 } : EqPoint)) then
    1
  else
    0

def nestedStructureEquality : UInt64 :=
  if (({ point := { x := 1, y := 2 }, tag := 3 } : EqTaggedPoint) ==
      ({ point := { x := 1, y := 2 }, tag := 3 } : EqTaggedPoint)) then
    1
  else
    0

def structureEqualityShortCircuit : UInt64 :=
  if (({ x := 1, y := (Array.replicate 0 (0 : UInt64)).back! } : EqPoint) ==
      ({ x := 2, y := 0 } : EqPoint)) then
    0
  else
    1

def structurePropEquality : UInt64 :=
  if ({ x := 3, y := 4 } : EqPoint) = ({ x := 3, y := 4 } : EqPoint) then
    1
  else
    0

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

def structureCallArgMaterialized : UInt64 :=
  structureParam (makePointHelper 7)

def proofStructureParam (point : CheckedPoint) : UInt64 :=
  point.value + 1

def paramBoxProjection : UInt64 :=
  let box : Box UInt64 := { value := 41 }
  box.value + 1

def paramBoxMatch : UInt64 :=
  match ({ value := 7 } : Box UInt64) with
  | { value } => value + 1

def paramPairBoxParam (box : PairBox UInt64 Bool) : UInt64 :=
  if box.right then box.left else 0

def paramBoxReturn (x : UInt64) : Box UInt64 :=
  { value := x + 1 }

def paramCheckedBoxProjection : UInt64 :=
  let box : CheckedBox UInt64 := { value := 8, ok := True.intro }
  box.value + 1

def paramBoxArrayFold : UInt64 :=
  let boxes : Array (Box UInt64) := #[{ value := 2 }, { value := 3 }]
  boxes.foldl (fun acc box => acc + box.value) 0

def genericBoxValue {α : Type} (box : Box α) : α :=
  box.value

def genericPairLeft {α β : Type} (box : PairBox α β) : α :=
  box.left

def genericPairRight {α β : Type} (box : PairBox α β) : β :=
  box.right

def genericFirstBoxValue {α β : Type} (left : Box α) (_right : Box β) : α :=
  left.value

def genericApplyWithSeed {α : Type} (seed : UInt64) (value : α)
    (f : α -> UInt64) : UInt64 :=
  seed + f value

def genericBoxHelperProjection : UInt64 :=
  genericBoxValue ({ value := 20 } : Box UInt64) + 2

def genericPairBoxHelper : UInt64 :=
  let box : PairBox UInt64 Bool := { left := 9, right := true }
  if genericPairRight box then genericPairLeft box else 0

def genericBoxHelperSkipsUnusedTrap : UInt64 :=
  genericFirstBoxValue
    ({ value := 7 } : Box UInt64)
    ({ value := (Array.replicate 0 (0 : UInt64)).back! } : Box UInt64)

def genericInterleavedLambdaHelper : UInt64 :=
  let bonus := (5 : UInt64)
  genericApplyWithSeed
    10
    ({ value := 7 } : Box UInt64)
    (fun box => box.value + bonus)

structure TypeclassPoint where
  x : UInt64
  y : UInt64

instance : Inhabited TypeclassPoint where
  default := { x := 3, y := 4 }

structure WeirdEq where
  value : UInt64

instance : BEq WeirdEq where
  beq _left _right := false

class TypeclassScore (α : Type) where
  score : α -> UInt64

instance : TypeclassScore UInt64 where
  score value := value + 3

instance : TypeclassScore TypeclassPoint where
  score point := point.x * (10 : UInt64) + point.y

instance [TypeclassScore α] : TypeclassScore (Option α) where
  score
    | none => 5
    | some value => TypeclassScore.score value + 10

def typeclassSame [BEq α] (left right : α) : Bool :=
  left == right

def typeclassSameUInt64 : UInt64 :=
  if typeclassSame (7 : UInt64) 7 then 1 else 0

def typeclassSameCustomBEq : UInt64 :=
  if typeclassSame ({ value := 1 } : WeirdEq) ({ value := 1 } : WeirdEq) then 0 else 1

def typeclassDefaultOr [Inhabited α] (flag : Bool) (value : α) : α :=
  if flag then value else default

def typeclassDefaultUInt64 : UInt64 :=
  typeclassDefaultOr false (7 : UInt64)

def typeclassDefaultPoint : UInt64 :=
  let point := typeclassDefaultOr false ({ x := 9, y := 9 } : TypeclassPoint)
  point.x * (10 : UInt64) + point.y

def typeclassScoreGeneric [TypeclassScore α] (value : α) : UInt64 :=
  TypeclassScore.score value

def typeclassScoreUInt64 : UInt64 :=
  typeclassScoreGeneric (5 : UInt64)

def typeclassScorePoint : UInt64 :=
  typeclassScoreGeneric ({ x := 8, y := 6 } : TypeclassPoint)

def typeclassScoreOptionUInt64 : UInt64 :=
  typeclassScoreGeneric (some (5 : UInt64))

def typeclassScoreArrayTotal [TypeclassScore α] (values : Array α) : UInt64 :=
  values.foldl (fun acc value => acc + TypeclassScore.score value) 0

def typeclassScoreArrayTotalDemo : UInt64 :=
  typeclassScoreArrayTotal (#[some (1 : UInt64), none, some 2] : Array (Option UInt64))

def typeclassScoreArrayAny [TypeclassScore α] (limit : UInt64) (values : Array α) : Bool :=
  values.any (fun value => limit < TypeclassScore.score value)

def typeclassScoreArrayAnyDemo : UInt64 :=
  if typeclassScoreArrayAny 14 (#[some (1 : UInt64), none, some 2] : Array (Option UInt64)) then
    1
  else
    0

def typeclassScoreArrayFind? [TypeclassScore α] (target : UInt64) (values : Array α) : Option α :=
  values.find? (fun value => TypeclassScore.score value == target)

def typeclassScoreArrayFindDemo : UInt64 :=
  match typeclassScoreArrayFind? 15 (#[some (1 : UInt64), none, some 2] : Array (Option UInt64)) with
  | none => 0
  | some value => TypeclassScore.score value

def typeclassScoreListFoldl [TypeclassScore α] (values : List α) : UInt64 :=
  values.foldl (fun acc value => acc + TypeclassScore.score value) 0

def typeclassScoreListFoldlDemo : UInt64 :=
  typeclassScoreListFoldl ([some (1 : UInt64), none, some 2] : List (Option UInt64))

def typeclassScoreListFind? [TypeclassScore α] (target : UInt64) (values : List α) : Option α :=
  values.find? (fun value => TypeclassScore.score value == target)

def typeclassScoreListFindDemo : UInt64 :=
  match typeclassScoreListFind? 15 ([some (1 : UInt64), none, some 2] : List (Option UInt64)) with
  | none => 0
  | some value => TypeclassScore.score value

def rejectTypeclassEntry [TypeclassScore UInt64] (value : UInt64) : UInt64 :=
  TypeclassScore.score value

def rejectTypeclassRuntimeDictionaryParam (inst : TypeclassScore UInt64) (value : UInt64) : UInt64 :=
  TypeclassScore.score (self := inst) value

structure DigitState where
  pos : Nat
  sum : UInt64

structure ByteOutputState where
  count : UInt64
  bytes : ByteArray

structure ByteArrayGroup where
  values : Array ByteArray
  marker : UInt64
deriving BEq

inductive PublicToken where
  | text : ByteArray -> PublicToken
  | number : UInt64 -> PublicToken
deriving BEq

inductive PublicHeapArrayResult where
  | failed : ByteArray -> PublicHeapArrayResult
  | ok : Array ByteArray -> UInt64 -> PublicHeapArrayResult

structure ParserBufferState where
  pos : Nat
  out : ByteArray
  ok : Bool

structure ArrayBuilderState where
  values : Array UInt64
  count : UInt64

structure OwnedCallBox where
  values : Array UInt64
  bytes : ByteArray
  count : UInt64

structure EqByteBox where
  bytes : ByteArray
  count : UInt64
deriving BEq

def isAsciiDigitByte (byte : UInt8) : Bool :=
  (48 : UInt8) <= byte && byte <= (57 : UInt8)

def digitStateCanContinue (input : ByteArray) (state : DigitState) : Bool :=
  if state.pos < input.size then
    isAsciiDigitByte input[state.pos]!
  else
    false

def digitStateStep (input : ByteArray) (state : DigitState) : DigitState :=
  let byte := input[state.pos]!
  { pos := state.pos + 1, sum := state.sum + (byte.toUInt64 - 48) }

def digitStateParseFuel : Nat → ByteArray → DigitState → DigitState
  | 0, _input, state => state
  | fuel + 1, input, state =>
      if digitStateCanContinue input state then
        digitStateParseFuel fuel input (digitStateStep input state)
      else
        state

def digitStateParseValue (input : ByteArray) : UInt64 :=
  let state := digitStateParseFuel (input.size + 1) input { pos := 0, sum := 0 }
  if state.pos == input.size then
    state.sum * 100 + Nat.toUInt64 state.pos
  else
    999

def digitStateParserAllDigitsDemo : UInt64 :=
  digitStateParseValue (ByteArray.mk #[(49 : UInt8), (50 : UInt8), (51 : UInt8)])

def digitStateParserStopsDemo : UInt64 :=
  digitStateParseValue (ByteArray.mk #[(49 : UInt8), (50 : UInt8), (65 : UInt8)])

inductive Status where
  | ok : UInt64 -> Status
  | error : UInt64 -> Status

inductive EqStatus where
  | ok : UInt64 -> EqStatus
  | error : UInt64 -> EqStatus
deriving BEq, DecidableEq

inductive Mode where
  | idle : Mode
  | busy : Mode
  | done : Mode

inductive CheckedStatus where
  | checked : (value : UInt64) -> value = value -> CheckedStatus
  | failed : UInt64 -> CheckedStatus

inductive ParamResult (ε α : Type) where
  | error : ε -> ParamResult ε α
  | ok : α -> ParamResult ε α

inductive CheckedPayload (α : Type) where
  | wrap : (value : α) -> True -> CheckedPayload α

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

def paramResultOkMatch : UInt64 :=
  match (ParamResult.ok ({ value := 5 } : Box UInt64) : ParamResult UInt64 (Box UInt64)) with
  | .error code => code
  | .ok box => box.value + 1

def paramResultErrorMatch : UInt64 :=
  match (ParamResult.error (4 : UInt64) : ParamResult UInt64 (Box UInt64)) with
  | .error code => code + 10
  | .ok box => box.value

def paramResultReturn (flag : UInt64) : ParamResult UInt64 Point :=
  if flag == 0 then
    ParamResult.error 7
  else
    ParamResult.ok { x := flag, y := flag + 1 }

def paramResultParam (value : ParamResult UInt64 Point) : UInt64 :=
  match value with
  | .error code => code
  | .ok point => point.x * 10 + point.y

def checkedPayloadMatch : UInt64 :=
  match (CheckedPayload.wrap (9 : UInt64) True.intro) with
  | .wrap value _ => value + 1

def paramResultArrayFold : UInt64 :=
  let values : Array (ParamResult UInt64 UInt64) :=
    #[ParamResult.ok 5, ParamResult.error 7]
  values.foldl
    (fun acc item =>
      match item with
      | .error code => acc + code * 10
      | .ok value => acc + value)
    0

def genericResultIsOk {ε α : Type} (value : ParamResult ε α) : Bool :=
  match value with
  | .error _ => false
  | .ok _ => true

def genericResultValueOr {ε α : Type} (fallback : α) (value : ParamResult ε α) : α :=
  match value with
  | .error _ => fallback
  | .ok item => item

def genericCheckedPayloadValue {α : Type} (payload : CheckedPayload α) : α :=
  match payload with
  | .wrap value _ => value

def genericResultIsOkDemo : UInt64 :=
  if genericResultIsOk (ParamResult.ok ({ x := 1, y := 2 } : Point) :
      ParamResult UInt64 Point) then
    1
  else
    0

def genericResultValueOrDemo : UInt64 :=
  let point :=
    genericResultValueOr
      ({ x := 9, y := 9 } : Point)
      (ParamResult.ok ({ x := 3, y := 4 } : Point) : ParamResult UInt64 Point)
  point.x * 10 + point.y

def genericCheckedPayloadDemo : UInt64 :=
  genericCheckedPayloadValue (CheckedPayload.wrap (11 : UInt64) True.intro) + 1

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

def inductiveEqualitySameCtor : UInt64 :=
  if (EqStatus.ok 7 == EqStatus.ok 7) then
    1
  else
    0

def inductiveInequalitySameCtor : UInt64 :=
  if (EqStatus.ok 7 != EqStatus.ok 8) then
    1
  else
    0

def inductiveEqualityDifferentCtor : UInt64 :=
  if (EqStatus.ok 7 == EqStatus.error 7) then
    0
  else
    1

def inductiveEqualityDifferentCtorSkipsPayload : UInt64 :=
  if (EqStatus.ok ((Array.replicate 0 (0 : UInt64)).back!) == EqStatus.error 0) then
    0
  else
    1

def inductivePropEquality : UInt64 :=
  if EqStatus.ok 5 = EqStatus.ok 5 then
    1
  else
    0

def optionStructuralEquality : UInt64 :=
  if ((some ({ x := 1, y := 2 } : EqPoint)) == some ({ x := 1, y := 2 } : EqPoint)) &&
      ((none : Option EqPoint) != some ({ x := 0, y := 0 } : EqPoint)) then
    1
  else
    0

def byteArrayEquality : UInt64 :=
  if (ByteArray.mk #[(65 : UInt8), (66 : UInt8)] ==
      ByteArray.mk #[(65 : UInt8), (66 : UInt8)]) then
    1
  else
    0

def byteArrayInequalityValue : UInt64 :=
  if (ByteArray.mk #[(65 : UInt8), (66 : UInt8)] !=
      ByteArray.mk #[(65 : UInt8), (67 : UInt8)]) then
    1
  else
    0

def byteArrayInequalityLength : UInt64 :=
  if (ByteArray.mk #[(65 : UInt8), (66 : UInt8)] !=
      ByteArray.mk #[(65 : UInt8)]) then
    1
  else
    0

def byteArrayFieldStructureEquality : UInt64 :=
  if (({ bytes := ByteArray.mk #[(65 : UInt8)], count := 1 } : EqByteBox) ==
      ({ bytes := ByteArray.mk #[(65 : UInt8)], count := 1 } : EqByteBox)) then
    1
  else
    0

def byteArrayOptionEquality : UInt64 :=
  if ((some (ByteArray.mk #[(65 : UInt8), (66 : UInt8)])) ==
      some (ByteArray.mk #[(65 : UInt8), (66 : UInt8)])) then
    1
  else
    0

def arrayEquality : UInt64 :=
  if ((#[(1 : UInt64), (2 : UInt64)] : Array UInt64) ==
      (#[(1 : UInt64), (2 : UInt64)] : Array UInt64)) then
    1
  else
    0

def arrayInequalityValue : UInt64 :=
  if ((#[(1 : UInt64), (2 : UInt64)] : Array UInt64) !=
      (#[(1 : UInt64), (3 : UInt64)] : Array UInt64)) then
    1
  else
    0

def arrayInequalityLength : UInt64 :=
  if ((#[(1 : UInt64), (2 : UInt64)] : Array UInt64) !=
      (#[(1 : UInt64)] : Array UInt64)) then
    1
  else
    0

def arrayPropEquality : UInt64 :=
  if (#[(1 : UInt64), (2 : UInt64)] : Array UInt64) =
      (#[(1 : UInt64), (2 : UInt64)] : Array UInt64) then
    1
  else
    0

def pointArrayEquality : UInt64 :=
  if ((#[({ x := 1, y := 2 } : EqPoint), ({ x := 3, y := 4 } : EqPoint)] : Array EqPoint) ==
      #[({ x := 1, y := 2 } : EqPoint), ({ x := 3, y := 4 } : EqPoint)]) then
    1
  else
    0

def statusArrayEquality : UInt64 :=
  if ((#[EqStatus.ok 5, EqStatus.error 7] : Array EqStatus) ==
      #[EqStatus.ok 5, EqStatus.error 7]) then
    1
  else
    0

def nestedArrayEquality : UInt64 :=
  if ((#[#[1, 2], #[3]] : Array (Array UInt64)) ==
      (#[#[1, 2], #[3]] : Array (Array UInt64))) then
    1
  else
    0

def byteArrayArrayEquality : UInt64 :=
  if ((#[ByteArray.mk #[(65 : UInt8)], ByteArray.mk #[(66 : UInt8), (67 : UInt8)]] :
        Array ByteArray) ==
      #[ByteArray.mk #[(65 : UInt8)], ByteArray.mk #[(66 : UInt8), (67 : UInt8)]]) then
    1
  else
    0

def byteArrayStructureArrayEquality : UInt64 :=
  if ((#[
          ({ bytes := ByteArray.mk #[(65 : UInt8)], count := 1 } : EqByteBox),
          ({ bytes := ByteArray.mk #[(66 : UInt8), (67 : UInt8)], count := 2 } : EqByteBox)
        ] : Array EqByteBox) ==
      #[
          ({ bytes := ByteArray.mk #[(65 : UInt8)], count := 1 } : EqByteBox),
          ({ bytes := ByteArray.mk #[(66 : UInt8), (67 : UInt8)], count := 2 } : EqByteBox)
        ]) then
    1
  else
    0

inductive U64List where
  | nil : U64List
  | cons : UInt64 → U64List → U64List

inductive EqU64List where
  | nil : EqU64List
  | cons : UInt64 → EqU64List → EqU64List
deriving BEq, DecidableEq

def rejectRecursiveInductiveEquality : UInt64 :=
  if (EqU64List.cons 1 EqU64List.nil == EqU64List.cons 1 EqU64List.nil) then
    1
  else
    0

def u64List123 : U64List :=
  U64List.cons 1 (U64List.cons 2 (U64List.cons 3 U64List.nil))

def u64ListHeadOrZero (xs : U64List) : UInt64 :=
  match xs with
  | .nil => 0
  | .cons head _tail => head

def u64ListHeadDemo : UInt64 :=
  u64ListHeadOrZero u64List123

def u64ListTailHeadDemo : UInt64 :=
  match u64List123 with
  | .nil => 0
  | .cons _head tail => u64ListHeadOrZero tail

def u64ListNilDemo : UInt64 :=
  u64ListHeadOrZero U64List.nil + 7

def u64ListIsCons (xs : U64List) : Bool :=
  match xs with
  | .nil => false
  | .cons _head _tail => true

def u64ListTail (xs : U64List) : U64List :=
  match xs with
  | .nil => xs
  | .cons _head tail => tail

def u64ListAddHead (xs : U64List) (acc : UInt64) : UInt64 :=
  match xs with
  | .nil => acc
  | .cons head _tail => acc + head

def u64ListSumFuel : Nat → U64List → UInt64 → UInt64
  | 0, _xs, acc => acc
  | fuel + 1, xs, acc =>
      if u64ListIsCons xs then
        u64ListSumFuel fuel (u64ListTail xs) (u64ListAddHead xs acc)
      else
        acc

def u64ListSumDemo : UInt64 :=
  u64ListSumFuel 10 u64List123 0

def u64ListSumShortFuel : UInt64 :=
  u64ListSumFuel 2 u64List123 0

def u64ListStructuralSum : U64List → UInt64
  | .nil => 0
  | .cons head tail => head + u64ListStructuralSum tail

def u64ListStructuralSumDemo : UInt64 :=
  u64ListStructuralSum u64List123

def u64ListBranch (flag : UInt64) : UInt64 :=
  let xs :=
    if flag == 0 then
      U64List.nil
    else
      U64List.cons 9 U64List.nil
  u64ListHeadOrZero xs

def u64ListArrayHeadOrZero (xs : Array U64List) (index : Nat) : UInt64 :=
  match xs[index]? with
  | some item => u64ListHeadOrZero item
  | none => 0

def u64ListArrayLiteralHeadSum : UInt64 :=
  let xs : Array U64List := #[U64List.nil, u64List123, U64List.cons 9 U64List.nil]
  u64ListArrayHeadOrZero xs 0 + u64ListArrayHeadOrZero xs 1 + u64ListArrayHeadOrZero xs 2

def u64ListArrayPushSetSum : UInt64 :=
  let xs : Array U64List := #[U64List.nil]
  let pushed := xs.push (U64List.cons 5 U64List.nil)
  let updated := pushed.set! 0 u64List123
  u64ListArrayHeadOrZero updated 0 + u64ListArrayHeadOrZero updated 1

def u64ListArrayMapTailHead : UInt64 :=
  let xs : Array U64List := #[u64List123, U64List.cons 9 U64List.nil]
  let tails := xs.map (fun item => u64ListTail item)
  u64ListArrayHeadOrZero tails 0 + u64ListArrayHeadOrZero tails 1

def u64ListArrayFoldHeads : UInt64 :=
  let xs : Array U64List := #[u64List123, U64List.cons 9 U64List.nil]
  xs.foldl (fun acc item => acc + u64ListHeadOrZero item) 0

def u64ListArrayRuntimeReleaseFrees : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let retainBefore := LeanExe.Runtime.retainCount
  let after :=
    LeanExe.Runtime.release
      (Array.replicate 2 (U64List.cons 1 U64List.nil) : Array U64List)
  (LeanExe.Runtime.retainCount - retainBefore) * 100 + (after - before)

def u64ListTailValue : U64List :=
  u64ListTail u64List123

def u64ListBytes : U64List -> ByteArray
  | .nil => "N".toUTF8
  | .cons head tail =>
      let out := "C(".toUTF8
      let out := LeanExe.Ascii.appendUInt64Decimal out head
      let out := out.push (44 : UInt8)
      let out := out.append (u64ListBytes tail)
      out.push (41 : UInt8)

def leanList123 : List UInt64 :=
  [1, 2, 3]

def leanListScenario (kind : UInt64) : List UInt64 :=
  if kind == 0 then
    []
  else if kind == 1 then
    [7]
  else if kind == 2 then
    [1, 2, 3]
  else
    [8, 13, 21, 34]

def leanListHeadOrZero (xs : List UInt64) : UInt64 :=
  match xs with
  | [] => 0
  | head :: _tail => head

def leanListHeadDemo : UInt64 :=
  leanListHeadOrZero leanList123

def leanListTailHeadDemo : UInt64 :=
  match leanList123 with
  | [] => 0
  | _head :: tail => leanListHeadOrZero tail

def leanListStructuralSum : List UInt64 → UInt64
  | [] => 0
  | head :: tail => head + leanListStructuralSum tail

def leanListStructuralSumDemo : UInt64 :=
  leanListStructuralSum leanList123

def leanListMapAddOne (xs : List UInt64) : List UInt64 :=
  xs.map (fun x => x + 1)

def leanListMapDemo : UInt64 :=
  leanListHeadOrZero (leanListMapAddOne leanList123)

def leanListMapDirectDemo : UInt64 :=
  leanListHeadOrZero (leanList123.map (fun x => x + 1))

def leanListMapDirectBranchDemo (flag : Bool) : UInt64 :=
  let xs := if flag then leanList123 else [9]
  leanListHeadOrZero (xs.map (fun x => x + 1))

def leanListFilterGtOne (xs : List UInt64) : List UInt64 :=
  xs.filter (fun x => x > 1)

def leanListFilterDemo : UInt64 :=
  leanListHeadOrZero (leanListFilterGtOne leanList123)

def leanListFilterDirectDemo : UInt64 :=
  leanListHeadOrZero (leanList123.filter (fun x => x > 1))

def leanListLengthDirectDemo : UInt64 :=
  leanList123.length.toUInt64

def leanListLengthRec : List UInt64 → UInt64
  | [] => 0
  | _head :: tail => 1 + leanListLengthRec tail

def leanListLengthRecDemo : UInt64 :=
  leanListLengthRec leanList123

def leanListAppendDirectDemo : UInt64 :=
  leanListStructuralSum (leanList123 ++ [4, 5])

def leanListAppendDirectBranchDemo (flag : Bool) : UInt64 :=
  let ys := if flag then [4, 5] else []
  leanListStructuralSum (leanList123 ++ ys)

def leanListAppendRec : List UInt64 → List UInt64 → List UInt64
  | [], ys => ys
  | head :: tail, ys => head :: leanListAppendRec tail ys

def leanListAppendRecDemo : UInt64 :=
  leanListStructuralSum (leanListAppendRec leanList123 [4, 5])

def leanListReverseDirectDemo : UInt64 :=
  leanListHeadOrZero leanList123.reverse

def leanListReverseAcc : List UInt64 → List UInt64 → List UInt64
  | [], acc => acc
  | head :: tail, acc => leanListReverseAcc tail (head :: acc)

def leanListReverseRecDemo : UInt64 :=
  leanListHeadOrZero (leanListReverseAcc leanList123 [])

def leanListFoldrDemo : UInt64 :=
  leanList123.foldr (fun x acc => acc * 10 + x) 0

def leanListFoldrRec : List UInt64 → UInt64 → UInt64
  | [], acc => acc
  | head :: tail, acc => leanListFoldrRec tail acc * 10 + head

def leanListFoldrRecDemo : UInt64 :=
  leanListFoldrRec leanList123 0

def leanListFindGtOne (xs : List UInt64) : Option UInt64 :=
  xs.find? (fun x => x > 1)

def leanListFindDemo : UInt64 :=
  match leanListFindGtOne leanList123 with
  | none => 0
  | some value => value

def leanListFindGtTen (xs : List UInt64) : Option UInt64 :=
  xs.find? (fun x => x > 10)

def leanListFindMissingDemo : UInt64 :=
  match leanListFindGtTen leanList123 with
  | none => 0
  | some value => value

def leanListFoldlDecimal (xs : List UInt64) (acc : UInt64) : UInt64 :=
  xs.foldl (fun acc x => acc * 10 + x) acc

def leanListFoldlDemo : UInt64 :=
  leanListFoldlDecimal leanList123 0

def leanListAnyEqTwo (xs : List UInt64) : Bool :=
  xs.any (fun x => x == 2)

def leanListAnyDemo : UInt64 :=
  if leanListAnyEqTwo leanList123 then 1 else 0

def leanListAnyMissing (xs : List UInt64) : Bool :=
  xs.any (fun x => x == 9)

def leanListAnyMissingDemo : UInt64 :=
  if leanListAnyMissing leanList123 then 1 else 0

def leanListFoldlClosedDemo : UInt64 :=
  leanList123.foldl (fun acc x => acc * 10 + x) 0

structure CountSum where
  count : UInt64
  sum : UInt64

def leanListFoldlClosedStruct : CountSum :=
  leanList123.foldl
    (fun acc x => { count := acc.count + 1, sum := acc.sum + x })
    { count := 0, sum := 0 }

def leanListFoldlClosedStructDemo : UInt64 :=
  let result := leanListFoldlClosedStruct
  result.count * 10 + result.sum

def leanListAnyDirectDemo : UInt64 :=
  if leanList123.any (fun x => x == 2) then 1 else 0

def leanListAnyDirectMissingDemo : UInt64 :=
  if leanList123.any (fun x => x == 9) then 1 else 0

def leanListAllDirectDemo : UInt64 :=
  if leanList123.all (fun x => x < 4) then 1 else 0

def leanListAllDirectMissingDemo : UInt64 :=
  if leanList123.all (fun x => x < 3) then 1 else 0

def leanListAppendRecValue : List UInt64 :=
  leanListAppendRec leanList123 [4, 5]

def leanListReverseValue : List UInt64 :=
  leanListReverseAcc leanList123 []

def leanListMapValue : List UInt64 :=
  leanList123.map (fun x => x + 1)

def leanListFilterValue : List UInt64 :=
  leanList123.filter (fun x => x > 1)

def leanListBytes : List UInt64 -> ByteArray
  | [] => "N".toUTF8
  | head :: tail =>
      let out := "C(".toUTF8
      let out := LeanExe.Ascii.appendUInt64Decimal out head
      let out := out.push (44 : UInt8)
      let out := out.append (leanListBytes tail)
      out.push (41 : UInt8)

structure LeanListBox where
  values : List UInt64
  tag : UInt64

def leanListBoxValue : LeanListBox :=
  { values := leanListReverseAcc leanList123 [], tag := 8 }

def leanListBoxScore (box : LeanListBox) : UInt64 :=
  box.tag * 10 + leanListStructuralSum box.values

def leanListBoxScoreDemo : UInt64 :=
  leanListBoxScore leanListBoxValue

def leanListBoxBytes (box : LeanListBox) : ByteArray :=
  let out := "Box(".toUTF8
  let out := LeanExe.Ascii.appendUInt64Decimal out box.tag
  let out := out.push (44 : UInt8)
  let out := out.append (leanListBytes box.values)
  out.push (41 : UInt8)

def leanListScenarioScore (kind needle : UInt64) : UInt64 :=
  let xs := leanListScenario kind
  let found :=
    match xs.find? (fun value => value == needle) with
    | none => 0
    | some value => value
  xs.length.toUInt64 * 1000 + leanListStructuralSum xs * 10 + found

def leanPairList : List (UInt64 × UInt64) :=
  [(7, 70), (2, 20), (9, 90), (2, 22)]

def leanPairListLookup : List (UInt64 × UInt64) → UInt64 → UInt64
  | [], _ => 0
  | (k, v) :: rest, key =>
      if k == key then v else leanPairListLookup rest key

def leanPairListLookupDemo (key : UInt64) : UInt64 :=
  leanPairListLookup leanPairList key

def leanListScenarioReverseValue (kind : UInt64) : List UInt64 :=
  leanListReverseAcc (leanListScenario kind) []

def leanListScenarioAppendMapValue (kind : UInt64) : List UInt64 :=
  (leanListAppendRec (leanListScenario kind) [5]).map (fun value => value + 1)

def pointBytes (point : Point) : ByteArray :=
  let out := "P(".toUTF8
  let out := LeanExe.Ascii.appendUInt64Decimal out point.x
  let out := out.push (44 : UInt8)
  let out := LeanExe.Ascii.appendUInt64Decimal out point.y
  out.push (41 : UInt8)

def pointListValue : List Point :=
  [{ x := 1, y := 2 }, { x := 3, y := 5 }, { x := 8, y := 13 }]

def pointListMapValue : List Point :=
  pointListValue.map (fun point => { x := point.x + 1, y := point.y + 2 })

def pointListFilterValue : List Point :=
  pointListValue.filter (fun point => point.x + 2 < point.y)

def pointListFindValue : Option Point :=
  pointListValue.find? (fun point => point.x == 3)

def pointListAppendReverseValue : List Point :=
  pointListValue.reverse ++ [{ x := 21, y := 34 }]

def pointListFoldlScore : UInt64 :=
  pointListValue.foldl (fun acc point => acc + point.x * 10 + point.y) 0

def pointListFoldrScore : UInt64 :=
  pointListValue.foldr (fun point acc => acc * 100 + point.x * 10 + point.y) 0

def pointListAnyDemo : UInt64 :=
  if pointListValue.any (fun point => point.x == 3 && point.y == 5) then 1 else 0

def pointListAllDemo : UInt64 :=
  if pointListValue.all (fun point => point.x < point.y) then 1 else 0

def pointListBytes : List Point -> ByteArray
  | [] => "N".toUTF8
  | head :: tail =>
      let out := "C(".toUTF8
      let out := out.append (pointBytes head)
      let out := out.push (44 : UInt8)
      let out := out.append (pointListBytes tail)
      out.push (41 : UInt8)

def pointOptionBytes : Option Point -> ByteArray
  | none => "none".toUTF8
  | some point =>
      let out := "some(".toUTF8
      let out := out.append (pointBytes point)
      out.push (41 : UInt8)

def statusBytes : Status -> ByteArray
  | .ok value =>
      let out := "ok(".toUTF8
      let out := LeanExe.Ascii.appendUInt64Decimal out value
      out.push (41 : UInt8)
  | .error code =>
      let out := "error(".toUTF8
      let out := LeanExe.Ascii.appendUInt64Decimal out code
      out.push (41 : UInt8)

def statusListValue : List Status :=
  [Status.ok 1, Status.error 4, Status.ok 9]

def statusListBump : Status -> Status
  | Status.ok value => Status.ok (value + 1)
  | Status.error code => Status.error (code + 1)

def statusListMapValue : List Status :=
  statusListValue.map statusListBump

def statusListFilterValue : List Status :=
  statusListValue.filter (fun status =>
    match status with
    | Status.ok _ => true
    | Status.error _ => false)

def statusListFindValue : Option Status :=
  statusListValue.find? (fun status =>
    match status with
    | Status.ok value => value > 5
    | Status.error _ => false)

def statusListAppendReverseValue : List Status :=
  statusListValue.reverse ++ [Status.error 12]

def statusListFoldlScore : UInt64 :=
  statusListValue.foldl
    (fun acc status =>
      match status with
      | Status.ok value => acc + value
      | Status.error code => acc + code * 10)
    0

def statusListFoldrScore : UInt64 :=
  statusListValue.foldr
    (fun status acc =>
      match status with
      | Status.ok value => acc * 10 + value
      | Status.error code => acc * 10 + code)
    0

def statusListAnyDemo : UInt64 :=
  if statusListValue.any (fun status =>
    match status with
    | Status.ok value => value > 5
    | Status.error _ => false) then 1 else 0

def statusListAllDemo : UInt64 :=
  if statusListValue.all (fun status =>
    match status with
    | Status.ok _ => true
    | Status.error code => code < 10) then 1 else 0

def statusListBytes : List Status -> ByteArray
  | [] => "N".toUTF8
  | head :: tail =>
      let out := "C(".toUTF8
      let out := out.append (statusBytes head)
      let out := out.push (44 : UInt8)
      let out := out.append (statusListBytes tail)
      out.push (41 : UInt8)

def statusOptionBytes : Option Status -> ByteArray
  | none => "none".toUTF8
  | some status =>
      let out := "some(".toUTF8
      let out := out.append (statusBytes status)
      out.push (41 : UInt8)

def byteArrayCellBytes (bytes : ByteArray) : ByteArray :=
  let out := "B(".toUTF8
  let out := LeanExe.Ascii.appendUInt64Decimal out bytes.size.toUInt64
  let out := out.push (58 : UInt8)
  let out := out.append bytes
  out.push (41 : UInt8)

def byteArrayListValue : List ByteArray :=
  ["A".toUTF8, "BC".toUTF8, ByteArray.empty]

def byteArrayListMapValue : List ByteArray :=
  byteArrayListValue.map (fun bytes => bytes.push (33 : UInt8))

def byteArrayListFilterValue : List ByteArray :=
  byteArrayListValue.filter (fun bytes => bytes.size > 1)

def byteArrayListFindValue : Option ByteArray :=
  byteArrayListValue.find? (fun bytes => bytes.size == 0)

def byteArrayListAppendReverseValue : List ByteArray :=
  byteArrayListValue.reverse ++ ["DEF".toUTF8]

def byteArrayListFoldlValue : ByteArray :=
  byteArrayListValue.foldl (fun acc bytes => acc.append bytes) ByteArray.empty

def byteArrayListFoldrValue : ByteArray :=
  byteArrayListValue.foldr (fun bytes acc => acc.append bytes) ByteArray.empty

def byteArrayListAnyDemo : UInt64 :=
  if byteArrayListValue.any (fun bytes => bytes.size == 0) then 1 else 0

def byteArrayListAllDemo : UInt64 :=
  if byteArrayListValue.all (fun bytes => bytes.size < 3) then 1 else 0

def byteArrayListBytes : List ByteArray -> ByteArray
  | [] => "N".toUTF8
  | head :: tail =>
      let out := "C(".toUTF8
      let out := out.append (byteArrayCellBytes head)
      let out := out.push (44 : UInt8)
      let out := out.append (byteArrayListBytes tail)
      out.push (41 : UInt8)

def byteArrayOptionBytes : Option ByteArray -> ByteArray
  | none => "none".toUTF8
  | some bytes =>
      let out := "some(".toUTF8
      let out := out.append (byteArrayCellBytes bytes)
      out.push (41 : UInt8)

def optionByteArrayBytes (value : Option ByteArray) : ByteArray :=
  byteArrayOptionBytes value

def optionByteArrayListValue : List (Option ByteArray) :=
  [some "A".toUTF8, none, some "BC".toUTF8]

def optionByteArrayListMapValue : List (Option ByteArray) :=
  optionByteArrayListValue.map (fun item => item.map (fun bytes => bytes.push (33 : UInt8)))

def optionByteArrayListFilterValue : List (Option ByteArray) :=
  optionByteArrayListValue.filter (fun item =>
    match item with
    | some bytes => bytes.size > 1
    | none => false)

def optionByteArrayListFindValue : Option (Option ByteArray) :=
  optionByteArrayListValue.find? (fun item =>
    match item with
    | some bytes => bytes.size == 1
    | none => false)

def optionByteArrayListAppendReverseValue : List (Option ByteArray) :=
  optionByteArrayListValue.reverse ++ [some "DEF".toUTF8]

def optionByteArrayListAnyDemo : UInt64 :=
  if optionByteArrayListValue.any (fun item =>
    match item with
    | some bytes => bytes.size == 2
    | none => false) then 1 else 0

def optionByteArrayListAllDemo : UInt64 :=
  if optionByteArrayListValue.all (fun item =>
    match item with
    | some bytes => bytes.size < 3
    | none => true) then 1 else 0

def optionByteArrayListFoldlValue : ByteArray :=
  optionByteArrayListValue.foldl
    (fun acc item =>
      let out := acc.append (optionByteArrayBytes item)
      out.push (59 : UInt8))
    ByteArray.empty

def optionByteArrayListFoldrValue : ByteArray :=
  optionByteArrayListValue.foldr
    (fun item acc =>
      let out := optionByteArrayBytes item
      let out := out.push (59 : UInt8)
      out.append acc)
    ByteArray.empty

def optionByteArrayListFoldlStateValue : ByteOutputState :=
  optionByteArrayListValue.foldl
    (fun acc item =>
      let out := acc.bytes.append (optionByteArrayBytes item)
      { count := acc.count + 1, bytes := out.push (59 : UInt8) })
    ({ count := 0, bytes := ByteArray.empty } : ByteOutputState)

def optionByteArrayListFoldlTaggedAccumulatorValue : Option ByteArray :=
  optionByteArrayListValue.foldl
    (fun acc item =>
      match acc, item with
      | none, none => some "N".toUTF8
      | none, some bytes => some bytes
      | some out, none => some (out.push (45 : UInt8))
      | some out, some bytes => some (out.append bytes))
    none

def optionByteArrayListBytes : List (Option ByteArray) -> ByteArray
  | [] => "N".toUTF8
  | head :: tail =>
      let out := "C(".toUTF8
      let out := out.append (optionByteArrayBytes head)
      let out := out.push (44 : UInt8)
      let out := out.append (optionByteArrayListBytes tail)
      out.push (41 : UInt8)

def optionOptionByteArrayBytes : Option (Option ByteArray) -> ByteArray
  | none => "none".toUTF8
  | some item =>
      let out := "some(".toUTF8
      let out := out.append (optionByteArrayBytes item)
      out.push (41 : UInt8)

def exceptByteArrayUInt64Bytes : Except ByteArray UInt64 -> ByteArray
  | Except.error bytes =>
      let out := "error(".toUTF8
      let out := out.append (byteArrayCellBytes bytes)
      out.push (41 : UInt8)
  | Except.ok value =>
      let out := "ok(".toUTF8
      let out := LeanExe.Ascii.appendUInt64Decimal out value
      out.push (41 : UInt8)

def exceptByteArrayByteArrayBytes : Except ByteArray ByteArray -> ByteArray
  | Except.error bytes =>
      let out := "error(".toUTF8
      let out := out.append (byteArrayCellBytes bytes)
      out.push (41 : UInt8)
  | Except.ok bytes =>
      let out := "ok(".toUTF8
      let out := out.append (byteArrayCellBytes bytes)
      out.push (41 : UInt8)

def exceptByteArrayUInt64ListValue : List (Except ByteArray UInt64) :=
  [Except.ok 1, Except.error "E".toUTF8, Except.ok 5]

def exceptByteArrayUInt64ListMapValue : List (Except ByteArray UInt64) :=
  exceptByteArrayUInt64ListValue.map (fun item =>
    match item with
    | Except.error bytes => Except.error (bytes.push (33 : UInt8))
    | Except.ok value => Except.ok (value + 1))

def exceptByteArrayUInt64ListFilterValue : List (Except ByteArray UInt64) :=
  exceptByteArrayUInt64ListValue.filter (fun item =>
    match item with
    | Except.error _ => true
    | Except.ok value => value > 3)

def exceptByteArrayUInt64ListFindValue : Option (Except ByteArray UInt64) :=
  exceptByteArrayUInt64ListValue.find? (fun item =>
    match item with
    | Except.error _ => true
    | Except.ok _ => false)

def exceptByteArrayUInt64ListAppendReverseValue : List (Except ByteArray UInt64) :=
  exceptByteArrayUInt64ListValue.reverse ++ [Except.error "FG".toUTF8]

def exceptByteArrayUInt64ListAnyDemo : UInt64 :=
  if exceptByteArrayUInt64ListValue.any (fun item =>
    match item with
    | Except.error _ => true
    | Except.ok _ => false) then 1 else 0

def exceptByteArrayUInt64ListAllDemo : UInt64 :=
  if exceptByteArrayUInt64ListValue.all (fun item =>
    match item with
    | Except.error bytes => bytes.size == 1
    | Except.ok value => value < 10) then 1 else 0

def exceptByteArrayUInt64ListFoldlValue : ByteArray :=
  exceptByteArrayUInt64ListValue.foldl
    (fun acc item =>
      let out := acc.append (exceptByteArrayUInt64Bytes item)
      out.push (59 : UInt8))
    ByteArray.empty

def exceptByteArrayUInt64ListFoldrValue : ByteArray :=
  exceptByteArrayUInt64ListValue.foldr
    (fun item acc =>
      let out := exceptByteArrayUInt64Bytes item
      let out := out.push (59 : UInt8)
      out.append acc)
    ByteArray.empty

def exceptByteArrayUInt64ListFoldlStateValue : ByteOutputState :=
  exceptByteArrayUInt64ListValue.foldl
    (fun acc item =>
      let out := acc.bytes.append (exceptByteArrayUInt64Bytes item)
      { count := acc.count + 1, bytes := out.push (59 : UInt8) })
    ({ count := 0, bytes := ByteArray.empty } : ByteOutputState)

def exceptByteArrayUInt64ListFoldlTaggedAccumulatorValue : Except ByteArray ByteArray :=
  exceptByteArrayUInt64ListValue.foldl
    (fun acc item =>
      match acc, item with
      | Except.error out, Except.error bytes => Except.error (out.append bytes)
      | Except.error out, Except.ok value =>
          Except.error (LeanExe.Ascii.appendUInt64Decimal (out.push (35 : UInt8)) value)
      | Except.ok out, Except.error bytes => Except.error (out.append bytes)
      | Except.ok out, Except.ok value =>
          Except.ok (LeanExe.Ascii.appendUInt64Decimal out value))
    (Except.ok ByteArray.empty)

def exceptByteArrayUInt64ListBytes : List (Except ByteArray UInt64) -> ByteArray
  | [] => "N".toUTF8
  | head :: tail =>
      let out := "C(".toUTF8
      let out := out.append (exceptByteArrayUInt64Bytes head)
      let out := out.push (44 : UInt8)
      let out := out.append (exceptByteArrayUInt64ListBytes tail)
      out.push (41 : UInt8)

def optionExceptByteArrayUInt64Bytes : Option (Except ByteArray UInt64) -> ByteArray
  | none => "none".toUTF8
  | some item =>
      let out := "some(".toUTF8
      let out := out.append (exceptByteArrayUInt64Bytes item)
      out.push (41 : UInt8)

def byteOutputStateBytes (state : ByteOutputState) : ByteArray :=
  let out := "state(".toUTF8
  let out := LeanExe.Ascii.appendUInt64Decimal out state.count
  let out := out.push (44 : UInt8)
  let out := out.append (byteArrayCellBytes state.bytes)
  out.push (41 : UInt8)

def optionUInt64Bytes : Option UInt64 -> ByteArray
  | none => "none".toUTF8
  | some value =>
      let out := "some(".toUTF8
      let out := LeanExe.Ascii.appendUInt64Decimal out value
      out.push (41 : UInt8)

def optionUInt64ListValue : List (Option UInt64) :=
  [some 1, none, some 5]

def optionUInt64ListMapValue : List (Option UInt64) :=
  optionUInt64ListValue.map (fun item => item.map (fun value => value + 1))

def optionUInt64ListFilterValue : List (Option UInt64) :=
  optionUInt64ListValue.filter (fun item => item.isSome)

def optionUInt64ListFindValue : Option (Option UInt64) :=
  optionUInt64ListValue.find? (fun item =>
    match item with
    | some value => value > 3
    | none => false)

def optionUInt64ListAppendReverseValue : List (Option UInt64) :=
  optionUInt64ListValue.reverse ++ [some 8]

def optionUInt64ListFoldlScore : UInt64 :=
  optionUInt64ListValue.foldl
    (fun acc item =>
      match item with
      | none => acc + 10
      | some value => acc + value)
    0

def optionUInt64ListFoldrScore : UInt64 :=
  optionUInt64ListValue.foldr
    (fun item acc =>
      match item with
      | none => acc * 10
      | some value => acc * 10 + value)
    0

def optionUInt64ListAnyDemo : UInt64 :=
  if optionUInt64ListValue.any (fun item =>
    match item with
    | some value => value > 3
    | none => false) then 1 else 0

def optionUInt64ListAllDemo : UInt64 :=
  if optionUInt64ListValue.all (fun item =>
    match item with
    | some value => value < 10
    | none => true) then 1 else 0

def optionUInt64ListBytes : List (Option UInt64) -> ByteArray
  | [] => "N".toUTF8
  | head :: tail =>
      let out := "C(".toUTF8
      let out := out.append (optionUInt64Bytes head)
      let out := out.push (44 : UInt8)
      let out := out.append (optionUInt64ListBytes tail)
      out.push (41 : UInt8)

def optionOptionUInt64Bytes : Option (Option UInt64) -> ByteArray
  | none => "none".toUTF8
  | some item =>
      let out := "some(".toUTF8
      let out := out.append (optionUInt64Bytes item)
      out.push (41 : UInt8)

inductive U64Tree where
  | leaf : UInt64 → U64Tree
  | node : Array U64Tree → U64Tree

inductive U64Binary where
  | leaf : UInt64 → U64Binary
  | node : U64Binary → U64Binary → U64Binary

inductive U64Expr where
  | lit : UInt64 → U64Expr
  | add : U64Expr → U64Expr → U64Expr
  | mul : U64Expr → U64Expr → U64Expr

structure ExprBox where
  value : U64Expr
  bias : UInt64

inductive ExprSlot where
  | empty : ExprSlot
  | filled : UInt64 → U64Expr → ExprSlot

structure RecursiveArrayBox where
  values : Array U64List
  marker : UInt64

inductive RecursiveArraySlot where
  | empty : RecursiveArraySlot
  | values : Array U64List -> RecursiveArraySlot

mutual
inductive MutJson where
  | null : MutJson
  | num : UInt64 → MutJson
  | arr : Array MutJson → MutJson
  | obj : Array MutField → MutJson

inductive MutField where
  | mk : UInt64 → MutJson → MutField
end

structure MutFieldBox where
  field : MutField
  salt : UInt64

inductive MutJsonSlot where
  | missing : MutJsonSlot
  | present : MutJson → MutJsonSlot

structure BytesFoldState where
  first : Bool
  out : ByteArray

def appendSeparatedBytes (state : BytesFoldState) (bytes : ByteArray) : BytesFoldState :=
  let out :=
    if state.first then
      state.out
    else
      state.out.push (44 : UInt8)
  { first := false, out := out.append bytes }

def u64TreeFirstChildHead (tree : U64Tree) : UInt64 :=
  match tree with
  | .leaf value => value
  | .node children =>
      match children[0]? with
      | some child =>
          match child with
          | .leaf value => value
          | .node _ => 99
      | none => 0

def u64TreeArrayFieldDemo : UInt64 :=
  let tree := U64Tree.node #[U64Tree.leaf 7, U64Tree.node #[U64Tree.leaf 11]]
  u64TreeFirstChildHead tree

def u64TreeSize : U64Tree → UInt64
  | .leaf _value => 1
  | .node children =>
      children.foldl (fun acc child => acc + u64TreeSize child) 1

def u64TreeSizeDemo : UInt64 :=
  u64TreeSize
    (U64Tree.node #[
      U64Tree.leaf 1,
      U64Tree.node #[U64Tree.leaf 2, U64Tree.leaf 3],
      U64Tree.leaf 4
    ])

def u64TreeValue : U64Tree :=
  U64Tree.node #[
    U64Tree.leaf 1,
    U64Tree.node #[U64Tree.leaf 2, U64Tree.leaf 3],
    U64Tree.leaf 4
  ]

def u64TreeBytes : U64Tree -> ByteArray
  | .leaf value =>
      let out := "L(".toUTF8
      let out := LeanExe.Ascii.appendUInt64Decimal out value
      out.push (41 : UInt8)
  | .node children =>
      let state :=
        children.foldl
          (fun state child => appendSeparatedBytes state (u64TreeBytes child))
          { first := true, out := "T[".toUTF8 }
      state.out.push (93 : UInt8)

def u64BinaryStructuralSize : U64Binary → UInt64
  | .leaf _value => 1
  | .node left right => u64BinaryStructuralSize left + u64BinaryStructuralSize right

def u64BinaryStructuralSizeDemo : UInt64 :=
  u64BinaryStructuralSize
    (U64Binary.node (U64Binary.leaf 1) (U64Binary.node (U64Binary.leaf 2) (U64Binary.leaf 3)))

def u64BinaryValue : U64Binary :=
  U64Binary.node
    (U64Binary.leaf 1)
    (U64Binary.node (U64Binary.leaf 2) (U64Binary.leaf 3))

def u64BinaryScenario (kind : UInt64) : U64Binary :=
  if kind == 0 then
    U64Binary.leaf 5
  else if kind == 1 then
    U64Binary.node
      (U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2))
      (U64Binary.node (U64Binary.leaf 3) (U64Binary.leaf 4))
  else if kind == 2 then
    U64Binary.node
      (U64Binary.node
        (U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2))
        (U64Binary.leaf 3))
      (U64Binary.leaf 4)
  else
    U64Binary.node
      (U64Binary.leaf 1)
      (U64Binary.node
        (U64Binary.leaf 2)
        (U64Binary.node (U64Binary.leaf 3) (U64Binary.leaf 4)))

def u64BinaryBytes : U64Binary -> ByteArray
  | .leaf value =>
      let out := "L(".toUTF8
      let out := LeanExe.Ascii.appendUInt64Decimal out value
      out.push (41 : UInt8)
  | .node left right =>
      let out := "B(".toUTF8
      let out := out.append (u64BinaryBytes left)
      let out := out.push (44 : UInt8)
      let out := out.append (u64BinaryBytes right)
      out.push (41 : UInt8)

def u64BinaryNodeCount : U64Binary → UInt64
  | .leaf _value => 1
  | .node left right => 1 + u64BinaryNodeCount left + u64BinaryNodeCount right

def u64BinaryHeight : U64Binary → UInt64
  | .leaf _value => 1
  | .node left right =>
      let leftHeight := u64BinaryHeight left
      let rightHeight := u64BinaryHeight right
      if leftHeight < rightHeight then rightHeight + 1 else leftHeight + 1

def u64BinaryLeafSum : U64Binary → UInt64
  | .leaf value => value
  | .node left right => u64BinaryLeafSum left + u64BinaryLeafSum right

def u64BinaryContains (needle : UInt64) : U64Binary → Bool
  | .leaf value => value == needle
  | .node left right =>
      u64BinaryContains needle left || u64BinaryContains needle right

def u64BinaryLeftmost : U64Binary → UInt64
  | .leaf value => value
  | .node left _right => u64BinaryLeftmost left

def u64BinaryMapAddOne : U64Binary → U64Binary
  | .leaf value => .leaf (value + 1)
  | .node left right =>
      .node (u64BinaryMapAddOne left) (u64BinaryMapAddOne right)

def u64BinaryMirror : U64Binary → U64Binary
  | .leaf value => .leaf value
  | .node left right => .node (u64BinaryMirror right) (u64BinaryMirror left)

def u64BinaryInsertLeftmost (value : UInt64) : U64Binary → U64Binary
  | .leaf leafValue => .node (.leaf value) (.leaf leafValue)
  | .node left right => .node (u64BinaryInsertLeftmost value left) right

def u64BinaryFindLeaf (needle : UInt64) : U64Binary → Option U64Binary
  | .leaf value =>
      if value == needle then some (.leaf value) else none
  | .node left right =>
      match u64BinaryFindLeaf needle left with
      | some found => some found
      | none => u64BinaryFindLeaf needle right

def u64BinaryRequireLeaf (needle : UInt64) (tree : U64Binary) : Except UInt64 U64Binary :=
  match u64BinaryFindLeaf needle tree with
  | some found => Except.ok found
  | none => Except.error needle

def u64BinaryScenarioScore (kind needle : UInt64) : UInt64 :=
  let tree := u64BinaryScenario kind
  let found := if u64BinaryContains needle tree then 1 else 0
  u64BinaryNodeCount tree * 10000 +
    u64BinaryHeight tree * 100 +
    u64BinaryLeafSum tree * 10 +
    found

def u64BinaryScenarioValue (kind : UInt64) : U64Binary :=
  u64BinaryScenario kind

def u64BinaryScenarioMirrorValue (kind : UInt64) : U64Binary :=
  u64BinaryMirror (u64BinaryScenario kind)

def u64BinaryScenarioFindValue (kind needle : UInt64) : Option U64Binary :=
  u64BinaryFindLeaf needle (u64BinaryScenario kind)

def u64BinaryScenarioRequireByteErrorValue (kind needle : UInt64) : Except ByteArray U64Binary :=
  match u64BinaryFindLeaf needle (u64BinaryScenario kind) with
  | none =>
      let out := "missing:".toUTF8
      Except.error (LeanExe.Ascii.appendUInt64Decimal out needle)
  | some found => Except.ok found

def u64BinaryOptionMapValue (kind needle : UInt64) : Option U64Binary :=
  Option.map
    (fun tree => u64BinaryMirror tree)
    (u64BinaryScenarioFindValue kind needle)

def u64BinaryExceptMapValue (kind needle : UInt64) : Except ByteArray U64Binary :=
  Except.map
    (fun tree => u64BinaryMapAddOne tree)
    (u64BinaryScenarioRequireByteErrorValue kind needle)

def u64BinaryScenarioExceptValue (kind flag : UInt64) : Except ByteArray U64Binary :=
  if flag == 0 then
    Except.error "disabled".toUTF8
  else
    Except.ok (u64BinaryScenario kind)

def u64BinaryExceptBindValue (kind flag : UInt64) : Except ByteArray U64Binary :=
  Except.bind
    (u64BinaryScenarioExceptValue kind flag)
    (fun tree =>
      if u64BinaryHeight tree > 1 then
        Except.ok (u64BinaryMirror tree)
      else
        Except.error "leaf".toUTF8)

def u64BinaryShapeDemo : UInt64 :=
  let tree := u64BinaryValue
  let foundTwo := if u64BinaryContains 2 tree then 1 else 0
  let foundNine := if u64BinaryContains 9 tree then 1 else 0
  u64BinaryNodeCount tree * 100 + u64BinaryHeight tree * 10 + foundTwo + foundNine

def u64BinaryMapLeafSumDemo : UInt64 :=
  u64BinaryLeafSum (u64BinaryMapAddOne u64BinaryValue)

def u64BinaryMirrorLeftmostDemo : UInt64 :=
  u64BinaryLeftmost (u64BinaryMirror u64BinaryValue)

def u64BinaryInsertShapeDemo : UInt64 :=
  let tree := u64BinaryInsertLeftmost 9 u64BinaryValue
  u64BinaryNodeCount tree * 100 + u64BinaryHeight tree * 10 + u64BinaryLeafSum tree

def u64BinaryFindOptionDemo : UInt64 :=
  match u64BinaryFindLeaf 2 u64BinaryValue with
  | none => 0
  | some tree => u64BinaryLeafSum tree

def u64BinaryFindMissingDemo : UInt64 :=
  match u64BinaryFindLeaf 9 u64BinaryValue with
  | none => 7
  | some tree => u64BinaryLeafSum tree

def u64BinaryRequireOkDemo : UInt64 :=
  match u64BinaryRequireLeaf 2 u64BinaryValue with
  | Except.error code => code
  | Except.ok tree => u64BinaryLeafSum tree + 10

def u64BinaryRequireErrorDemo : UInt64 :=
  match u64BinaryRequireLeaf 9 u64BinaryValue with
  | Except.error code => code
  | Except.ok tree => u64BinaryLeafSum tree

def u64BinaryMapValue : U64Binary :=
  u64BinaryMapAddOne u64BinaryValue

def u64BinaryMirrorValue : U64Binary :=
  u64BinaryMirror u64BinaryValue

def u64BinaryInsertValue : U64Binary :=
  u64BinaryInsertLeftmost 9 u64BinaryValue

def u64BinaryFindValue : Option U64Binary :=
  u64BinaryFindLeaf 2 u64BinaryValue

def u64BinaryFindMissingValue : Option U64Binary :=
  u64BinaryFindLeaf 9 u64BinaryValue

def u64BinaryRequireValue : Except UInt64 U64Binary :=
  u64BinaryRequireLeaf 2 u64BinaryValue

def u64BinaryRequireMissingValue : Except UInt64 U64Binary :=
  u64BinaryRequireLeaf 9 u64BinaryValue

structure U64BinaryBox where
  tree : U64Binary
  label : UInt64

structure U64BinaryPairBox where
  left : U64Binary
  right : U64Binary
  marker : UInt64

inductive U64BinaryPairSlot where
  | empty : U64BinaryPairSlot
  | pair : U64Binary → U64Binary → U64BinaryPairSlot

def u64BinaryBoxValue : U64BinaryBox :=
  { tree := u64BinaryMirror u64BinaryValue, label := 7 }

def u64BinaryBoxScore (box : U64BinaryBox) : UInt64 :=
  box.label * 100 + u64BinaryLeafSum box.tree

def u64BinaryBoxScoreDemo : UInt64 :=
  u64BinaryBoxScore u64BinaryBoxValue

def u64BinarySharedChildScore : UInt64 :=
  let child := U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2)
  let tree := U64Binary.node child child
  u64BinaryNodeCount tree * 10000 + u64BinaryHeight tree * 100 + u64BinaryLeafSum tree

def u64BinaryLeftSubtree? : U64Binary → Option U64Binary
  | .leaf _ => none
  | .node left _right => some left

def u64BinaryReturnedSubtreeAliasScore : UInt64 :=
  let shared := U64Binary.node (U64Binary.leaf 8) (U64Binary.leaf 9)
  let tree := U64Binary.node shared shared
  match u64BinaryLeftSubtree? tree with
  | none => 0
  | some left => u64BinaryNodeCount left * 100 + u64BinaryLeafSum left

def u64BinarySharedArrayScore : UInt64 :=
  let child := U64Binary.node (U64Binary.leaf 2) (U64Binary.leaf 3)
  let values := #[child, child, U64Binary.leaf 4]
  values.foldl
    (fun acc tree => acc + u64BinaryNodeCount tree * 100 + u64BinaryLeafSum tree)
    0

def u64BinarySharedStructAliasScore : UInt64 :=
  let child := U64Binary.node (U64Binary.leaf 5) (U64Binary.leaf 6)
  let box : U64BinaryPairBox := { left := child, right := child, marker := 7 }
  u64BinaryNodeCount box.left * 10000 +
    u64BinaryNodeCount box.right * 100 +
    u64BinaryLeafSum box.left +
    u64BinaryLeafSum box.right +
    box.marker

def u64BinarySharedTaggedAliasScore : UInt64 :=
  let child := U64Binary.node (U64Binary.leaf 10) (U64Binary.leaf 11)
  let slot := U64BinaryPairSlot.pair child child
  match slot with
  | .empty => 1
  | .pair left right =>
      u64BinaryNodeCount left * 10000 +
        u64BinaryNodeCount right * 100 +
        u64BinaryLeafSum left +
        u64BinaryLeafSum right

def u64BinaryBoxFlowValue (kind flag : UInt64) : U64BinaryBox :=
  let source := u64BinaryScenario kind
  if flag == 0 then
    { tree := u64BinaryMapAddOne source, label := 20 }
  else
    { tree := u64BinaryMirror source, label := 10 }

def u64BinaryPairSlotFlowValue (kind : UInt64) : U64BinaryPairSlot :=
  if kind == 0 then
    U64BinaryPairSlot.empty
  else
    let source := u64BinaryScenario kind
    U64BinaryPairSlot.pair source (u64BinaryMirror source)

def u64BinaryArrayFlowValue (kind : UInt64) : Array U64Binary :=
  let source := u64BinaryScenario kind
  let selected :=
    if u64BinaryContains 3 source then
      source
    else
      u64BinaryMirror source
  #[selected, u64BinaryMapAddOne source, u64BinaryMirror selected]

def u64BinaryLoopGrowValue : U64Binary := Id.run do
  let mut tree : U64Binary := U64Binary.leaf 0
  for i in [0:3] do
    tree := U64Binary.node tree (U64Binary.leaf i.toUInt64)
  return tree

def u64BinaryLoopOptionValue : Option U64Binary := Id.run do
  let mut result : Option U64Binary := none
  for i in [0:4] do
    if i == (2 : Nat) then
      result := some (U64Binary.node (U64Binary.leaf i.toUInt64) (U64Binary.leaf 9))
  return result

def u64BinaryLoopExceptValue : Except ByteArray U64Binary := Id.run do
  let mut result : Except ByteArray U64Binary := Except.error "none".toUTF8
  for i in [0:3] do
    if i == (1 : Nat) then
      result := Except.ok (U64Binary.node (U64Binary.leaf i.toUInt64) (U64Binary.leaf 8))
  return result

def u64BinaryBoxBytes (box : U64BinaryBox) : ByteArray :=
  let out := "Box(".toUTF8
  let out := LeanExe.Ascii.appendUInt64Decimal out box.label
  let out := out.push (44 : UInt8)
  let out := out.append (u64BinaryBytes box.tree)
  out.push (41 : UInt8)

def u64BinaryPairSlotBytes : U64BinaryPairSlot -> ByteArray
  | .empty => "empty".toUTF8
  | .pair left right =>
      let out := "pair(".toUTF8
      let out := out.append (u64BinaryBytes left)
      let out := out.push (44 : UInt8)
      let out := out.append (u64BinaryBytes right)
      out.push (41 : UInt8)

def u64BinaryArrayBytes (values : Array U64Binary) : ByteArray :=
  let state :=
    values.foldl
      (fun state tree => appendSeparatedBytes state (u64BinaryBytes tree))
      { first := true, out := ByteArray.empty.push (91 : UInt8) }
  state.out.push (93 : UInt8)

def u64BinaryOptionBytes : Option U64Binary -> ByteArray
  | none => "none".toUTF8
  | some tree =>
      let out := "some(".toUTF8
      let out := out.append (u64BinaryBytes tree)
      out.push (41 : UInt8)

def u64BinaryExceptBytes : Except UInt64 U64Binary -> ByteArray
  | Except.error code =>
      let out := "error(".toUTF8
      let out := LeanExe.Ascii.appendUInt64Decimal out code
      out.push (41 : UInt8)
  | Except.ok tree =>
      let out := "ok(".toUTF8
      let out := out.append (u64BinaryBytes tree)
      out.push (41 : UInt8)

def u64BinaryByteErrorExceptBytes : Except ByteArray U64Binary -> ByteArray
  | Except.error bytes =>
      let out := "error(".toUTF8
      let out := out.append bytes
      out.push (41 : UInt8)
  | Except.ok tree =>
      let out := "ok(".toUTF8
      let out := out.append (u64BinaryBytes tree)
      out.push (41 : UInt8)

def u64ExprEval : U64Expr → UInt64
  | .lit value => value
  | .add left right => u64ExprEval left + u64ExprEval right
  | .mul left right => u64ExprEval left * u64ExprEval right

def u64ExprEvalDemo : UInt64 :=
  u64ExprEval
    (U64Expr.mul
      (U64Expr.add (U64Expr.lit 2) (U64Expr.lit 3))
      (U64Expr.add (U64Expr.lit 4) (U64Expr.lit 5)))

def exprBoxScore (box : ExprBox) : UInt64 :=
  box.bias + u64ExprEval box.value

def recursiveStructFieldDemo : UInt64 :=
  exprBoxScore { value := U64Expr.add (U64Expr.lit 8) (U64Expr.lit 9), bias := 4 }

def recursiveStructArrayFoldDemo : UInt64 :=
  let boxes : Array ExprBox :=
    #[
      { value := U64Expr.lit 3, bias := 10 },
      { value := U64Expr.mul (U64Expr.lit 2) (U64Expr.lit 5), bias := 1 }
    ]
  boxes.foldl (fun acc box => acc + exprBoxScore box) 0

def exprSlotScore : ExprSlot → UInt64
  | .empty => 0
  | .filled tag value => tag + u64ExprEval value

def recursiveTaggedPayloadDemo : UInt64 :=
  exprSlotScore (ExprSlot.filled 7 (U64Expr.add (U64Expr.lit 4) (U64Expr.lit 6)))

def recursiveTaggedArrayFindDemo : UInt64 :=
  let slots : Array ExprSlot :=
    #[
      ExprSlot.empty,
      ExprSlot.filled 4 (U64Expr.mul (U64Expr.lit 3) (U64Expr.lit 5)),
      ExprSlot.filled 9 (U64Expr.lit 1)
    ]
  match slots.find? (fun slot =>
    match slot with
    | .empty => false
    | .filled tag _value => tag == 4) with
  | none => 0
  | some slot => exprSlotScore slot

def mutJsonValue : MutJson :=
  MutJson.obj #[
    MutField.mk 2 (MutJson.num 7),
    MutField.mk 3 (MutJson.arr #[MutJson.null, MutJson.num 5])
  ]

mutual
def mutJsonBytes : MutJson -> ByteArray
  | .null => "null".toUTF8
  | .num value => LeanExe.Ascii.appendUInt64Decimal ByteArray.empty value
  | .arr items =>
      let state :=
        items.foldl
          (fun state item => appendSeparatedBytes state (mutJsonBytes item))
          { first := true, out := ByteArray.empty.push (91 : UInt8) }
      state.out.push (93 : UInt8)
  | .obj fields =>
      let state :=
        fields.foldl
          (fun state field => appendSeparatedBytes state (mutFieldBytes field))
          { first := true, out := ByteArray.empty.push (123 : UInt8) }
      state.out.push (125 : UInt8)

def mutFieldBytes : MutField -> ByteArray
  | .mk key value =>
      let out := LeanExe.Ascii.appendUInt64Decimal ByteArray.empty key
      let out := out.push (58 : UInt8)
      out.append (mutJsonBytes value)
end

def mutJsonShallowScore : MutJson → UInt64
  | .null => 0
  | .num value => value
  | .arr items => items.size.toUInt64
  | .obj fields => fields.size.toUInt64

def mutFieldScore : MutField → UInt64
  | .mk key value => key * 10 + mutJsonShallowScore value

def mutJsonObjectScore : MutJson → UInt64
  | .obj fields => fields.foldl (fun acc field => acc + mutFieldScore field) 1
  | .null => 0
  | .num value => value
  | .arr items => items.size.toUInt64

def mutualJsonArrayDemo : UInt64 :=
  match MutJson.arr #[MutJson.num 3, MutJson.obj #[MutField.mk 4 MutJson.null]] with
  | .arr items => items.foldl (fun acc item => acc + mutJsonShallowScore item) 0
  | .null => 0
  | .num value => value
  | .obj fields => fields.size.toUInt64

def mutualJsonObjectDemo : UInt64 :=
  mutJsonObjectScore
    (MutJson.obj #[
      MutField.mk 2 (MutJson.num 7),
      MutField.mk 3 (MutJson.arr #[MutJson.null, MutJson.num 5])
    ])

def mutFieldBoxScore (box : MutFieldBox) : UInt64 :=
  box.salt + mutFieldScore box.field

def mutualWrappedFieldArrayDemo : UInt64 :=
  let boxes : Array MutFieldBox :=
    #[
      { field := MutField.mk 1 (MutJson.num 2), salt := 5 },
      { field := MutField.mk 3 (MutJson.arr #[MutJson.null]), salt := 7 }
    ]
  boxes.foldl (fun acc box => acc + mutFieldBoxScore box) 0

def mutJsonSlotScore : MutJsonSlot → UInt64
  | .missing => 0
  | .present value => 100 + mutJsonShallowScore value

def mutualTaggedArrayFindDemo : UInt64 :=
  let slots : Array MutJsonSlot :=
    #[
      MutJsonSlot.missing,
      MutJsonSlot.present (MutJson.obj #[MutField.mk 1 MutJson.null, MutField.mk 2 (MutJson.num 3)])
    ]
  match slots.find? (fun slot =>
    match slot with
    | .missing => false
    | .present value => mutJsonShallowScore value == 2) with
  | none => 0
  | some slot => mutJsonSlotScore slot

mutual
def mutJsonDeepSize : MutJson → UInt64
  | .null => 1
  | .num _value => 1
  | .arr items => items.foldl (fun acc item => acc + mutJsonDeepSize item) 1
  | .obj fields => fields.foldl (fun acc field => acc + mutFieldDeepSize field) 1

def mutFieldDeepSize : MutField → UInt64
  | .mk key value => key + mutJsonDeepSize value
end

def mutualStructuralJsonSizeDemo : UInt64 :=
  mutJsonDeepSize
    (MutJson.obj #[
      MutField.mk 2 (MutJson.num 7),
      MutField.mk 3 (MutJson.arr #[MutJson.null, MutJson.num 5])
    ])

def mutualStructuralFieldSizeDemo : UInt64 :=
  mutFieldDeepSize
    (MutField.mk 4
      (MutJson.obj #[
        MutField.mk 1 MutJson.null,
        MutField.mk 2 (MutJson.arr #[MutJson.num 8])
      ]))

mutual
inductive TriA where
  | leaf : UInt64 → TriA
  | bs : Array TriB → TriA

inductive TriB where
  | leaf : UInt64 → TriB
  | cs : Array TriC → TriB

inductive TriC where
  | leaf : UInt64 → TriC
  | as : Array TriA → TriC
end

mutual
def triAScore : TriA → UInt64
  | .leaf value => value
  | .bs items => items.foldl (fun acc item => acc + triBScore item) 1

def triBScore : TriB → UInt64
  | .leaf value => value
  | .cs items => items.foldl (fun acc item => acc + triCScore item) 2

def triCScore : TriC → UInt64
  | .leaf value => value
  | .as items => items.foldl (fun acc item => acc + triAScore item) 3
end

def mutualStructuralTriADemo : UInt64 :=
  triAScore
    (TriA.bs #[
      TriB.leaf 4,
      TriB.cs #[TriC.leaf 5, TriC.as #[TriA.leaf 6]]
    ])

def mutualStructuralTriBDemo : UInt64 :=
  triBScore
    (TriB.cs #[
      TriC.as #[TriA.bs #[TriB.leaf 2]],
      TriC.leaf 7
    ])

def mutualStructuralTriCDemo : UInt64 :=
  triCScore
    (TriC.as #[
      TriA.bs #[TriB.cs #[TriC.leaf 1]],
      TriA.leaf 8
    ])

def rejectRecursiveInductiveParam (xs : U64List) : UInt64 :=
  u64ListHeadOrZero xs

def rejectRecursiveInductiveReturn : U64List :=
  u64List123

def rejectRecursiveArrayParam (xs : Array U64List) : Nat :=
  xs.size

def rejectRecursiveArrayReturn : Array U64List :=
  #[u64List123]

def rejectRecursiveStructParam (box : ExprBox) : UInt64 :=
  exprBoxScore box

def rejectRecursiveTaggedParam (slot : ExprSlot) : UInt64 :=
  exprSlotScore slot

def rejectRecursiveOptionArrayParam (value : Option (Array U64List)) : UInt64 :=
  match value with
  | none => 0
  | some xs => xs.size.toUInt64

def rejectRecursiveOptionArrayReturn : Option (Array U64List) :=
  some #[u64List123]

def rejectRecursiveStructArrayParam (box : RecursiveArrayBox) : UInt64 :=
  box.marker + box.values.size.toUInt64

def rejectRecursiveTaggedArrayParam (slot : RecursiveArraySlot) : UInt64 :=
  match slot with
  | .empty => 0
  | .values xs => xs.size.toUInt64

def rejectMutualJsonParam (json : MutJson) : UInt64 :=
  mutJsonObjectScore json

def rejectMutualFieldParam (field : MutField) : UInt64 :=
  mutFieldScore field

def rejectMutualJsonReturn : MutJson :=
  MutJson.num 1

def rejectMutualFieldArrayReturn : Array MutField :=
  #[MutField.mk 1 MutJson.null]

def leanListConcatDirectDemo (value : UInt64) : UInt64 :=
  leanListStructuralSum (leanList123.concat value)

def rejectListFoldlLocalCallback : UInt64 :=
  let folder := fun (acc : UInt64) (value : UInt64) => acc * 10 + value
  leanList123.foldl folder 0

def rejectListFoldlFunctionAccumulator : UInt64 :=
  let folder :=
    leanList123.foldl
      (fun acc value => fun seed => acc (seed + value))
      (fun seed : UInt64 => seed + 1)
  folder 10

def rejectListNestedClosedFold : UInt64 :=
  leanList123.foldl
    (fun acc value => acc + (leanList123.foldl (fun inner item => inner + item + value) 0))
    0

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

def idRunMutNestedIf : UInt64 := Id.run do
  let mut score := (1 : UInt64)
  let mut count := (0 : UInt64)
  if score == (1 : UInt64) then
    score := score + (2 : UInt64)
    if count == (0 : UInt64) then
      count := count + (4 : UInt64)
    else
      count := count + (40 : UInt64)
  else
    score := score + (20 : UInt64)
  return score * (10 : UInt64) + count

def idRunMutStructureReturn : Point := Id.run do
  let mut point : Point := { x := 1, y := 2 }
  if point.x < point.y then
    point := { point with x := point.y + 3 }
  else
    point := { point with y := point.x + 3 }
  return point

def idRunMutByteArrayReturn : ByteArray := Id.run do
  let mut output := ByteArray.empty
  if output.isEmpty then
    output := output.push (65 : UInt8)
  else
    output := output.push (90 : UInt8)
  if output.size == 1 then
    output := output.push (66 : UInt8)
  return output

def idRunMutOptionReturn : Option UInt64 := Id.run do
  let mut found : Option UInt64 := none
  if found.isNone then
    found := some (7 : UInt64)
  if found == some (7 : UInt64) then
    found := some (9 : UInt64)
  return found

def idRunMutExceptReturn : Except UInt64 UInt64 := Id.run do
  let mut result : Except UInt64 UInt64 := Except.ok (3 : UInt64)
  match result with
  | Except.error code =>
      result := Except.error (code + 1)
  | Except.ok value =>
      if value == (3 : UInt64) then
        result := Except.ok (value + 4)
      else
        result := Except.error value
  return result

def idRunMutOptionMatch : UInt64 := Id.run do
  let mut total := (1 : UInt64)
  let found : Option UInt64 := some 4
  match found with
  | some value =>
      total := total + value
  | none =>
      total := total + 100
  return total

def idRunMutOptionIfLet : UInt64 := Id.run do
  let mut total := (3 : UInt64)
  let found : Option UInt64 := some 5
  if let some value := found then
    total := total + value
  else
    total := total + 100
  return total

def idRunMutOptionCatchAllMatch : UInt64 := Id.run do
  let mut total := (0 : UInt64)
  let found : Option UInt64 := none
  match found with
  | some value =>
      total := value
  | other =>
      match other with
      | none =>
          total := 11
      | some value =>
          total := value + 100
  return total

def idRunMutStatusMatchReturn : Status := Id.run do
  let mut status : Status := Status.ok 2
  match status with
  | .ok value =>
      status := Status.ok (value + 8)
  | .error code =>
      status := Status.error (code + 1)
  return status

def idRunMutStatusIfLet : UInt64 := Id.run do
  let mut total := (1 : UInt64)
  let status : Status := Status.ok 6
  if let Status.ok value := status then
    total := total + value
  else
    total := total + 100
  return total

def idRunMutStatusCatchAllMatch : UInt64 := Id.run do
  let mut total := (0 : UInt64)
  let status : Status := Status.error 9
  match status with
  | .ok value =>
      total := value
  | other =>
      match other with
      | .error code =>
          total := code + 20
      | .ok value =>
          total := value + 100
  return total

def idRunMutModeIfLet : UInt64 := Id.run do
  let mut total := (0 : UInt64)
  let mode : Mode := Mode.done
  if let Mode.done := mode then
    total := 7
  else
    total := 3
  return total

def idRunWhileStatusIfLetSum : UInt64 := Id.run do
  let statuses : Array Status := #[Status.ok 2, Status.error 7, Status.ok 3]
  let mut i : Nat := 0
  let mut total := (0 : UInt64)
  while i < statuses.size do
    match statuses[i]? with
    | some status =>
        if let Status.ok value := status then
          total := total + value
        else
          total := total + 10
    | none =>
        total := total + 100
    i := i + 1
  return total

def idRunMutMatchStateRecord : DigitState := Id.run do
  let mut state : DigitState := { pos := 1, sum := 5 }
  let found : Option UInt64 := some 4
  match found with
  | some value =>
      state := { pos := state.pos + 1, sum := state.sum + value }
  | none =>
      state := { state with sum := 99 }
  return state

def rejectIdRunFunctionValue : UInt64 := Id.run do
  let f := fun x : UInt64 => x + 1
  let value := (f, (1 : UInt64))
  return value.2

def idRunByteArrayForSum : UInt64 := Id.run do
  let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]
  let mut acc := (0 : UInt64)
  for byte in input do
    acc := acc + byte.toUInt64
  return acc

def idRunArrayForSum : UInt64 := Id.run do
  let values : Array UInt64 := #[1, 2, 3]
  let mut acc := (0 : UInt64)
  for value in values do
    acc := acc + value
  return acc

def idRunArrayForTwoCounters : UInt64 := Id.run do
  let values : Array UInt64 := #[1, 2, 3]
  let mut sum := (0 : UInt64)
  let mut count := (0 : UInt64)
  for value in values do
    sum := sum + value
    count := count + 1
  return sum * 10 + count

def idRunNestedArrayForSum : UInt64 := Id.run do
  let rows : Array (Array UInt64) := #[#[1, 2], #[3, 4]]
  let mut sum := (0 : UInt64)
  for row in rows do
    for value in row do
      sum := sum + value
  return sum

def idRunArrayForBreakSum : UInt64 := Id.run do
  let values : Array UInt64 := #[1, 2, 99, 3]
  let mut acc := (0 : UInt64)
  for value in values do
    if value == (99 : UInt64) then
      break
    else
      acc := acc + value
  return acc

def idRunArrayForContinueNoElse : UInt64 := Id.run do
  let values : Array UInt64 := #[1, 2, 99, 3]
  let mut acc := (0 : UInt64)
  for value in values do
    if value == (99 : UInt64) then
      continue
    acc := acc + value
  return acc

def idRunByteArrayForState : DigitState := Id.run do
  let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]
  let mut state : DigitState := { pos := 0, sum := 0 }
  for byte in input do
    state := { pos := state.pos + 1, sum := state.sum + byte.toUInt64 }
  return state

def idRunByteArrayForBreakSum : UInt64 := Id.run do
  let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8), (99 : UInt8), (3 : UInt8)]
  let mut acc := (0 : UInt64)
  for byte in input do
    if byte == (99 : UInt8) then
      break
    else
      acc := acc + byte.toUInt64
  return acc

def idRunByteArrayForContinueNoElse : UInt64 := Id.run do
  let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8), (99 : UInt8), (3 : UInt8)]
  let mut acc := (0 : UInt64)
  for byte in input do
    if byte == (99 : UInt8) then
      continue
    acc := acc + byte.toUInt64
  return acc

def idRunByteArrayForOutput : ByteArray := Id.run do
  let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8)]
  let mut output := ByteArray.empty
  for byte in input do
    output := output.push byte
  return output

def idRunByteArrayForOutputBreak : ByteArray := Id.run do
  let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8), (99 : UInt8), (3 : UInt8)]
  let mut output := ByteArray.empty
  for byte in input do
    if byte == (99 : UInt8) then
      break
    output := output.push byte
  return output

def idRunByteArrayForOutputContinue : ByteArray := Id.run do
  let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8), (99 : UInt8), (3 : UInt8)]
  let mut output := ByteArray.empty
  for byte in input do
    if byte == (99 : UInt8) then
      continue
    output := output.push byte
  return output

def idRunByteArrayForOutputReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output := Id.run do
    let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]
    let mut output := ByteArray.empty
    for byte in input do
      output := output.push byte
    return output
  let releasesAfterLoop := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterLoop := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterLoop * 100 + freesAfterLoop

def idRunArrayForStatus : Status := Id.run do
  let values : Array UInt64 := #[1, 2, 3]
  let mut state : Status := .ok 0
  for value in values do
    state :=
      match state with
      | .ok sum =>
          if value == (2 : UInt64) then
            .error value
          else
            .ok (sum + value)
      | .error code => .error code
  return state

def idRunArrayForStatusScore : UInt64 :=
  match idRunArrayForStatus with
  | .ok sum => sum
  | .error code => code + 100

def idRunRangeForCount : UInt64 := Id.run do
  let mut acc := (0 : UInt64)
  for _i in [0:3] do
    acc := acc + 1
  return acc

def idRunRangeForStepSum : UInt64 := Id.run do
  let mut acc := (0 : UInt64)
  for i in [1:7:2] do
    acc := acc + i.toUInt64
  return acc

def idRunRangeForState : DigitState := Id.run do
  let mut state : DigitState := { pos := 0, sum := 0 }
  for i in [2:5] do
    state := { pos := state.pos + 1, sum := state.sum + i.toUInt64 }
  return state

def idRunRangeForBreakSum : UInt64 := Id.run do
  let mut acc := (0 : UInt64)
  for i in [0:10] do
    if i == (4 : Nat) then
      break
    else
      acc := acc + i.toUInt64
  return acc

def idRunRangeForBreakNoElse : UInt64 := Id.run do
  let mut acc := (0 : UInt64)
  for i in [0:6] do
    if i == (3 : Nat) then
      break
    acc := acc + i.toUInt64
  return acc

def idRunRangeForContinueNoElse : UInt64 := Id.run do
  let mut acc := (0 : UInt64)
  for i in [0:6] do
    if i == (3 : Nat) then
      continue
    acc := acc + i.toUInt64
  return acc

def idRunRangeForByteArrayOutput : ByteArray := Id.run do
  let mut output := ByteArray.empty
  for _i in [0:2] do
    output := output.push (1 : UInt8)
  return output

def idRunRangeForByteArrayOutputReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output := Id.run do
    let mut output := ByteArray.empty
    for _i in [0:3] do
      output := output.push (1 : UInt8)
    return output
  let releasesAfterLoop := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterLoop := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterLoop * 100 + freesAfterLoop

def idRunRangeForBreakState : DigitState := Id.run do
  let mut state : DigitState := { pos := 0, sum := 0 }
  for i in [1:6] do
    if i == (4 : Nat) then
      break
    else
      state := { pos := state.pos + 1, sum := state.sum + i.toUInt64 }
  return state

def idRunRangeForContinueState : DigitState := Id.run do
  let mut state : DigitState := { pos := 0, sum := 0 }
  for i in [1:6] do
    if i == (4 : Nat) then
      continue
    state := { pos := state.pos + 1, sum := state.sum + i.toUInt64 }
  return state

def exceptForArraySum : Except UInt64 UInt64 := do
  let values : Array UInt64 := #[1, 2, 3]
  let mut acc := (0 : UInt64)
  for value in values do
    acc := acc + value
  return acc

def exceptForArrayErrorSkipsRestTrap : Except UInt64 UInt64 := do
  let values : Array UInt64 := #[1, 2, 3]
  let mut acc := (0 : UInt64)
  for value in values do
    if value == (2 : UInt64) then
      Except.error (acc + 20)
    else if value == (3 : UInt64) then
      acc := (Array.replicate 0 (0 : UInt64))[0]!
    else
      acc := acc + value
  return acc

def optionForByteArraySum : Option UInt64 := do
  let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]
  let mut acc := (0 : UInt64)
  for byte in input do
    acc := acc + byte.toUInt64
  return acc

def optionForByteArrayNoneSkipsRestTrap : Option UInt64 := do
  let input := ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]
  let mut acc := (0 : UInt64)
  for byte in input do
    if byte == (2 : UInt8) then
      none
    else if byte == (3 : UInt8) then
      acc := (Array.replicate 0 (0 : UInt64))[0]!
    else
      acc := acc + byte.toUInt64
  return acc

def exceptForRangeBreakSum : Except UInt64 UInt64 := do
  let mut acc := (0 : UInt64)
  for i in [0:6] do
    if i == (4 : Nat) then
      break
    acc := acc + i.toUInt64
  return acc

def optionForArrayContinueSum : Option UInt64 := do
  let values : Array UInt64 := #[1, 2, 3]
  let mut acc := (0 : UInt64)
  for value in values do
    if value == (2 : UInt64) then
      continue
    acc := acc + value
  return acc

def optionWhileSum : Option UInt64 := do
  let mut i := (0 : UInt64)
  let mut acc := (0 : UInt64)
  while i < (3 : UInt64) do
    acc := acc + i
    i := i + 1
  return acc

def optionForByteArrayOutput : Option ByteArray := do
  let input := ByteArray.mk #[(65 : UInt8), (66 : UInt8), (67 : UInt8)]
  let mut output := ByteArray.empty
  for byte in input do
    output := output.push byte
  return output

def optionForByteArrayOutputNoneSkipsRestTrap : Option ByteArray := do
  let input := ByteArray.mk #[(65 : UInt8), (99 : UInt8), (66 : UInt8)]
  let mut output := ByteArray.empty
  for byte in input do
    if byte == (99 : UInt8) then
      none
    else if byte == (66 : UInt8) then
      output := output.push ((Array.replicate 0 (0 : UInt8))[0]!)
    else
      output := output.push byte
  return output

def exceptForByteArrayOutput : Except UInt64 ByteArray := do
  let input := ByteArray.mk #[(65 : UInt8), (66 : UInt8), (67 : UInt8)]
  let mut output := ByteArray.empty
  for byte in input do
    output := output.push byte
  return output

def exceptForByteArrayOutputErrorSkipsRestTrap : Except UInt64 ByteArray := do
  let input := ByteArray.mk #[(65 : UInt8), (99 : UInt8), (66 : UInt8)]
  let mut output := ByteArray.empty
  for byte in input do
    if byte == (99 : UInt8) then
      Except.error (output.size.toUInt64 + 20)
    else if byte == (66 : UInt8) then
      output := output.push ((Array.replicate 0 (0 : UInt8))[0]!)
    else
      output := output.push byte
  return output

def optionForByteArrayState : Option ByteOutputState := do
  let input := ByteArray.mk #[(65 : UInt8), (66 : UInt8), (67 : UInt8)]
  let mut state : ByteOutputState := { count := 0, bytes := ByteArray.empty }
  for byte in input do
    state := { count := state.count + 1, bytes := state.bytes.push byte }
  return state

def optionForByteArrayOutputReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let result : Option ByteArray := do
    let input := ByteArray.mk #[(65 : UInt8), (66 : UInt8), (67 : UInt8)]
    let mut output := ByteArray.empty
    for byte in input do
      output := output.push byte
    return output
  let releasesAfterLoop := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterLoop := LeanExe.Runtime.freeCount - before
  match result with
  | some _ => 10000 + releasesAfterLoop * 100 + freesAfterLoop
  | none => releasesAfterLoop * 100 + freesAfterLoop

def exceptForByteArrayOutputReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let result : Except UInt64 ByteArray := do
    let input := ByteArray.mk #[(65 : UInt8), (66 : UInt8), (67 : UInt8)]
    let mut output := ByteArray.empty
    for byte in input do
      output := output.push byte
    return output
  let releasesAfterLoop := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterLoop := LeanExe.Runtime.freeCount - before
  match result with
  | Except.ok _ => 10000 + releasesAfterLoop * 100 + freesAfterLoop
  | Except.error code => code * 1000000 + releasesAfterLoop * 100 + freesAfterLoop

def optionForByteArrayStateReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let result : Option ByteOutputState := do
    let input := ByteArray.mk #[(65 : UInt8), (66 : UInt8), (67 : UInt8)]
    let mut state : ByteOutputState := { count := 0, bytes := ByteArray.empty }
    for byte in input do
      state := { count := state.count + 1, bytes := state.bytes.push byte }
    return state
  let releasesAfterLoop := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterLoop := LeanExe.Runtime.freeCount - before
  match result with
  | some state => state.count * 10000 + releasesAfterLoop * 100 + freesAfterLoop
  | none => releasesAfterLoop * 100 + freesAfterLoop

def idRunWhileSum : UInt64 := Id.run do
  let mut i := (0 : UInt64)
  let mut sum := (0 : UInt64)
  while i < 5 do
    sum := sum + i
    i := i + 1
  return sum

def idRunWhileBreakContinue : UInt64 := Id.run do
  let mut i := (0 : UInt64)
  let mut sum := (0 : UInt64)
  while i < 8 do
    i := i + 1
    if i == (3 : UInt64) then
      continue
    if i == (6 : UInt64) then
      break
    sum := sum + i
  return sum

def idRunWhileState : DigitState := Id.run do
  let mut state : DigitState := { pos := 0, sum := 0 }
  while state.pos < 4 do
    state := { pos := state.pos + 1, sum := state.sum + state.pos.toUInt64 }
  return state

def idRunNestedWhileSum : UInt64 := Id.run do
  let mut outer := (0 : UInt64)
  let mut sum := (0 : UInt64)
  while outer < 3 do
    let mut inner := (0 : UInt64)
    while inner < 2 do
      sum := sum + outer * (10 : UInt64) + inner
      inner := inner + (1 : UInt64)
    outer := outer + (1 : UInt64)
  return sum

def idRunWhileByteArrayOutput : ByteArray := Id.run do
  let mut i := (0 : UInt64)
  let mut output := ByteArray.empty
  while i < 3 do
    output := output.push (1 : UInt8)
    i := i + (1 : UInt64)
  return output

def idRunWhileDigitScanner : DigitState := Id.run do
  let input := ByteArray.mk #[(49 : UInt8), (50 : UInt8), (65 : UInt8), (51 : UInt8)]
  let mut pos : Nat := 0
  let mut sum := (0 : UInt64)
  let mut ok := true
  while pos < input.size do
    let byte := input[pos]!
    if isAsciiDigitByte byte then
      sum := sum + (byte.toUInt64 - 48)
      pos := pos + 1
    else
      ok := false
      break
  if ok then
    return { pos := pos, sum := sum }
  else
    return { pos := pos, sum := sum + 100 }

def idRunWhileDigitOutput : ByteArray := Id.run do
  let input := ByteArray.mk #[(49 : UInt8), (50 : UInt8), (51 : UInt8)]
  let mut pos : Nat := 0
  let mut output := ByteArray.empty
  while pos < input.size do
    let byte := input[pos]!
    if isAsciiDigitByte byte then
      output := output.push (byte - 48)
      pos := pos + 1
    else
      break
  return output

def idRunWhileParserExcept : Except UInt64 DigitState := Id.run do
  let input := ByteArray.mk #[(49 : UInt8), (50 : UInt8), (65 : UInt8)]
  let mut pos : Nat := 0
  let mut sum := (0 : UInt64)
  let mut result : Except UInt64 DigitState := Except.ok { pos := 0, sum := 0 }
  while pos < input.size do
    let byte := input[pos]!
    if isAsciiDigitByte byte then
      sum := sum + (byte.toUInt64 - 48)
      pos := pos + 1
      result := Except.ok { pos := pos, sum := sum }
    else
      result := Except.error pos.toUInt64
      break
  return result

def idRunWhileArrayUpdateSum : UInt64 := Id.run do
  let mut values : Array UInt64 := #[1, 2, 3]
  let mut i : Nat := 0
  while i < values.size do
    let value := values[i]!
    values := values.set! i (value + i.toUInt64)
    i := i + 1
  let mut sum := (0 : UInt64)
  for value in values do
    sum := sum + value
  return sum

def idRunWhileParserBufferState : ParserBufferState := Id.run do
  let input := ByteArray.mk #[(49 : UInt8), (50 : UInt8), (65 : UInt8), (51 : UInt8)]
  let mut state : ParserBufferState := { pos := 0, out := ByteArray.empty, ok := true }
  while state.pos < input.size do
    let byte := input[state.pos]!
    if isAsciiDigitByte byte then
      state := { pos := state.pos + 1, out := state.out.push (byte - 48), ok := state.ok }
    else
      state := { state with ok := false }
      break
  return state

def idRunWhileArrayBuilderState : ArrayBuilderState := Id.run do
  let mut state : ArrayBuilderState := { values := #[1, 2, 3], count := 0 }
  let mut i : Nat := 0
  while i < state.values.size do
    let value := state.values[i]!
    state := { values := state.values.set! i (value + state.count), count := state.count + 1 }
    i := i + 1
  return state

def digitByteOrError (byte : UInt8) : Except UInt64 UInt8 :=
  if isAsciiDigitByte byte then
    Except.ok (byte - 48)
  else
    Except.error byte.toUInt64

def scanDigitsExceptLoop (input : ByteArray) : Except UInt64 DigitState := Id.run do
  let mut pos : Nat := 0
  let mut sum := (0 : UInt64)
  let mut result : Except UInt64 DigitState := Except.ok { pos := 0, sum := 0 }
  while pos < input.size do
    let byte := input[pos]!
    if isAsciiDigitByte byte then
      sum := sum + (byte.toUInt64 - 48)
      pos := pos + 1
      result := Except.ok { pos := pos, sum := sum }
    else
      result := Except.error pos.toUInt64
      break
  return result

def exceptDoStateFromLoop : Except UInt64 DigitState := do
  let input ← Except.ok (ByteArray.mk #[(49 : UInt8), (50 : UInt8), (51 : UInt8)])
  let state ← scanDigitsExceptLoop input
  pure { pos := state.pos + 1, sum := state.sum + 10 }

def exceptDoLoopErrorSkipsRestTrap : UInt64 :=
  match (do
      let input ← Except.ok (ByteArray.mk #[(49 : UInt8), (65 : UInt8)])
      let _state ← scanDigitsExceptLoop input
      let later ← digitByteOrError ((Array.replicate 0 (0 : UInt8))[0]!)
      pure later : Except UInt64 UInt8) with
  | Except.error code => code
  | Except.ok value => value.toUInt64

def exceptDoByteArrayFromValidation : Except UInt64 ByteArray := do
  let first ← digitByteOrError (52 : UInt8)
  let second ← digitByteOrError (53 : UInt8)
  let output := Id.run do
    let mut out := ByteArray.empty
    out := out.push first
    out := out.push second
    return out
  pure output

def exceptDoStatusFromLoop : Except UInt64 Status := do
  let state ← scanDigitsExceptLoop (ByteArray.mk #[(50 : UInt8), (51 : UInt8)])
  pure (Status.ok (state.sum + state.pos.toUInt64))

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

def arrayFoldSum : Nat :=
  (#[1, 2, 3] : Array UInt64).foldl
    (fun acc value => acc + value.toNat)
    0

def arrayFoldWindow : Nat :=
  (#[1, 2, 3, 4] : Array UInt64).foldl
    (fun acc value => acc * 10 + value.toNat)
    0
    1
    3

def arrayFoldEmptySkipsFunctionTrap : Nat :=
  (#[] : Array UInt64).foldl
    (fun acc _value => acc + ((Array.replicate 0 (0 : UInt64))[0]!).toNat)
    7

def arrayFoldrDigits : UInt64 :=
  (#[1, 2, 3] : Array UInt64).foldr
    (fun value acc => acc * 10 + value)
    0

def arrayFoldrWindow : UInt64 :=
  (#[1, 2, 3, 4] : Array UInt64).foldr
    (fun value acc => acc * 10 + value)
    0
    3
    1

def arrayFoldrStartClamps : UInt64 :=
  (#[1, 2, 3] : Array UInt64).foldr
    (fun value acc => acc * 10 + value)
    0
    10
    0

def arrayFoldrEmptySkipsFunctionTrap : UInt64 :=
  (#[] : Array UInt64).foldr
    (fun _value acc => acc + (Array.replicate 0 (0 : UInt64))[0]!)
    7

def arrayFoldrStructAccumulator : UInt64 :=
  let result :=
    (#[1, 2, 3] : Array UInt64).foldr
      (fun value acc => { count := acc.count + 1, sum := acc.sum * 10 + value })
      ({ count := 0, sum := 0 } : CountSum)
  result.count * (1000 : UInt64) + result.sum

def arrayFoldrByteArrayAccumulator : ByteArray :=
  (#[65, 66, 67] : Array UInt64).foldr
    (fun value acc => acc.push (UInt64.toUInt8 value))
    ByteArray.empty

def arrayFoldrByteArrayAccumulatorReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output :=
    (#[65, 66, 67] : Array UInt64).foldr
      (fun value acc => acc.push (UInt64.toUInt8 value))
      ByteArray.empty
  let releasesAfterFold := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterFold := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterFold * 100 + freesAfterFold

def arrayFoldStructAccumulator : UInt64 :=
  let result :=
    (#[1, 2, 3] : Array UInt64).foldl
      (fun acc value => { count := acc.count + 1, sum := acc.sum + value })
      ({ count := 0, sum := 0 } : CountSum)
  result.count * (10 : UInt64) + result.sum

def arrayFoldProductAccumulator : UInt64 :=
  let result :=
    (#[2, 3, 4] : Array UInt64).foldl
      (fun acc value => (acc.1 + 1, acc.2 + value))
      ((0 : UInt64), (0 : UInt64))
  result.1 * (10 : UInt64) + result.2

def arrayFoldStatusAccumulator : UInt64 :=
  let result :=
    (#[1, 2, 3] : Array UInt64).foldl
      (fun acc value =>
        match acc with
        | Status.ok sum => Status.ok (sum + value)
        | Status.error code => Status.error code)
      (Status.ok 0)
  match result with
  | Status.ok sum => sum
  | Status.error code => code + 100

def arrayFoldArrayAccumulator : UInt64 :=
  let result :=
    (#[1, 2, 3] : Array UInt64).foldl
      (fun acc value => acc.push (value + 10))
      (#[] : Array UInt64)
  if result.size == 3 then
    result[0]! * (100 : UInt64) + result[2]!
  else
    0

def arrayFoldByteArrayAccumulator : ByteArray :=
  (#[65, 66] : Array UInt64).foldl
    (fun acc value => acc.push (UInt64.toUInt8 value))
    ByteArray.empty

def arrayFoldByteArrayAccumulatorReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output :=
    (#[65, 66, 67] : Array UInt64).foldl
      (fun acc value => acc.push (UInt64.toUInt8 value))
      ByteArray.empty
  let releasesAfterFold := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterFold := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterFold * 100 + freesAfterFold

def arrayFoldInputByteArrayAccumulatorReleaseStats (values : Array UInt64) : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output :=
    values.foldl
      (fun acc value => acc.push (UInt64.toUInt8 value))
      ByteArray.empty
  let releasesAfterFold := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterFold := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterFold * 100 + freesAfterFold

def arrayFoldByteOutputState : ByteOutputState :=
  (#[65, 66, 67] : Array UInt64).foldl
    (fun acc value =>
      { count := acc.count + 1, bytes := acc.bytes.push (UInt64.toUInt8 value) })
    ({ count := 0, bytes := ByteArray.empty } : ByteOutputState)

def arrayFoldMExceptSuccess : Except UInt64 UInt64 :=
  (#[1, 2, 3] : Array UInt64).foldlM (m := Except UInt64)
    (fun (acc : UInt64) (value : UInt64) => Except.ok (acc + value))
    0

def arrayFoldMExceptErrorSkipsRestTrap : Except UInt64 UInt64 :=
  (#[1, 2, 3] : Array UInt64).foldlM (m := Except UInt64)
    (fun (acc : UInt64) (value : UInt64) =>
      if value == 2 then
        Except.error (acc + 20)
      else if value == 3 then
        Except.ok ((Array.replicate 0 (0 : UInt64))[0]!)
      else
        Except.ok (acc + value))
    0

def arrayFoldMOptionSuccess : Option UInt64 :=
  (#[1, 2, 3] : Array UInt64).foldlM (m := Option)
    (fun (acc : UInt64) (value : UInt64) => some (acc + value))
    0

def arrayFoldMOptionNoneSkipsRestTrap : Option UInt64 :=
  (#[1, 2, 3] : Array UInt64).foldlM (m := Option)
    (fun (acc : UInt64) (value : UInt64) =>
      if value == 2 then
        none
      else if value == 3 then
        some ((Array.replicate 0 (0 : UInt64))[0]!)
      else
        some (acc + value))
    0

def arrayAttachFoldMExcept : Except UInt64 UInt64 :=
  (#[1, 2, 3] : Array UInt64).attach.foldlM (m := Except UInt64)
    (fun (acc : UInt64) item =>
      match item with
      | ⟨value, _hmem⟩ => Except.ok (acc + value))
    0

def arrayFindIdxSome : Option Nat :=
  (#[1, 2, 3] : Array UInt64).findIdx? (fun value => value == 2)

def arrayFindIdxNone : Option Nat :=
  (#[1, 2, 3] : Array UInt64).findIdx? (fun value => value == 9)

def arrayFindIdxStructure : Option Nat :=
  (#[{ x := 1, y := 2 }, { x := 3, y := 4 }] : Array Point).findIdx?
    (fun point => point.y == 4)

def arrayFindIdxStatus : Option Nat :=
  (#[Status.error 5, Status.ok 7] : Array Status).findIdx?
    (fun status =>
      match status with
      | Status.ok value => value == 7
      | Status.error _ => false)

def arrayFindIdxEmptySkipsPredicateTrap : Option Nat :=
  (#[] : Array UInt64).findIdx?
    (fun _value => (Array.replicate 0 false)[0]!)

def matchedScalarScrutinee (flag : UInt64) : Option UInt64 :=
  if flag == 0 then some 4 else none

def matchedScalarScore (flag : UInt64) : UInt64 :=
  let point : Point :=
    match matchedScalarScrutinee flag with
    | some value => { x := value, y := value + 1 }
    | none => { x := 7, y := 8 }
  point.x * 10 + point.y

def matchedScalarSkipsUnusedBranchField (flag : UInt64) : UInt64 :=
  let point : Point :=
    match matchedScalarScrutinee flag with
    | some value =>
        { x := value, y := (Array.replicate 0 (0 : UInt64))[0]! }
    | none =>
        { x := 7, y := (Array.replicate 0 (0 : UInt64))[0]! }
  point.x

def matchedFindIdxPoint (needle : UInt64) : Point :=
  match (#[1, 2, 3] : Array UInt64).findIdx? (fun value => value == needle) with
  | some index => { x := 1, y := UInt64.ofNat index }
  | none => { x := 0, y := 9 }

def matchedFindIdxArray (needle : UInt64) : Array UInt64 :=
  match (#[1, 2, 3] : Array UInt64).findIdx? (fun value => value == needle) with
  | some index => #[UInt64.ofNat index, needle]
  | none => #[99]

def matchedFindIdxArrayReleaseStats (needle : UInt64) : UInt64 :=
  let allocsBefore := LeanExe.Runtime.allocCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let freesBefore := LeanExe.Runtime.freeCount
  let output := matchedFindIdxArray needle
  let size := output.size.toUInt64
  let freesAfter := LeanExe.Runtime.release output
  size * 1000000 +
    (LeanExe.Runtime.allocCount - allocsBefore) * 10000 +
    (LeanExe.Runtime.releaseCount - releasesBefore) * 100 +
    (freesAfter - freesBefore)

def matchedFindIdxPredicateTrap : UInt64 :=
  match (#[1] : Array UInt64).findIdx?
      (fun _value => (Array.replicate 0 false)[0]!) with
  | some index => UInt64.ofNat index
  | none => 9

def arrayFindSome : Option UInt64 :=
  (#[1, 2, 3] : Array UInt64).find? (fun value => value == 2)

def arrayFindNone : Option UInt64 :=
  (#[1, 2, 3] : Array UInt64).find? (fun value => value == 9)

def arrayFindStructure : Option Point :=
  (#[{ x := 1, y := 2 }, { x := 3, y := 4 }] : Array Point).find?
    (fun point => point.y == 4)

def arrayFindStatus : Option Status :=
  (#[Status.error 5, Status.ok 7] : Array Status).find?
    (fun status =>
      match status with
      | Status.ok value => value == 7
      | Status.error _ => false)

def arrayFindEmptySkipsPredicateTrap : Option UInt64 :=
  (#[] : Array UInt64).find?
    (fun _value => (Array.replicate 0 false)[0]!)

def arrayAnySome : Bool :=
  (#[1, 2, 3] : Array UInt64).any (fun value => value == 2)

def arrayAnyWindowFalse : Bool :=
  (#[1, 2, 3] : Array UInt64).any (fun value => value == 1) 1 3

def arrayAnyEmptySkipsPredicateTrap : Bool :=
  (#[] : Array UInt64).any
    (fun _value => (Array.replicate 0 false)[0]!)

def arrayAllScalars : Bool :=
  (#[2, 4, 6] : Array UInt64).all (fun value => value % 2 == 0)

def arrayAllWindowTrue : Bool :=
  (#[1, 2, 4] : Array UInt64).all (fun value => value % 2 == 0) 1 3

def arrayAllStructure : Bool :=
  (#[{ x := 1, y := 2 }, { x := 3, y := 4 }] : Array Point).all
    (fun point => point.x < point.y)

def arrayAnyStatus : Bool :=
  (#[Status.error 5, Status.ok 7] : Array Status).any
    (fun status =>
      match status with
      | Status.ok value => value == 7
      | Status.error _ => false)

def arrayAllEmptySkipsPredicateTrap : Bool :=
  (#[] : Array UInt64).all
    (fun _value => (Array.replicate 0 false)[0]!)

def arrayFilterScalarsRead : UInt64 :=
  let b := (#[1, 5, 7, 2, 7] : Array UInt64).filter (fun value => value > 2)
  if b.size == 3 then
    b[0]! * (100 : UInt64) + b[1]! * (10 : UInt64) + b[2]!
  else
    0

def arrayFilterWindowRead : UInt64 :=
  let b := (#[1, 2, 5, 7] : Array UInt64).filter (fun _value => true) 1 3
  if b.size == 2 then
    b[0]! * (10 : UInt64) + b[1]!
  else
    0

def arrayFilterNoneSize : Nat :=
  ((#[1, 2, 3] : Array UInt64).filter (fun value => value == 9)).size

def arrayFilterStructureRead : UInt64 :=
  let b :=
    (#[{ x := 1, y := 2 }, { x := 3, y := 4 }, { x := 5, y := 6 }] : Array Point).filter
      (fun point => point.y > 2)
  if b.size == 2 then
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

def arrayFilterStatusRead : UInt64 :=
  let b :=
    (#[Status.error 5, Status.ok 7, Status.ok 2] : Array Status).filter
      (fun status =>
        match status with
        | Status.ok _ => true
        | Status.error _ => false)
  if b.size == 2 then
    match b[0]? with
    | none => 0
    | some first =>
        match b[1]? with
        | none => 0
        | some second => statusLeftScore first * (10 : UInt64) + statusLeftScore second
  else
    0

def arrayFilterEmptySkipsPredicateTrap : Nat :=
  ((#[] : Array UInt64).filter
    (fun _value => (Array.replicate 0 false)[0]!)).size

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

def arrayStructurePushHelperRead : UInt64 :=
  let a := (#[] : Array Point).push (makePointHelper 7)
  match a[0]? with
  | some point => structureParam point
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

def trapPointHelper : Point :=
  { x := (Array.replicate 0 (0 : UInt64)).back!, y := 9 }

def arrayStructureInsertSkipsHelperValueTrap : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point)]
  let b := a.insertIdxIfInBounds 5 trapPointHelper
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

def arrayStructureSetIfInBoundsSkipsHelperValueTrap : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point)]
  let b := a.setIfInBounds 5 trapPointHelper
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

def arrayStructureReplicateHelperRead : UInt64 :=
  let a := Array.replicate 2 (makePointHelper 7)
  if a.size == 2 then
    match a[0]? with
    | none => 0
    | some first =>
        match a[1]? with
        | none => 0
        | some last =>
            first.x * (1000 : UInt64) + first.y * (100 : UInt64) +
              last.x * (10 : UInt64) + last.y
  else
    0

def arrayStructureMapRead : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point)]
  let b := a.map (fun point => ({ x := point.x + point.y, y := point.y + 1 } : Point))
  match b[0]? with
  | none => 0
  | some first =>
      match b[1]? with
      | none => 0
      | some second =>
          first.x * (1000 : UInt64) + first.y * (100 : UInt64) +
            second.x * (10 : UInt64) + second.y

def arrayStructureMapEmptySkipsFunctionTrap : Nat :=
  ((#[] : Array Point).map
    (fun _point => ({ x := (Array.replicate 0 (0 : UInt64)).back!, y := 9 } : Point))).size

def arrayStructureMapEmptySkipsHelperTrap : Nat :=
  ((#[] : Array Point).map (fun _point => trapPointHelper)).size

def arrayStructureFoldRead : UInt64 :=
  let a : Array Point := #[({ x := 1, y := 2 } : Point), ({ x := 3, y := 4 } : Point)]
  a.foldl
    (fun acc point => acc * (100 : UInt64) + point.x * (10 : UInt64) + point.y)
    0

def arrayStructureSafeGet : UInt64 :=
  match (#[({ x := 4, y := 5 } : Point)] : Array Point)[0]? with
  | none => 99
  | some point => point.x * (10 : UInt64) + point.y

def arrayStructureSafeNoneSkipsPayloadTrap : UInt64 :=
  match (#[] : Array Point)[0]? with
  | none => 7
  | some point => point.x + point.y

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

def arrayStatusMapMatch : UInt64 :=
  let a : Array Status := #[Status.ok 5, Status.error 7]
  let b :=
    a.map (fun status =>
      match status with
      | Status.ok value => Status.error (value + 1)
      | Status.error code => Status.ok (code + 1))
  let left := Option.elim b[0]? 0 (fun status => statusLeftScore status)
  let right := Option.elim b[1]? 0 (fun status => statusRightScore status)
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

def nestedArrayLiteralRead : UInt64 :=
  let rows : Array (Array UInt64) := #[#[1, 2], #[3, 4, 5]]
  let first := rows[0]!
  let second := rows[1]!
  first[1]! * (100 : UInt64) + second[2]! * (10 : UInt64) +
    first.size.toUInt64 + second.size.toUInt64

def nestedArraySetPushRead : UInt64 :=
  let rows : Array (Array UInt64) := #[#[1], #[2, 3]]
  let updated := rows.set! 0 ((rows[0]!).push 9)
  let extended := updated.push #[4, 5, 6]
  let first := extended[0]!
  let third := extended[2]!
  first[1]! * (100 : UInt64) + third.size.toUInt64 * (10 : UInt64) +
    extended.size.toUInt64

def nestedArrayFoldSizes : UInt64 :=
  let rows : Array (Array UInt64) := #[#[1, 2], #[], #[3, 4, 5]]
  rows.foldl (fun acc row => acc + row.size.toUInt64) 0

def nestedArrayMapPushRead : UInt64 :=
  let rows : Array (Array UInt64) := #[#[1], #[2, 3]]
  let grown := rows.map (fun row => row.push 9)
  let first := grown[0]!
  let second := grown[1]!
  first.size.toUInt64 * (100 : UInt64) + first[1]! * (10 : UInt64) + second[2]!

def nestedArrayFindRead : UInt64 :=
  let rows : Array (Array UInt64) := #[#[], #[4, 5], #[6]]
  match rows.find? (fun row => row.size == 2) with
  | some row => row[1]!
  | none => 0

def arrayBoxElementRead : UInt64 :=
  let boxes : Array ArrayBox :=
    #[{ values := #[1, 2], count := 2 }, { values := #[3], count := 1 }]
  match boxes[0]? with
  | none => 0
  | some first =>
      match boxes[1]? with
      | none => 0
      | some second =>
          first.values[1]! * (100 : UInt64) + first.count * (10 : UInt64) +
            second.values[0]!

def arrayProductElementRead : UInt64 :=
  let pairs : Array (UInt64 × UInt64) :=
    #[((1 : UInt64), (2 : UInt64)), ((3 : UInt64), (4 : UInt64))]
  let swapped := pairs.map (fun pair => (pair.2, pair.1))
  let pair := swapped[1]!
  pair.1 * (10 : UInt64) + pair.2

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

def recStepLetFuel : Nat → UInt64 → UInt64
  | 0, acc => acc
  | fuel + 1, acc =>
      let next := acc + 1
      recStepLetFuel fuel next

def recStepLetDemo : UInt64 :=
  recStepLetFuel 5 0

def recStepLetExitFuel : Nat → UInt64 → UInt64
  | 0, acc => acc
  | fuel + 1, acc =>
      let next := acc + 1
      if next == 3 then
        next + 10
      else
        recStepLetExitFuel fuel next

def recStepLetExitDemo : UInt64 :=
  recStepLetExitFuel 10 0

def recStepUnusedLetSkipsTrapFuel : Nat → UInt64 → UInt64
  | 0, acc => acc
  | fuel + 1, acc =>
      let _unused := (Array.replicate 0 (0 : UInt64)).back!
      recStepUnusedLetSkipsTrapFuel fuel (acc + 1)

def recStepUnusedLetSkipsTrap : UInt64 :=
  recStepUnusedLetSkipsTrapFuel 3 0

def recPointFuel : Nat → UInt64 → Point
  | 0, value => { x := value, y := value + 1 }
  | fuel + 1, value => recPointFuel fuel (value + 1)

def recPointFuelCallRead (fuel : Nat) (value : UInt64) : UInt64 :=
  let point := recPointFuel fuel value
  point.x * 10 + point.y

def recStatusExitFuel : Nat → UInt64 → Status
  | 0, value => Status.ok value
  | fuel + 1, value =>
      if value == 3 then
        Status.error value
      else
        recStatusExitFuel fuel (value + 1)

def recPointCarryFuel : Nat → Point → Point
  | 0, point => point
  | fuel + 1, point =>
      recPointCarryFuel fuel { x := point.x + 1, y := point.y + 2 }

def bumpStatus (status : Status) : Status :=
  match status with
  | Status.ok value => Status.ok (value + 1)
  | Status.error code => Status.error (code + 1)

def recStatusCarryFuel : Nat → Status → UInt64
  | 0, status => statusLeftScore status
  | fuel + 1, status => recStatusCarryFuel fuel (bumpStatus status)

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

def optionDoSome : UInt64 :=
  match (do
      let first <- (some (5 : UInt64) : Option UInt64)
      let second <- some (first + 1)
      pure (second + 1) : Option UInt64) with
  | none => 0
  | some value => value

def optionDoNoneSkipsRestTrap : UInt64 :=
  match (do
      let _first <- (none : Option UInt64)
      let second <- some ((Array.replicate 0 (0 : UInt64)).back!)
      pure second : Option UInt64) with
  | none => 7
  | some value => value

def optionFunctorMapSome : UInt64 :=
  match (Functor.map (fun value : UInt64 => value + 1)
      (some (5 : UInt64)) : Option UInt64) with
  | none => 0
  | some value => value

def optionFunctorMapNoneSkipsFunctionTrap : UInt64 :=
  match (Functor.map (fun _value : UInt64 => (Array.replicate 0 (0 : UInt64)).back!)
      (none : Option UInt64) : Option UInt64) with
  | none => 7
  | some value => value

def exceptDoOk : UInt64 :=
  match (do
      let first <- (Except.ok (5 : UInt64) : Except UInt64 UInt64)
      let second <- exceptIncrementHelper first
      pure (second + 1) : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok value => value

def exceptDoErrorSkipsRestTrap : UInt64 :=
  match (do
      let _first <- (Except.error (7 : UInt64) : Except UInt64 UInt64)
      let second <- Except.ok ((Array.replicate 0 (0 : UInt64)).back!)
      pure second : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok value => value

def exceptFunctorMapOk : UInt64 :=
  match (Functor.map (fun value : UInt64 => value + 1)
      (Except.ok (5 : UInt64) : Except UInt64 UInt64) : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok value => value

def exceptFunctorMapErrorSkipsFunctionTrap : UInt64 :=
  match (Functor.map (fun _value : UInt64 => (Array.replicate 0 (0 : UInt64)).back!)
      (Except.error (7 : UInt64) : Except UInt64 UInt64) : Except UInt64 UInt64) with
  | Except.error code => code
  | Except.ok value => value

def byteArrayReturnABC : ByteArray :=
  ((ByteArray.empty.push (65 : UInt8)).push (66 : UInt8)).push (67 : UInt8)

def byteArrayPushSize : Nat :=
  byteArrayReturnABC.size

def byteArrayPushSizeForcesValueTrap : Nat :=
  (ByteArray.empty.push ((Array.replicate 0 (0 : UInt8))[0]!)).size

def byteArrayAppendReturn : ByteArray :=
  (ByteArray.empty.push (65 : UInt8)).append
    ((ByteArray.empty.push (66 : UInt8)).push (67 : UInt8))

def byteArrayAppendSize : Nat :=
  byteArrayAppendReturn.size

def byteArrayAppendSizeForcesRightTrap : Nat :=
  ByteArray.empty.append
    (ByteArray.empty.push ((Array.replicate 0 (0 : UInt8))[0]!))
    |>.size

def byteArraySetReturn : ByteArray :=
  let bytes := byteArrayReturnABC
  if h : 1 < bytes.size then
    bytes.set 1 (90 : UInt8) h
  else
    bytes

def byteArraySetSize : Nat :=
  byteArraySetReturn.size

def byteArraySetSizeForcesValueTrap : Nat :=
  let bytes := ByteArray.empty.push (1 : UInt8)
  if h : 0 < bytes.size then
    (bytes.set 0 ((Array.replicate 0 (0 : UInt8))[0]!) h).size
  else
    0

def byteArraySetBangReturn : ByteArray :=
  byteArrayReturnABC.set! 2 (90 : UInt8)

def byteArraySetBangTrap : ByteArray :=
  byteArrayReturnABC.set! 5 (90 : UInt8)

def byteArrayToUInt64LE : UInt64 :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8), (4 : UInt8),
    (5 : UInt8), (6 : UInt8), (7 : UInt8), (8 : UInt8)]).toUInt64LE!

def byteArrayToUInt64BE : UInt64 :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8), (4 : UInt8),
    (5 : UInt8), (6 : UInt8), (7 : UInt8), (8 : UInt8)]).toUInt64BE!

def byteArrayToUInt64Trap : UInt64 :=
  byteArrayReturnABC.toUInt64LE!

def byteArrayMkReturn : ByteArray :=
  ByteArray.mk #[(65 : UInt8), (66 : UInt8), (67 : UInt8)]

def byteArrayMkSize : Nat :=
  byteArrayMkReturn.size

def byteArrayStringLiteralReturn : ByteArray :=
  "ABC".toUTF8

def byteArrayStringLiteralSize : Nat :=
  "ABC".toUTF8.size

def stringConstName : String :=
  "XY" ++ "Z"

def byteArrayStringAppendReturn : ByteArray :=
  ("AB" ++ "C").toUTF8

def byteArrayStringLetReturn : ByteArray :=
  let text : String := "A" ++ "Z"
  text.toUTF8

def byteArrayStringConstReturn : ByteArray :=
  stringConstName.toUTF8

def stringLengthAppend : Nat :=
  ("AB" ++ "CD").length

def stringIsEmptyLet : Bool :=
  let text : String := ""
  text.isEmpty

def stringEqualityLet : UInt64 :=
  let text : String := "AB" ++ "C"
  if text == "ABC" then
    1
  else
    0

def stringInequalityLet : UInt64 :=
  let text : String := "AB" ++ "D"
  if text != "ABC" then
    1
  else
    0

def byteArrayBranchHelperReturn (flag : UInt64) : ByteArray :=
  if flag == 0 then
    byteArrayReturnABC
  else
    "Z".toUTF8

def byteArrayMkSizeForcesArrayTrap : Nat :=
  (ByteArray.mk #[(Array.replicate 0 (0 : UInt8))[0]!]).size

def byteArrayCopySliceReturn : ByteArray :=
  (ByteArray.mk #[(88 : UInt8), (89 : UInt8), (90 : UInt8)]).copySlice
    1
    byteArrayReturnABC
    1
    2

def byteArrayCopySliceSize : Nat :=
  byteArrayCopySliceReturn.size

def byteArrayCopySliceShortSource : ByteArray :=
  (ByteArray.mk #[(88 : UInt8)]).copySlice
    0
    byteArrayReturnABC
    1
    3

def byteArrayCopySliceExactSkipsTrap : Nat :=
  let exact := (Array.replicate 0 false)[0]!
  (ByteArray.empty.copySlice 0 byteArrayReturnABC 1 0 exact).size

def byteArrayFoldSum : Nat :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).foldl
    (fun acc byte => acc + byte.toNat)
    0

def byteArrayFoldWindow : Nat :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8), (4 : UInt8)]).foldl
    (fun acc byte => acc * 10 + byte.toNat)
    0
    1
    3

def byteArrayFoldEmptySkipsFunctionTrap : Nat :=
  ByteArray.empty.foldl
    (fun acc _byte => acc + ((Array.replicate 0 (0 : UInt64))[0]!).toNat)
    7

def byteArrayFoldStructAccumulator : UInt64 :=
  let result :=
    (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).foldl
      (fun acc byte => { pos := acc.pos + 1, sum := acc.sum + byte.toUInt64 })
      ({ pos := 0, sum := 0 } : DigitState)
  result.pos.toUInt64 * (10 : UInt64) + result.sum

def byteArrayFoldProductAccumulator : UInt64 :=
  let result :=
    (ByteArray.mk #[(5 : UInt8), (6 : UInt8)]).foldl
      (fun acc byte => (acc.1 + 1, acc.2 + byte.toUInt64))
      ((0 : UInt64), (0 : UInt64))
  result.1 * (100 : UInt64) + result.2

def byteArrayFoldStatusAccumulator : UInt64 :=
  let result :=
    (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).foldl
      (fun acc byte =>
        match acc with
        | Status.ok sum =>
            if byte == (2 : UInt8) then
              Status.error (sum + 20)
            else
              Status.ok (sum + byte.toUInt64)
        | Status.error code => Status.error (code + byte.toUInt64))
      (Status.ok 0)
  match result with
  | Status.ok sum => sum
  | Status.error code => code

def byteArrayFoldArrayAccumulator : UInt64 :=
  let result :=
    (ByteArray.mk #[(1 : UInt8), (2 : UInt8)]).foldl
      (fun acc byte => acc.push byte.toUInt64)
      (#[] : Array UInt64)
  if result.size == 2 then
    result[0]! * (10 : UInt64) + result[1]!
  else
    0

def byteArrayFoldByteArrayAccumulator : ByteArray :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8)]).foldl
    (fun acc byte => acc.push byte)
    ByteArray.empty

def byteArrayFoldByteArrayAccumulatorReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output :=
    (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).foldl
      (fun acc byte => acc.push byte)
      ByteArray.empty
  let releasesAfterFold := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterFold := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterFold * 100 + freesAfterFold

def byteArrayFoldMExceptSuccess : Except UInt64 UInt64 :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).foldlM (m := Except UInt64)
    (fun (acc : UInt64) byte => Except.ok (acc + byte.toUInt64))
    0

def byteArrayFoldMExceptErrorSkipsRestTrap : Except UInt64 UInt64 :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).foldlM (m := Except UInt64)
    (fun (acc : UInt64) byte =>
      if byte == (2 : UInt8) then
        Except.error (acc + 20)
      else if byte == (3 : UInt8) then
        Except.ok ((Array.replicate 0 (0 : UInt64))[0]!)
      else
        Except.ok (acc + byte.toUInt64))
    0

def byteArrayFoldMOptionSuccess : Option UInt64 :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).foldlM (m := Option)
    (fun (acc : UInt64) byte => some (acc + byte.toUInt64))
    0

def byteArrayFoldMOptionNoneSkipsRestTrap : Option UInt64 :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).foldlM (m := Option)
    (fun (acc : UInt64) byte =>
      if byte == (2 : UInt8) then
        none
      else if byte == (3 : UInt8) then
        some ((Array.replicate 0 (0 : UInt64))[0]!)
      else
        some (acc + byte.toUInt64))
    0

def byteArrayFoldMOptionByteArray : Option ByteArray :=
  (ByteArray.mk #[(65 : UInt8), (66 : UInt8)]).foldlM (m := Option)
    (fun acc byte => some (acc.push byte))
    ByteArray.empty

def byteArrayFoldInputByteArrayAccumulatorReleaseStats (input : ByteArray) : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output :=
    input.foldl
      (fun acc byte => acc.push byte)
      ByteArray.empty
  let releasesAfterFold := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterFold := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterFold * 100 + freesAfterFold

def byteArrayArrayReadSize : Nat :=
  let values := #["A".toUTF8, "BC".toUTF8]
  values[0]!.size * 10 + values[1]!.size

def byteArrayArrayFoldSize : Nat :=
  let values := #["A".toUTF8, "BC".toUTF8, "DEF".toUTF8]
  values.foldl (fun acc bytes => acc + bytes.size) 0

def byteArrayArrayFoldAppend : ByteArray :=
  let values := #["A".toUTF8, "BC".toUTF8, "DEF".toUTF8]
  values.foldl (fun acc bytes => acc ++ bytes) ByteArray.empty

def byteArrayFieldStructureArrayFold : UInt64 :=
  let values :=
    #[({ count := 1, bytes := "A".toUTF8 } : ByteOutputState),
      ({ count := 2, bytes := "BC".toUTF8 } : ByteOutputState)]
  values.foldl (fun acc state => acc + state.count + state.bytes.size.toUInt64) 0

def byteArrayStructReplicateRuntimeReleaseFrees : UInt64 :=
  let values :=
    Array.replicate 1
      ({ count := 1, bytes := "ABC".toUTF8.extract 1 3 } : ByteOutputState)
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release values
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def nestedArrayRuntimeReleaseFrees : UInt64 :=
  let values := Array.replicate 1 (Array.replicate 2 (5 : UInt64))
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release values
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def structArrayFieldRuntimeReleaseFrees : UInt64 :=
  let values :=
    Array.replicate 1 ({ values := Array.replicate 2 (5 : UInt64), count := 2 } : ArrayBox)
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release values
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def ownedArrayCallTemp : Array UInt64 :=
  Array.replicate 1 (5 : UInt64)

def ownedArrayCallTempScalar : UInt64 :=
  let values := ownedArrayCallTemp
  values[0]!

def ownedByteArrayCallTemp : ByteArray :=
  ByteArray.empty.push (65 : UInt8)

def ownedByteArrayCallTempScalar : UInt64 :=
  let bytes := ownedByteArrayCallTemp
  bytes.size.toUInt64 + bytes[0]!.toUInt64

def ownedArrayCallTempFromParam (input : Array UInt64) : Array UInt64 :=
  input.push (9 : UInt64)

def ownedArrayParamCallTempScalarFromInput (input : Array UInt64) : UInt64 :=
  let values := ownedArrayCallTempFromParam input
  values.size.toUInt64 + values[0]! + values[1]!

def ownedArrayParamCallTempScalar : UInt64 :=
  ownedArrayParamCallTempScalarFromInput #[5]

def ownedByteArrayCallTempFromParam (input : ByteArray) : ByteArray :=
  input.push (33 : UInt8)

def ownedByteArrayParamCallTempScalarFromInput (input : ByteArray) : UInt64 :=
  let bytes := ownedByteArrayCallTempFromParam input
  bytes.size.toUInt64 + bytes[0]!.toUInt64 + bytes[1]!.toUInt64

def ownedByteArrayParamCallTempScalar : UInt64 :=
  ownedByteArrayParamCallTempScalarFromInput "A".toUTF8

def depthAliasSideBuy : UInt64 := 0

def depthAliasSideSell : UInt64 := 1

structure DepthAliasOrder where
  id : UInt64
  trader : UInt64
  side : UInt64
  qty : UInt64
  price : UInt64
deriving Inhabited

structure DepthAliasLevel where
  price : UInt64
  qty : UInt64
deriving Inhabited

structure DepthAliasState where
  bids : Array DepthAliasLevel
  asks : Array DepthAliasLevel

structure DepthAliasResult where
  bids : Array DepthAliasLevel
  asks : Array DepthAliasLevel

def depthAliasInsertLevelFuel :
    Nat → Array DepthAliasLevel → DepthAliasLevel → Nat → Array DepthAliasLevel
  | 0, levels, level, _index => levels.push level
  | fuel + 1, levels, level, index =>
      if index == levels.size then
        levels.push level
      else
        let current := levels[index]!
        if current.price == level.price then
          levels.setIfInBounds index { current with qty := current.qty + level.qty }
        else if current.price < level.price then
          levels.insertIdxIfInBounds index level
        else
          depthAliasInsertLevelFuel fuel levels level (index + 1)

def depthAliasInsertLevel (levels : Array DepthAliasLevel) (level : DepthAliasLevel) :
    Array DepthAliasLevel :=
  depthAliasInsertLevelFuel (levels.size + 1) levels level 0

def depthAliasBidOnlyOrders : Array DepthAliasOrder :=
  Array.empty.push
    { id := 1, trader := 5, side := depthAliasSideBuy, qty := 6, price := 12 }

def depthAliasAskOnlyOrders : Array DepthAliasOrder :=
  Array.empty.push
    { id := 1, trader := 5, side := depthAliasSideSell, qty := 6, price := 100 }

def depthAliasAddOrder (state : DepthAliasState) (order : DepthAliasOrder) :
    DepthAliasState :=
  let level := { price := order.price, qty := order.qty }
  if order.side == depthAliasSideBuy then
    { state with bids := depthAliasInsertLevel state.bids level }
  else if order.side == depthAliasSideSell then
    { state with asks := depthAliasInsertLevel state.asks level }
  else
    state

def depthAliasStateFuel :
    Nat → Array DepthAliasOrder → Nat → DepthAliasState → DepthAliasState
  | 0, _orders, _index, state => state
  | fuel + 1, orders, index, state =>
      if index == orders.size then
        state
      else
        depthAliasStateFuel fuel orders (index + 1) (depthAliasAddOrder state orders[index]!)

def depthAliasResult (orders : Array DepthAliasOrder) : DepthAliasResult :=
  let state :=
    depthAliasStateFuel
      (orders.size + 1)
      orders
      0
      ({ bids := Array.empty, asks := Array.empty } : DepthAliasState)
  { bids := state.bids, asks := state.asks }

def appendDepthAliasLevel (out : ByteArray) (level : DepthAliasLevel) : ByteArray :=
  let out := LeanExe.Ascii.appendUInt64Decimal out level.price
  let out := out.push (32 : UInt8)
  LeanExe.Ascii.appendUInt64Decimal out level.qty

def appendDepthAliasLevelsFuel :
    Nat → ByteArray → Array DepthAliasLevel → Nat → ByteArray
  | 0, out, _levels, _index => out
  | fuel + 1, out, levels, index =>
      if index == levels.size then
        out
      else
        let out := out.push (32 : UInt8)
        let out := appendDepthAliasLevel out levels[index]!
        appendDepthAliasLevelsFuel fuel out levels (index + 1)

def appendDepthAliasLevels (out : ByteArray) (levels : Array DepthAliasLevel) : ByteArray :=
  let out := LeanExe.Ascii.appendUInt64Decimal out levels.size.toUInt64
  appendDepthAliasLevelsFuel (levels.size + 1) out levels 0

def renderDepthAliasResult (result : DepthAliasResult) : ByteArray :=
  let out := LeanExe.Ascii.appendUInt64Decimal ByteArray.empty 0
  let out := out.push (32 : UInt8)
  let out := appendDepthAliasLevels out result.bids
  let out := out.push (32 : UInt8)
  let out := appendDepthAliasLevels out result.asks
  out.push (10 : UInt8)

def depthAliasOrdersForInput (input : ByteArray) : Array DepthAliasOrder :=
  if input.size == 0 then
    depthAliasBidOnlyOrders
  else
    depthAliasAskOnlyOrders

def depthAliasRun (input : ByteArray) : Except ByteArray ByteArray :=
  Except.ok (renderDepthAliasResult (depthAliasResult (depthAliasOrdersForInput input)))

def byteArrayResultDropsOwnedTemp : ByteArray :=
  let temp := ByteArray.empty.push (65 : UInt8)
  if temp[0]! == (65 : UInt8) then
    ByteArray.empty.push (66 : UInt8)
  else
    ByteArray.empty.push (67 : UInt8)

def byteArrayResultDropsOwnedTempStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output := byteArrayResultDropsOwnedTemp
  let releasesAfterCall := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterCall := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterCall * 100 + freesAfterCall

def ownedRecursiveNodeCallTempFromParam (tree : U64Binary) : U64Binary :=
  U64Binary.node (U64Binary.leaf 9) tree

def ownedRecursiveNodeParamCallTempScalar : UInt64 :=
  let source := U64Binary.leaf 1
  let tree := ownedRecursiveNodeCallTempFromParam source
  u64BinaryNodeCount tree * 100 + u64BinaryLeafSum tree

def recursiveResultDropsOwnedTemp : U64Binary :=
  let temp := U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2)
  if u64BinaryLeafSum temp == 3 then
    U64Binary.node (U64Binary.leaf 4) (U64Binary.leaf 5)
  else
    U64Binary.leaf 0

def unusedRecursiveRuntimeReleaseFrees : UInt64 :=
  let tree := U64Binary.node (U64Binary.leaf 2) (U64Binary.leaf 3)
  let before := LeanExe.Runtime.freeCount
  let _ := LeanExe.Runtime.release tree
  LeanExe.Runtime.freeCount - before

def arrayFoldRecursiveAccumulatorReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let tree :=
    (#[1, 2, 3] : Array UInt64).foldl
      (fun _acc value =>
        U64Binary.node
          (U64Binary.leaf value)
          (U64Binary.leaf (value + 10)))
      (U64Binary.leaf 0)
  let releasesAfterFold := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterFold := LeanExe.Runtime.freeCount - before
  u64BinaryNodeCount tree * 10000 + releasesAfterFold * 100 + freesAfterFold

def recursiveScenarioRuntimeReleaseStats (kind : UInt64) : UInt64 :=
  let tree :=
    if kind == 0 then
      U64Binary.leaf 5
    else if kind == 1 then
      U64Binary.node
        (U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2))
        (U64Binary.node (U64Binary.leaf 3) (U64Binary.leaf 4))
    else if kind == 2 then
      U64Binary.node
        (U64Binary.node
          (U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2))
          (U64Binary.leaf 3))
        (U64Binary.leaf 4)
    else
      U64Binary.node
        (U64Binary.leaf 1)
        (U64Binary.node
          (U64Binary.leaf 2)
          (U64Binary.node (U64Binary.leaf 3) (U64Binary.leaf 4)))
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release tree
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def recursiveScenarioHelperRuntimeReleaseStats (kind : UInt64) : UInt64 :=
  let tree := u64BinaryScenario kind
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release tree
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def sharedRecursiveChildReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let retainsBefore := LeanExe.Runtime.retainCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let child := U64Binary.leaf 7
  let tree := U64Binary.node child child
  let after := LeanExe.Runtime.release tree
  (LeanExe.Runtime.retainCount - retainsBefore) * 10000 +
    (LeanExe.Runtime.releaseCount - releasesBefore) * 100 +
    (after - before)

def ownedBoxCallTemp : OwnedCallBox :=
  { values := Array.replicate 1 (5 : UInt64),
    bytes := ByteArray.empty.push (65 : UInt8),
    count := 7 }

def ownedBoxCallTempScalar : UInt64 :=
  let box := ownedBoxCallTemp
  box.values[0]! + box.bytes.size.toUInt64 + box.count

def borrowedArrayPopEmptyReleaseFrees (values : Array UInt64) : UInt64 :=
  let popped := values.pop
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release popped
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def borrowedArraySetOobReleaseFrees (values : Array UInt64) : UInt64 :=
  let updated := values.setIfInBounds values.size (99 : UInt64)
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release updated
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def borrowedArrayReverseSingletonReleaseFrees (values : Array UInt64) : UInt64 :=
  let reversed := values.reverse
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release reversed
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def rejectReleaseUseAfter : UInt64 :=
  let tree := U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2)
  let released := LeanExe.Runtime.release tree
  released + u64BinaryNodeCount tree

def rejectReleaseTwice : UInt64 :=
  let tree := U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2)
  let first := LeanExe.Runtime.release tree
  let second := LeanExe.Runtime.release tree
  first + second

def rejectReleaseAlias : UInt64 :=
  let tree := U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2)
  let alias := tree
  let released := LeanExe.Runtime.release tree
  released + u64BinaryNodeCount alias

def rejectReleaseContainerEscape : UInt64 :=
  let tree := U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2)
  let held : Array U64Binary := #[tree]
  let released := LeanExe.Runtime.release tree
  released + held.size.toUInt64

def releaseReturnEscapeHelper : U64Binary :=
  let tree := U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2)
  let _ := LeanExe.Runtime.release tree
  tree

def rejectReleaseReturnEscape : UInt64 :=
  u64BinaryNodeCount releaseReturnEscapeHelper

def releaseParameterHelper (tree : U64Binary) : UInt64 :=
  let released := LeanExe.Runtime.release tree
  released

def rejectReleaseParameter : UInt64 :=
  releaseParameterHelper (U64Binary.leaf 1)

def returnSameTree (tree : U64Binary) : U64Binary :=
  tree

def rejectReleaseInterproceduralAlias : UInt64 :=
  let tree := U64Binary.node (U64Binary.leaf 1) (U64Binary.leaf 2)
  let alias := returnSameTree tree
  let released := LeanExe.Runtime.release tree
  released + u64BinaryNodeCount alias

def releaseOwnedSetOobHelper (values : Array UInt64) : UInt64 :=
  let updated := values.setIfInBounds values.size (99 : UInt64)
  let released := LeanExe.Runtime.release updated
  released

def rejectReleaseOwnedSetOobHelper : UInt64 :=
  releaseOwnedSetOobHelper (Array.replicate 1 (5 : UInt64))

def byteArrayFoldByteOutputState : ByteOutputState :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).foldl
    (fun acc byte => { count := acc.count + 1, bytes := acc.bytes.push byte })
    ({ count := 0, bytes := ByteArray.empty } : ByteOutputState)

def byteArrayFindIdxSome : Option Nat :=
  (ByteArray.mk #[(1 : UInt8), (42 : UInt8), (3 : UInt8)]).findIdx?
    (fun byte => byte == (42 : UInt8))

def byteArrayFindIdxNone : Option Nat :=
  (ByteArray.mk #[(1 : UInt8), (2 : UInt8), (3 : UInt8)]).findIdx?
    (fun byte => byte == (42 : UInt8))

def byteArrayFindIdxStart : Option Nat :=
  (ByteArray.mk #[(42 : UInt8), (1 : UInt8), (42 : UInt8)]).findIdx?
    (fun byte => byte == (42 : UInt8))
    1

def byteArrayFindIdxEmptySkipsPredicateTrap : Option Nat :=
  ByteArray.empty.findIdx?
    (fun _byte => (Array.replicate 0 false)[0]!)

def rejectUnitReturn : Unit :=
  ()

def rejectUnitParam (_value : Unit) : UInt64 :=
  1

def byteArrayIdentityReturn (input : ByteArray) : ByteArray :=
  input

def byteArrayExceptBangOrError (input : ByteArray) : Except ByteArray ByteArray :=
  if input.isEmpty then
    Except.error "empty".toUTF8
  else
    Except.ok (input.push (33 : UInt8))

def publicNestedArrayReturn : Array (Array UInt64) :=
  #[#[1, 2]]

def publicNestedArrayParam (rows : Array (Array UInt64)) : UInt64 :=
  rows.foldl (fun acc row => acc + row.foldl (fun inner value => inner + value) 0) 0

def publicNestedArrayOpsReturn (rows : Array (Array UInt64)) : Array (Array UInt64) :=
  let mapped := rows.map (fun row => row.push row.size.toUInt64)
  let grown := mapped.push #[99, 100]
  (grown.extract 0 3).reverse

def publicByteArrayArrayReturn : Array ByteArray :=
  #["A".toUTF8, "BC".toUTF8]

def publicByteArrayArrayParam (values : Array ByteArray) : UInt64 :=
  values.foldl (fun acc bytes => acc + bytes.size.toUInt64) 0

def publicOptionArrayReturn : Option (Array ByteArray) :=
  some #["A".toUTF8, "BC".toUTF8]

def publicOptionArrayParam (value : Option (Array ByteArray)) : UInt64 :=
  match value with
  | none => 0
  | some values => values.foldl (fun acc bytes => acc + bytes.size.toUInt64) 0

def publicExceptArrayReturn : Except ByteArray (Array ByteArray) :=
  Except.ok #["A".toUTF8, "BC".toUTF8]

def publicExceptArrayParam (value : Except ByteArray (Array ByteArray)) : UInt64 :=
  match value with
  | Except.error bytes => bytes.size.toUInt64
  | Except.ok values => values.foldl (fun acc bytes => acc + bytes.size.toUInt64) 10

def publicOptionByteArrayArrayReturn : Array (Option ByteArray) :=
  #[some "A".toUTF8, none, some "BC".toUTF8]

def publicOptionByteArrayArrayParam (values : Array (Option ByteArray)) : UInt64 :=
  values.foldl
    (fun acc item =>
      match item with
      | none => acc + 10
      | some bytes => acc + bytes.size.toUInt64)
    0

def publicOptionByteArrayArrayOpsReturn (values : Array (Option ByteArray)) :
    Array (Option ByteArray) :=
  let mapped :=
    values.map (fun item =>
      match item with
      | none => none
      | some bytes => some (bytes.push (33 : UInt8)))
  mapped.reverse

def publicOptionByteArrayScore : Option ByteArray -> UInt64
  | none => 10
  | some bytes => bytes.size.toUInt64

def publicOptionByteArrayArrayFullOps (values : Array (Option ByteArray)) :
    Except UInt64 UInt64 := do
  let pushed := values.push (some "D".toUTF8)
  let appended := pushed ++ #[none, some "EF".toUTF8]
  let extracted := appended.extract 1 5
  let set := extracted.setIfInBounds 0 (some "GHI".toUTF8)
  let inserted := set.insertIdxIfInBounds 2 (some "JK".toUTF8)
  let erased := inserted.eraseIdxIfInBounds 3
  let swapped := erased.swapIfInBounds 0 3
  let reversed := swapped.reverse
  let mapped := reversed.map (fun item =>
    match item with
    | none => none
    | some bytes => some (bytes.push (33 : UInt8)))
  let filtered := mapped.filter (fun item =>
    match item with
    | none => false
    | some bytes => if bytes.size > 2 then true else false)
  let foundSize :=
    match mapped.find? (fun item =>
      match item with
      | none => false
      | some bytes => bytes.size == 3) with
    | none => 0
    | some item => publicOptionByteArrayScore item
  let foundIdx :=
    match mapped.findIdx? (fun item =>
      match item with
      | none => true
      | some _bytes => false) with
    | none => 99
    | some index => index.toUInt64
  let anyScore := if mapped.any (fun item => item.isNone) then 1 else 0
  let allScore :=
    if mapped.all (fun item =>
      match item with
      | none => false
      | some bytes => if bytes.size > 0 then true else false) then 1 else 0
  let foldSum ←
    filtered.foldlM (m := Except UInt64)
      (fun acc item =>
        match item with
        | none => Except.error 99
        | some bytes => Except.ok (acc + bytes.size.toUInt64))
      0
  Except.ok
    (foldSum * 100000 + filtered.size.toUInt64 * 10000 + foundSize * 1000 +
      foundIdx * 100 + anyScore * 10 + allScore)

def publicOptionByteArrayArrayFullOpsReturn (values : Array (Option ByteArray)) :
    Array (Option ByteArray) :=
  let pushed := values.push (some "D".toUTF8)
  let appended := pushed ++ #[none, some "EF".toUTF8]
  let extracted := appended.extract 1 5
  let set := extracted.setIfInBounds 0 (some "GHI".toUTF8)
  let inserted := set.insertIdxIfInBounds 2 (some "JK".toUTF8)
  let erased := inserted.eraseIdxIfInBounds 3
  let swapped := erased.swapIfInBounds 0 3
  let reversed := swapped.reverse
  let mapped := reversed.map (fun item =>
    match item with
    | none => none
    | some bytes => some (bytes.push (33 : UInt8)))
  mapped.filter (fun item =>
    match item with
    | none => false
    | some bytes => if bytes.size > 2 then true else false)

def publicExceptByteArrayArrayReturn : Array (Except ByteArray ByteArray) :=
  #[Except.ok "A".toUTF8, Except.error "BC".toUTF8, Except.ok "DEF".toUTF8]

def publicExceptByteArrayArrayParam (values : Array (Except ByteArray ByteArray)) : UInt64 :=
  values.foldl
    (fun acc item =>
      match item with
      | Except.error bytes => acc + bytes.size.toUInt64 * 10
      | Except.ok bytes => acc + bytes.size.toUInt64)
    0

def publicExceptByteArrayScore : Except ByteArray ByteArray -> UInt64
  | Except.error bytes => bytes.size.toUInt64 * 10
  | Except.ok bytes => bytes.size.toUInt64

def publicExceptByteArrayArrayFullOps (values : Array (Except ByteArray ByteArray)) :
    Except UInt64 UInt64 := do
  let pushed := values.push (Except.error "G".toUTF8)
  let appended := pushed ++ #[Except.ok "HI".toUTF8]
  let extracted := appended.extract 1 5
  let set := extracted.setIfInBounds 1 (Except.ok "JK".toUTF8)
  let inserted := set.insertIdxIfInBounds 2 (Except.error "LMN".toUTF8)
  let erased := inserted.eraseIdxIfInBounds 3
  let swapped := erased.swapIfInBounds 0 2
  let reversed := swapped.reverse
  let mapped := reversed.map (fun item =>
    match item with
    | Except.error bytes => Except.error (bytes.push (63 : UInt8))
    | Except.ok bytes => Except.ok (bytes.push (33 : UInt8)))
  let filtered := mapped.filter (fun item =>
    match item with
    | Except.error bytes => if bytes.size > 3 then true else false
    | Except.ok _bytes => true)
  let foundErrorSize :=
    match mapped.find? (fun item =>
      match item with
      | Except.error _bytes => true
      | Except.ok _bytes => false) with
    | none => 0
    | some item => publicExceptByteArrayScore item
  let foundIdx :=
    match mapped.findIdx? (fun item =>
      match item with
      | Except.error _bytes => false
      | Except.ok bytes => bytes.size == 3) with
    | none => 99
    | some index => index.toUInt64
  let anyScore :=
    if mapped.any (fun item =>
      match item with
      | Except.error bytes => bytes.size == 4
      | Except.ok _bytes => false) then 1 else 0
  let allScore :=
    if mapped.all (fun item =>
      match item with
      | Except.error bytes => if bytes.size > 2 then true else false
      | Except.ok bytes => if bytes.size > 2 then true else false) then 1 else 0
  let foldSum ←
    mapped.foldlM (m := Except UInt64)
      (fun acc item =>
        match item with
        | Except.error bytes =>
            if bytes.size > 4 then
              Except.error 99
            else
              Except.ok (acc + bytes.size.toUInt64 * 10)
        | Except.ok bytes => Except.ok (acc + bytes.size.toUInt64))
      0
  Except.ok
    (foldSum * 100000 + filtered.size.toUInt64 * 10000 + foundErrorSize * 1000 +
      foundIdx * 100 + anyScore * 10 + allScore)

def publicExceptByteArrayArrayFullOpsReturn (values : Array (Except ByteArray ByteArray)) :
    Array (Except ByteArray ByteArray) :=
  let pushed := values.push (Except.error "G".toUTF8)
  let appended := pushed ++ #[Except.ok "HI".toUTF8]
  let extracted := appended.extract 1 5
  let set := extracted.setIfInBounds 1 (Except.ok "JK".toUTF8)
  let inserted := set.insertIdxIfInBounds 2 (Except.error "LMN".toUTF8)
  let erased := inserted.eraseIdxIfInBounds 3
  let swapped := erased.swapIfInBounds 0 2
  let reversed := swapped.reverse
  let mapped := reversed.map (fun item =>
    match item with
    | Except.error bytes => Except.error (bytes.push (63 : UInt8))
    | Except.ok bytes => Except.ok (bytes.push (33 : UInt8)))
  mapped.filter (fun item =>
    match item with
    | Except.error bytes => if bytes.size > 3 then true else false
    | Except.ok _bytes => true)

def publicTokenArrayReturn : Array PublicToken :=
  #[PublicToken.text "A".toUTF8, PublicToken.number 7, PublicToken.text "BC".toUTF8]

def publicTokenArrayParam (values : Array PublicToken) : UInt64 :=
  values.foldl
    (fun acc token =>
      match token with
      | PublicToken.text bytes => acc + bytes.size.toUInt64
      | PublicToken.number value => acc + value)
    0

def publicTokenArrayOpsReturn (values : Array PublicToken) : Array PublicToken :=
  let mapped :=
    values.map (fun token =>
      match token with
      | PublicToken.text bytes => PublicToken.text (bytes.push (33 : UInt8))
      | PublicToken.number value => PublicToken.number (value + 1))
  (mapped.filter (fun token =>
    match token with
    | PublicToken.text bytes => if bytes.size > 1 then true else false
    | PublicToken.number value => if value > 7 then true else false)).reverse

def publicTokenScore : PublicToken -> UInt64
  | PublicToken.text bytes => bytes.size.toUInt64
  | PublicToken.number value => value

def publicTokenArrayFullOps (values : Array PublicToken) : Except UInt64 UInt64 := do
  let pushed := values.push (PublicToken.text "D".toUTF8)
  let appended := pushed ++ #[PublicToken.number 3, PublicToken.text "EF".toUTF8]
  let extracted := appended.extract 1 5
  let set := extracted.setIfInBounds 2 (PublicToken.text "GHI".toUTF8)
  let inserted := set.insertIdxIfInBounds 1 (PublicToken.number 11)
  let erased := inserted.eraseIdxIfInBounds 0
  let swapped := erased.swapIfInBounds 1 3
  let reversed := swapped.reverse
  let mapped := reversed.map (fun token =>
    match token with
    | PublicToken.text bytes => PublicToken.text (bytes.push (33 : UInt8))
    | PublicToken.number value => PublicToken.number (value + 1))
  let filtered := mapped.filter (fun token =>
    match token with
    | PublicToken.text bytes => if bytes.size > 3 then true else false
    | PublicToken.number value => if value > 10 then true else false)
  let foundValue :=
    match mapped.find? (fun token =>
      match token with
      | PublicToken.text _bytes => false
      | PublicToken.number _value => true) with
    | none => 0
    | some token => publicTokenScore token
  let foundIdx :=
    match mapped.findIdx? (fun token =>
      match token with
      | PublicToken.text bytes => bytes.size == 3
      | PublicToken.number _value => false) with
    | none => 99
    | some index => index.toUInt64
  let anyScore :=
    if mapped.any (fun token =>
      match token with
      | PublicToken.text _bytes => false
      | PublicToken.number value => value == 12) then 1 else 0
  let allScore :=
    if mapped.all (fun token =>
      match token with
      | PublicToken.text bytes => if bytes.size > 0 then true else false
      | PublicToken.number value => if value > 0 then true else false) then 1 else 0
  let foldSum ←
    mapped.foldlM (m := Except UInt64)
      (fun acc token =>
        match token with
        | PublicToken.text bytes => Except.ok (acc + bytes.size.toUInt64)
        | PublicToken.number value =>
            if value == 0 then
              Except.error 99
            else
              Except.ok (acc + value))
      0
  Except.ok
    (foldSum * 100000 + filtered.size.toUInt64 * 10000 + foundValue * 1000 +
      foundIdx * 100 + anyScore * 10 + allScore)

def publicTokenArrayFullOpsReturn (values : Array PublicToken) : Array PublicToken :=
  let pushed := values.push (PublicToken.text "D".toUTF8)
  let appended := pushed ++ #[PublicToken.number 3, PublicToken.text "EF".toUTF8]
  let extracted := appended.extract 1 5
  let set := extracted.setIfInBounds 2 (PublicToken.text "GHI".toUTF8)
  let inserted := set.insertIdxIfInBounds 1 (PublicToken.number 11)
  let erased := inserted.eraseIdxIfInBounds 0
  let swapped := erased.swapIfInBounds 1 3
  let reversed := swapped.reverse
  let mapped := reversed.map (fun token =>
    match token with
    | PublicToken.text bytes => PublicToken.text (bytes.push (33 : UInt8))
    | PublicToken.number value => PublicToken.number (value + 1))
  mapped.filter (fun token =>
    match token with
    | PublicToken.text bytes => if bytes.size > 3 then true else false
    | PublicToken.number value => if value > 10 then true else false)

def publicByteArrayGroupReturn : ByteArrayGroup :=
  { values := #["A".toUTF8, "BC".toUTF8], marker := 9 }

def publicByteArrayGroupParam (group : ByteArrayGroup) : UInt64 :=
  group.values.foldl (fun acc bytes => acc + bytes.size.toUInt64) group.marker

def publicByteArrayGroupScore (group : ByteArrayGroup) : UInt64 :=
  group.marker * 100 + group.values.foldl (fun acc bytes => acc + bytes.size.toUInt64) 0

def publicByteArrayGroupArrayReturn : Array ByteArrayGroup :=
  #[
    { values := #["A".toUTF8, "BC".toUTF8], marker := 2 },
    { values := #["D".toUTF8], marker := 3 }
  ]

def publicByteArrayGroupArrayParam (groups : Array ByteArrayGroup) : UInt64 :=
  groups.foldl (fun acc group => acc + publicByteArrayGroupScore group) 0

def publicByteArrayGroupArrayFullOps (groups : Array ByteArrayGroup) : Except UInt64 UInt64 := do
  let pushed := groups.push { values := #["F".toUTF8], marker := 4 }
  let appended := pushed ++ #[{ values := #["GH".toUTF8], marker := 5 }]
  let extracted := appended.extract 0 4
  let set := extracted.setIfInBounds 1 { values := #["IJ".toUTF8, "K".toUTF8], marker := 6 }
  let inserted := set.insertIdxIfInBounds 2 { values := #["LMN".toUTF8], marker := 7 }
  let erased := inserted.eraseIdxIfInBounds 3
  let swapped := erased.swapIfInBounds 0 3
  let reversed := swapped.reverse
  let mapped := reversed.map (fun group =>
    { values := group.values.push "Z".toUTF8, marker := group.marker + 1 })
  let filtered := mapped.filter (fun group => if group.marker > 6 then true else false)
  let foundScore :=
    match mapped.find? (fun group => group.marker == 7) with
    | none => 0
    | some group => publicByteArrayGroupScore group
  let foundIdx :=
    match mapped.findIdx? (fun group => group.values.size == 2) with
    | none => 99
    | some index => index.toUInt64
  let anyScore := if mapped.any (fun group => group.marker == 8) then 1 else 0
  let allScore := if mapped.all (fun group => if group.values.isEmpty then false else true) then 1 else 0
  let foldSum ←
    mapped.foldlM (m := Except UInt64)
      (fun acc group =>
        if group.values.isEmpty then
          Except.error 99
        else
          Except.ok (acc + publicByteArrayGroupScore group))
      0
  Except.ok
    (foldSum * 100000000 + filtered.size.toUInt64 * 1000000 + foundScore * 1000 +
      foundIdx * 100 + anyScore * 10 + allScore)

def publicByteArrayGroupArrayFullOpsReturn (groups : Array ByteArrayGroup) :
    Array ByteArrayGroup :=
  let pushed := groups.push { values := #["F".toUTF8], marker := 4 }
  let appended := pushed ++ #[{ values := #["GH".toUTF8], marker := 5 }]
  let extracted := appended.extract 0 4
  let set := extracted.setIfInBounds 1 { values := #["IJ".toUTF8, "K".toUTF8], marker := 6 }
  let inserted := set.insertIdxIfInBounds 2 { values := #["LMN".toUTF8], marker := 7 }
  let erased := inserted.eraseIdxIfInBounds 3
  let swapped := erased.swapIfInBounds 0 3
  let reversed := swapped.reverse
  let mapped := reversed.map (fun group =>
    { values := group.values.push "Z".toUTF8, marker := group.marker + 1 })
  mapped.filter (fun group => if group.marker > 6 then true else false)

def publicNestedTaggedArrayReturn : Option (Array (Option ByteArray)) :=
  some #[some "A".toUTF8, none, some "BC".toUTF8]

def publicNestedTaggedArrayParam (value : Option (Array (Option ByteArray))) : UInt64 :=
  match value with
  | none => 99
  | some values =>
      values.foldl (fun acc item => acc + publicOptionByteArrayScore item) 0

def optionByteArrayArrayRuntimeReleaseFrees : UInt64 :=
  let values : Array (Option ByteArray) :=
    #[some "A".toUTF8, none, some "BC".toUTF8]
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release values
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def publicTokenArrayRuntimeReleaseFrees : UInt64 :=
  let values : Array PublicToken :=
    #[PublicToken.text "A".toUTF8, PublicToken.number 7, PublicToken.text "BC".toUTF8]
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release values
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def byteArrayGroupArrayRuntimeReleaseFrees : UInt64 :=
  let values : Array ByteArrayGroup :=
    #[
      { values := #["A".toUTF8, "BC".toUTF8], marker := 2 },
      { values := #["D".toUTF8], marker := 3 }
    ]
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let after := LeanExe.Runtime.release values
  (LeanExe.Runtime.releaseCount - releasesBefore) * 100 + (after - before)

def arrayFoldOptionByteArrayAccumulatorReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output :=
    (#[65, 66, 67] : Array UInt64).foldl
      (fun acc value =>
        acc.push (some (ByteArray.empty.push (UInt64.toUInt8 value))))
      (#[] : Array (Option ByteArray))
  let releasesAfterFold := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterFold := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterFold * 100 + freesAfterFold

def arrayFoldPublicTokenAccumulatorReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output :=
    (#[65, 66, 67] : Array UInt64).foldl
      (fun acc value =>
        if value == 66 then
          acc.push (PublicToken.number value)
        else
          acc.push (PublicToken.text (ByteArray.empty.push (UInt64.toUInt8 value))))
      (#[] : Array PublicToken)
  let releasesAfterFold := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterFold := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterFold * 100 + freesAfterFold

def arrayFoldByteArrayGroupAccumulatorReleaseStats : UInt64 :=
  let before := LeanExe.Runtime.freeCount
  let releasesBefore := LeanExe.Runtime.releaseCount
  let output :=
    (#[65, 66, 67] : Array UInt64).foldl
      (fun acc value =>
        acc.push
          ({ values := #[ByteArray.empty.push (UInt64.toUInt8 value)],
             marker := value } : ByteArrayGroup))
      (#[] : Array ByteArrayGroup)
  let releasesAfterFold := LeanExe.Runtime.releaseCount - releasesBefore
  let freesAfterFold := LeanExe.Runtime.freeCount - before
  output.size.toUInt64 * 10000 + releasesAfterFold * 100 + freesAfterFold

def optionByteArrayArrayEquality : UInt64 :=
  let first := #[some "A".toUTF8, none, some "BC".toUTF8]
  let second := #[some "A".toUTF8, none, some "BC".toUTF8]
  if first == second then 1 else 0

def publicTokenArrayEquality : UInt64 :=
  let first := #[PublicToken.text "A".toUTF8, PublicToken.number 7]
  let second := #[PublicToken.text "A".toUTF8, PublicToken.number 7]
  if first == second then 1 else 0

def byteArrayGroupArrayEquality : UInt64 :=
  let first : Array ByteArrayGroup :=
    #[
      { values := #["A".toUTF8, "BC".toUTF8], marker := 2 },
      { values := #["D".toUTF8], marker := 3 }
    ]
  let second : Array ByteArrayGroup :=
    #[
      { values := #["A".toUTF8, "BC".toUTF8], marker := 2 },
      { values := #["D".toUTF8], marker := 3 }
    ]
  if first == second then 1 else 0

def publicHeapArrayResultReturn (flag : UInt64) : PublicHeapArrayResult :=
  if flag == 0 then
    PublicHeapArrayResult.failed "bad".toUTF8
  else
    PublicHeapArrayResult.ok #["A".toUTF8, "BC".toUTF8] 5

def publicHeapArrayResultParam (result : PublicHeapArrayResult) : UInt64 :=
  match result with
  | PublicHeapArrayResult.failed bytes => bytes.size.toUInt64
  | PublicHeapArrayResult.ok values marker =>
      values.foldl (fun acc bytes => acc + bytes.size.toUInt64) marker

def publicByteOutputStateArrayReturn : Array ByteOutputState :=
  #[{ count := 1, bytes := "A".toUTF8 }, { count := 2, bytes := "BC".toUTF8 }]

def publicByteOutputStateArrayParam (values : Array ByteOutputState) : UInt64 :=
  values.foldl (fun acc state => acc + state.count + state.bytes.size.toUInt64) 0

def publicArrayBoxArrayReturn : Array ArrayBox :=
  #[{ values := #[1, 2], count := 2 }]

def publicArrayBoxArrayParam (boxes : Array ArrayBox) : UInt64 :=
  boxes.foldl
    (fun acc box => acc + box.count + box.values.foldl (fun inner value => inner + value) 0)
    0

def publicByteArrayArrayOps (values : Array ByteArray) : Except UInt64 UInt64 := do
  let pushed := values.push "G".toUTF8
  let appended := pushed ++ #["HI".toUTF8]
  let extracted := appended.extract 1 5
  let set := extracted.setIfInBounds 2 "JKL".toUTF8
  let inserted := set.insertIdxIfInBounds 1 "M".toUTF8
  let erased := inserted.eraseIdxIfInBounds 3
  let swapped := erased.swapIfInBounds 0 2
  let reversed := swapped.reverse
  let mapped := reversed.map (fun bytes => bytes.push (33 : UInt8))
  let filtered := mapped.filter (fun bytes => if bytes.size > 2 then true else false)
  let foundSize :=
    match mapped.find? (fun bytes => bytes.size == 4) with
    | none => 0
    | some bytes => bytes.size.toUInt64
  let foundIdx :=
    match mapped.findIdx? (fun bytes => bytes.size == 2) with
    | none => 99
    | some index => index.toUInt64
  let anyScore := if mapped.any (fun bytes => bytes.size == 4) then 1 else 0
  let allScore := if mapped.all (fun bytes => if bytes.size > 1 then true else false) then 1 else 0
  let foldSum ←
    mapped.foldlM (m := Except UInt64)
      (fun acc bytes =>
        if bytes.isEmpty then
          Except.error 99
        else
          Except.ok (acc + bytes.size.toUInt64))
      0
  Except.ok
    (foldSum * 100000 + filtered.size.toUInt64 * 10000 + foundSize * 1000 +
      foundIdx * 100 + anyScore * 10 + allScore)

def publicByteArrayArrayOpsReturn (values : Array ByteArray) : Array ByteArray :=
  let updated := values.setIfInBounds 0 "ZZ".toUTF8
  let grown := updated.push "Q".toUTF8
  let window := grown.extract 0 3
  (window.reverse.map (fun bytes => bytes.push (33 : UInt8))).filter
    (fun bytes => if bytes.size > 2 then true else false)

def uint8ParamToNat (b : UInt8) : Nat :=
  b.toNat

def uint8Return : UInt8 :=
  300

def uint32ParamToNat (x : UInt32) : Nat :=
  x.toNat

def uint32Return : UInt32 :=
  4294967297

def rejectRuntimeStringToUTF8 (flag : Bool) : ByteArray :=
  (if flag then "A" else "B").toUTF8

def rejectRuntimeStringLength (flag : Bool) : Nat :=
  (if flag then "A" else "B").length

def rejectStringParam (text : String) : Nat :=
  text.length

def alloc : UInt64 :=
  1

def rejectHugeNatLiteral : Nat :=
  18446744073709551616

def rejectHigherOrder (f : UInt64 → UInt64) : UInt64 :=
  f 1

def rejectIO : IO UInt64 :=
  pure 1

end LeanExe.Examples.Correctness
