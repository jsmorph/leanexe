import LeanExe.Extract.Arithmetic

namespace ArithmeticModeTest

def expression (x y : UInt64) : UInt64 := ((x + 7) * (y - 3)) / (x % (y + 1))
def bits (x y : UInt64) : UInt64 := ((x &&& y) ||| (x ^^^ y)) <<< (x >>> y)
def literal : UInt64 := 18446744073709551616
def binding (x : UInt64) : UInt64 := let y := x + 1; y * 2
def natBinding (x : UInt64) : UInt64 := let n : Nat := 3; x + UInt64.ofNat n
def customBinding (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 => z + 1
  f (x + y)
def branch (x : UInt64) : UInt64 := if x = 0 then 1 else x
def sequential (x : UInt64) : UInt64 := Id.run do
  let mut y := x
  y := y + 1
  let z ← pure (y * 2)
  return z
@[instance_reducible] def customPure : Pure Id := ⟨fun value => value⟩
@[instance_reducible] def customBind : Bind Id := ⟨fun value next => next value⟩
def customReturn (x : UInt64) : UInt64 := Id.run (@Pure.pure Id customPure UInt64 x)
def customSequence (x : UInt64) : UInt64 :=
  Id.run (@Bind.bind Id customBind UInt64 UInt64 x (fun y => y + 1))
def joinedChoice (x y : UInt64) : UInt64 := Id.run do
  let a ← if x < y then pure (x + 1) else pure (y - 1)
  return a * x
def binaryLocalFunction (x : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a + b
  f x x
def unsupportedLocalBody (x : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => expression z x
  x

def range (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    a := a + UInt64.ofNat i
  return a
def rangeNonUnitStep (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [0:n.toNat:2] do
    a := a + UInt64.ofNat i
  return a
def rangeBreak (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    if a == 7 then break
    a := a + 1
  return a
def rangeTwice (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    a := a + 1
  for _ in [:n.toNat] do
    a := a * 3
  return a
def rangeLocal (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let f := fun x : UInt64 => x + UInt64.ofNat i
    a := f a
  return a
def rangeUnsupportedFunction (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    let _f := fun x : UInt64 => expression x a
    a := a + 1
  return a
def rangeBinaryFunction (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    let f := fun x y : UInt64 => x + y
    a := f a a
  return a
def rangeBind (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let delta ← pure (UInt64.ofNat i)
    a := a + delta
  return a
def rangeCustomBind (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun i a =>
    @Bind.bind Id customBind UInt64 (ForInStep UInt64)
      (pure (UInt64.ofNat i)) (fun delta => pure (.yield (a + delta)))
def rangeBindBreak (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let delta ← pure (UInt64.ofNat i)
    if delta == 2 then break
    a := a + delta
  return a
def rangeJoined (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let index := UInt64.ofNat i
    let delta ← if a < 7 then pure (a + index) else pure (seed / index)
    a := a + delta
  return a
def rangeUnusedDone (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    let _bad : UInt64 → Id (ForInStep UInt64) := fun x => pure (.done x)
    a := a + 1
  return a

def rangeUnusedUnsupportedDone (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    let _bad : UInt64 → Id (ForInStep UInt64) := fun x => pure (.done (expression x a))
    a := a + 1
  return a

def rangeDirect (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun i a =>
    if a == seed + 2 then .done (a + UInt64.ofNat i) else .yield (a + 1)

def rangeUnsupportedDirect (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    let _bad : UInt64 → ForInStep UInt64 := fun x => .done (expression x a)
    a := a + 1
  return a

def rangeNatLiteral (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:8] do
    a := a + UInt64.ofNat i
    if a == n then break
  return a

def rangeNatOverflow (seed : UInt64) : UInt64 :=
  forIn (m := Id) [:18446744073709551616] seed fun _ a => .done a

@[instance_reducible] def customNat : OfNat Nat 8 := ⟨9⟩
def rangeCustomNat (seed : UInt64) : UInt64 :=
  forIn (m := Id) [:(@OfNat.ofNat Nat 8 customNat)] seed fun _ a => .done a

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

def intervalOverflow (seed : UInt64) : UInt64 :=
  forIn (m := Id) [18446744073709551616:0] seed fun _ a => .done a

@[instance_reducible] def customFirst : OfNat Nat 8 := ⟨9⟩
def intervalCustom (seed : UInt64) : UInt64 :=
  forIn (m := Id) [(@OfNat.ofNat Nat 8 customFirst):10] seed fun _ a => .done a

def intervalDynamic (seed : UInt64) : UInt64 :=
  forIn (m := Id) [seed.toNat:10] seed fun _ a => .done a

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

def dynamicNatAddition (seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed.toNat + 1):10] seed fun _ a => .done a

def dynamicHelper (seed : UInt64) : UInt64 := seed + 1
def dynamicCalledStart (seed : UInt64) : UInt64 :=
  forIn (m := Id) [(dynamicHelper seed).toNat:10] seed fun _ a => .done a

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

def strideOverflow (seed : UInt64) : UInt64 :=
  forIn (m := Id) [0:10:18446744073709551616] seed fun _ a => .done a

@[instance_reducible] def customStride : OfNat Nat 2 := ⟨3⟩
def strideCustom (seed : UInt64) : UInt64 :=
  forIn (m := Id) [0:10:(@OfNat.ofNat Nat 2 customStride)] seed fun _ a => .done a

def strideDynamic (seed : UInt64) : UInt64 :=
  forIn (m := Id) ({start := 0, stop := 10, step := seed.toNat + 1, step_pos := Nat.zero_lt_succ _} : Std.Legacy.Range) seed fun _ a => .done a

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

def binaryStepExternal (x : UInt64) : UInt64 := x + 1

def rangeBinaryStepUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _unused : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      .done (binaryStepExternal x + y)
    .yield (a + UInt64.ofNat i)

def rangeBinaryStepPartial (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y => .done (x + y)
    let remaining := finish a
    remaining (UInt64.ofNat i)

def rangeBinaryStepThree (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z => .done (x + y + z)
    finish a seed (UInt64.ofNat i)

def rangeBinaryStepBool (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → Bool → ForInStep UInt64 := fun x _ => .done x
    finish (a + UInt64.ofNat i) true

def rangeBinaryStepNat (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : Nat → UInt64 → ForInStep UInt64 := fun _ y => .done y
    finish i a

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

def boolNotCustomBEq (x y : UInt64) : UInt64 :=
  if !(@BEq.beq UInt64 ⟨fun _ _ => true⟩ x y) then x else y

def boolNotDecision (b : Bool) : Decidable (b = true) := inferInstance

def boolNotCustomDecision (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq Bool (Bool.not (x == y)) true) (boolNotDecision (Bool.not (x == y))) (x + 3) (y - 1)

def boolNotExternal (x y : UInt64) : Bool := x == y

def boolNotHelper (x y : UInt64) : UInt64 :=
  if !(boolNotExternal x y) then x + 3 else y - 1

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

def outerRangeExternal (x : UInt64) : UInt64 := x + 1

def rangeOuterUnsupported (count seed : UInt64) : UInt64 := Id.run do
  let _f := fun x : UInt64 => outerRangeExternal x
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeOuterThree (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y z : UInt64 => x + y + z
  let mut a := seed
  for i in [:count.toNat] do
    a := f a seed (UInt64.ofNat i)
  return a

def rangeOuterNat (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x : Nat => UInt64.ofNat x
  let mut a := seed
  for i in [:count.toNat] do
    a := a + f i
  return a

def rangeOuterPartial (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y : UInt64 => x + y
  let g := f seed
  let mut a := seed
  for i in [:count.toNat] do
    a := g a + UInt64.ofNat i
  return a

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

def rangeLetExternal (x : UInt64) : UInt64 := x + 1

def rangeLetUnsupported (count seed : UInt64) : UInt64 :=
  let _ignored := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := rangeLetExternal a + UInt64.ofNat i
    return a
  seed + count

def rangeLetTwoLoops (count seed : UInt64) : UInt64 :=
  let first := Id.run do
    let mut a := seed
    for _ in [:count.toNat] do
      a := a + 1
    return a
  let second := Id.run do
    let mut a := first
    for _ in [:count.toNat] do
      a := a * 3
    return a
  second

def rangeLetBool (count seed : UInt64) : UInt64 :=
  let flag := Id.run do
    let mut a := seed
    for _ in [:count.toNat] do
      a := a + 1
    return a == 0
  if flag then count else seed

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

def complementCustom (x y : UInt64) : UInt64 :=
  @Complement.complement UInt64 ⟨fun z => z + 1⟩ (x + y)

def complementExternal (x : UInt64) : UInt64 := ~~~x

def complementHelper (x y : UInt64) : UInt64 := complementExternal x + y

def complementUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => @Complement.complement UInt64 ⟨fun v => v + 1⟩ z
  x + y

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

def compoundCustom (x y : UInt64) : UInt64 :=
  @ite UInt64 (x = y ∧ y = 0)
    (if h : x = y ∧ y = 0 then isTrue h else isFalse h) (x + 1) (y + 2)

def compoundUnsupported (x y : UInt64) : UInt64 :=
  if x = y ∨ x.toNat < y.toNat then x else y

def compoundUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => @ite UInt64 (z = y ∨ z = 0)
    (if h : z = y ∨ z = 0 then isTrue h else isFalse h) (z + 1) (y + 2)
  x + y

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

def compoundNotCustom (x y : UInt64) : UInt64 :=
  @ite UInt64 (¬ (x = y ∧ y = 0))
    (if h : ¬ (x = y ∧ y = 0) then isTrue h else isFalse h) (x + 1) (y + 2)

def compoundNotInnerCustom (x y : UInt64) : UInt64 :=
  @ite UInt64 (¬ (x = y ∧ y = 0))
    (@instDecidableNot (x = y ∧ y = 0)
      (if h : x = y ∧ y = 0 then isTrue h else isFalse h)) x y

def compoundNotUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => @ite UInt64 (¬ (z = y ∨ z = 0))
    (if h : ¬ (z = y ∨ z = 0) then isTrue h else isFalse h) (z + 1) (y + 2)
  x + y

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

def boolCompoundCustom (x y : UInt64) : UInt64 :=
  if x == 0 && @BEq.beq UInt64 ⟨fun _ _ => true⟩ x y then x else y

def boolCompoundDecision (x y : UInt64) : UInt64 :=
  @ite UInt64 ((x == 0 && y == 0) = true)
    (if h : (x == 0 && y == 0) = true then isTrue h else isFalse h) x y

def boolCompoundUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 =>
    if z == 0 || @BEq.beq UInt64 ⟨fun _ _ => true⟩ z y then z else y
  x + y

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

def mixedGuardCustom (x y : UInt64) : UInt64 :=
  if (x == 0 && @BEq.beq UInt64 ⟨fun _ _ => true⟩ x y) ∨ x < y then x else y

def mixedGuardDecision (x y : UInt64) : UInt64 :=
  @ite UInt64 (((x == 0 || y == 0) = true) ∧ x ≠ y)
    (@instDecidableAnd ((x == 0 || y == 0) = true) (x ≠ y)
      (if h : (x == 0 || y == 0) = true then isTrue h else isFalse h) inferInstance) x y

def mixedGuardUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 =>
    if ¬ (z == 0 || @BEq.beq UInt64 ⟨fun _ _ => true⟩ z y) then z else y
  x + y

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

def minimumCustom (x y : UInt64) : UInt64 :=
  @Min.min UInt64 ⟨fun a b => a + b⟩ x y

def maximumCustom (x y : UInt64) : UInt64 :=
  @Max.max UInt64 ⟨fun a b => a * b⟩ x y

def extremaUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => @Min.min UInt64 ⟨fun a b => a ^^^ b⟩ z y
  max x y

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

def literalInactiveUnsupported (x y : UInt64) : UInt64 :=
  if true then x else @Min.min UInt64 ⟨fun a b => a + b⟩ x y

def literalCustomDecision (x y : UInt64) : UInt64 :=
  @ite UInt64 True (.isTrue True.intro) x y

def literalUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 =>
    if False then @Min.min UInt64 ⟨fun a b => a ^^^ b⟩ z y else z
  if true then x else y

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

def punitHigherUniverse (x y : UInt64) : UInt64 :=
  let f : PUnit.{2} → UInt64 → UInt64 := fun _ a => a + x
  f PUnit.unit y

def punitUnsupportedBody (x y : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a => @Min.min UInt64 ⟨fun b c => b + c⟩ a x
  f PUnit.unit y

def punitUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f : PUnit.{1} → UInt64 → UInt64 := fun _ a => @Min.min UInt64 ⟨fun b c => b ^^^ c⟩ a y
  x + y

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

def idCustomPure (x y : UInt64) : UInt64 :=
  @Pure.pure Id ⟨fun value => value⟩ (Id UInt64) (pure (x + y))

def idCustomBind (x y : UInt64) : UInt64 :=
  @Bind.bind Id ⟨fun value next => next value⟩ UInt64 (Id UInt64)
    x (fun value => pure (pure (value + y)))

def idUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f : UInt64 → Id (Id UInt64) := fun a =>
    pure (pure (@Min.min UInt64 ⟨fun b c => b ^^^ c⟩ a y))
  x + y

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

def manyUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f := fun a b c : UInt64 => UInt64.ofNat ((toString a).length) + b + c
  x + y

def manyWrongDomain (x y : UInt64) : UInt64 :=
  let _f := fun (a b c : UInt64) (d : Nat) => a + b + c + UInt64.ofNat d
  x + y

def manyIgnoredOperand (x y : UInt64) : UInt64 :=
  let f := fun (a b _c : UInt64) => a + b
  f x y (UInt64.ofNat ((toString x).length))

def manyPartial (x y : UInt64) : UInt64 :=
  let f := fun a b c : UInt64 => a + b + c
  let g := f x
  g y x

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

def stepManyUnusedUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let _f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      .yield (UInt64.ofNat ((toString x).length) + y + z)
    .yield (a + 1)

def stepManyWrongDomain (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let _f : UInt64 → UInt64 → UInt64 → Bool → ForInStep UInt64 := fun x y z b =>
      if b then .done (x + y) else .yield (z + a)
    .yield (a + 1)

def stepManyPartial (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z => .yield (x + y + z)
    let g := f a
    g seed (UInt64.ofNat i)

def stepManyIgnoredOperand (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y _z => .yield (x + y)
    f a seed (UInt64.ofNat ((toString seed).length))

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

def dependentInactiveUnsupported (x y : UInt64) : UInt64 :=
  if _h : True then x else @Min.min UInt64 ⟨fun a b => a + b⟩ x y

def dependentCustomDecision (x y : UInt64) : UInt64 :=
  @dite UInt64 True (.isTrue True.intro) (fun _ => x) (fun _ => y)

def dependentUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f := fun a b : UInt64 => if _h : False then UInt64.ofNat (toString a).length else b
  x + y

def rangeDependentInactiveUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    if _h : False then .done (UInt64.ofNat (toString a).length) else .yield (a + 1)

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

def booleanUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _flag := toString x == toString y
  x + y

def booleanCustomEquality (x y : UInt64) : UInt64 :=
  let flag := @BEq.beq UInt64 ⟨fun _ _ => true⟩ x y
  if flag then x else y

def booleanIgnoredOperand (x y : UInt64) : UInt64 :=
  let flag := true || UInt64.ofNat (toString x).length == y
  if flag then x else y

def rangeBooleanUnusedUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let _flag := toString a == toString seed
    .yield (a + 1)

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

def booleanDependentInactiveUnsupported (x y : UInt64) : UInt64 :=
  let flag := true
  if _h : flag then x else UInt64.ofNat (toString y).length

def booleanDependentCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == y
  @dite UInt64 (flag = true) (if h : flag then .isTrue h else .isFalse h)
    (fun _ => x) (fun _ => y)

def booleanDependentUnusedUnsupported (x y : UInt64) : UInt64 :=
  let flag := false
  let _f := fun a b : UInt64 => if _h : flag then UInt64.ofNat (toString a).length else b
  x + y

def rangeBooleanDependentInactiveUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let flag := false
    if _h : flag then .done (UInt64.ofNat (toString a).length) else .yield (a + 1)

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

def instanceCustom (x y : UInt64) : UInt64 :=
  x + @OfNat.ofNat UInt64 (nat_lit 5) ⟨y⟩

def instanceWrappedCustom (x y : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_ : UInt64) => ⟨y⟩) x)

def instanceWrappedVariable (x y : UInt64) : UInt64 :=
  let custom : OfNat UInt64 5 := ⟨x⟩
  @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_ : UInt64) => custom) y)

def rangeInstanceCustom (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    .yield (a + @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_ : UInt64) => ⟨a⟩) seed))

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

def naturalCustomNat (x y : UInt64) : UInt64 :=
  x + UInt64.ofNat (@OfNat.ofNat Nat (nat_lit 5) ⟨y.toNat⟩)

def naturalCustomWord (x y : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 5 ((fun (_ : UInt64) => ⟨y⟩) x)

def naturalNotLiteral (x y : UInt64) : UInt64 :=
  UInt64.ofNat (x.toNat + y.toNat)

def rangeNaturalCustomNat (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    .yield (a + UInt64.ofNat (@OfNat.ofNat Nat (nat_lit 5) ⟨seed.toNat⟩))

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

def boolBindCustomPure (x y : UInt64) : UInt64 := Id.run do
  let flag ← @Pure.pure Id ⟨fun value => value⟩ Bool (x == y)
  return if flag then x else y

def boolBindCustomBind (x y : UInt64) : UInt64 :=
  @Bind.bind Id ⟨fun value next => next value⟩ Bool UInt64 (pure (x == y))
    (fun flag => if flag then x else y)

def boolBindUnusedUnsupported (x y : UInt64) : UInt64 := Id.run do
  let _unused ← pure (toString x == toString y)
  return x + y

def rangeBoolBindUnusedUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused ← pure (toString a == toString seed)
    return .yield (a + 1)

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

def boolChoiceUnsupportedArm (x y : UInt64) : UInt64 :=
  let flag := if true then false else toString x == toString y
  if flag then x else y

def boolChoiceUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := if false then toString x == toString y else true
  x + y

def boolChoiceCustomDecision (x y : UInt64) : UInt64 :=
  let flag := @ite Bool ((x == y) = true)
    (if h : (x == y) = true then .isTrue h else .isFalse h) true false
  if flag then x else y

def rangeBoolChoiceUnsupportedArm (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let flag := if false then toString a == toString seed else true
    return if flag then .yield (a + 1) else .done a

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

def propChoiceUnsupportedArm (x y : UInt64) : UInt64 :=
  let flag := if True then false else toString x == toString y
  if flag then x else y

def propChoiceUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := if False then toString x == toString y else true
  x + y

def propChoiceCustomDecision (x y : UInt64) : UInt64 :=
  let flag := @ite Bool (x < y)
    (if h : x < y then .isTrue h else .isFalse h) true false
  if flag then x else y

def rangePropChoiceUnsupportedArm (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let flag := if False then toString a == toString seed else true
    return if flag then .yield (a + 1) else .done a

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

def boolFnUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := fun flag : Bool => if flag then (toString x).length.toUInt64 else y
  x + y

def boolFnUnsupportedArgument (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => if flag then x else y
  f (toString x == toString y)

def boolFnBooleanResult (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => !flag
  if f (x == y) then x else y

def rangeBoolFnUnusedUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused : Bool → Id (ForInStep UInt64) := fun flag =>
      pure (if flag then .yield ((toString a).length.toUInt64) else .done a)
    return .yield (a + 1)

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

def decideUnsupportedOperand (x y : UInt64) : UInt64 :=
  let flag := decide ((toString x).length.toUInt64 < y)
  if flag then x else y

def decideUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := decide (False ∧ (toString x).length.toUInt64 < y)
  x + y

def decideCustomEvidence (x y : UInt64) : UInt64 :=
  let flag := @Decidable.decide (x < y) (if h : x < y then .isTrue h else .isFalse h)
  if flag then x else y

def rangeDecideUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := decide ((toString a).length.toUInt64 < seed)
    return .yield (a + 1)

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

def boolWordUnsupported (x y : UInt64) : UInt64 := (toString x == toString y).toUInt64

def boolWordUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := (false && (toString x == toString y)).toUInt64
  x + y

def boolWordUnknownHelper (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => !flag
  (f (x == y)).toUInt64

def rangeBoolWordUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := (toString a == toString seed).toUInt64
    return .yield (a + 1)

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

def boolEqUnsupported (x y : UInt64) : UInt64 :=
  ((x == 0) == (toString x == toString y)).toUInt64

def boolEqUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := false == (toString x == toString y)
  x + y

def boolEqCustomInstance (x y : UInt64) : UInt64 :=
  let flag := @BEq.beq Bool ⟨fun _ _ => true⟩ (x == 0) (y == 0)
  if flag then x else y

def rangeBoolEqUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := true != (toString a == toString seed)
    return .yield (a + 1)

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

def boolPropUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  if flag = (toString x == toString y) then x else y

def boolPropInactiveUnsupported (x y : UInt64) : UInt64 :=
  if true = false then (toString x).length.toUInt64 else x + y

def boolPropCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == 0
  @ite UInt64 (flag = flag) (isTrue rfl) x y

def rangeBoolPropUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    if _h : true ≠ false then return .yield (a + 1)
    else return .done ((toString a).length.toUInt64)
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

def localDecideUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  (decide (flag = (toString x == toString y))).toUInt64

def localDecideInactiveUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let _unused := decide ((if true then flag else (toString x == toString y)) = false)
  x + y

def localDecideCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let value := @Decidable.decide (flag = flag) (isTrue rfl)
  if value then x else y

def rangeLocalDecideUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := decide ((a == seed) ≠ (toString a == toString seed))
    return .yield (a + 1)
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

def relationChoiceUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  (if flag = (toString x == toString y) then flag else !flag).toUInt64

def relationChoiceInactiveUnsupported (x y : UInt64) : UInt64 :=
  let _unused := if true ≠ false then true else toString x == toString y
  x + y

def relationChoiceCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let value := @ite Bool (flag = flag) (isTrue rfl) flag (!flag)
  value.toUInt64 + y

def rangeRelationChoiceUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := if (a == seed) ≠ false then true else toString a == toString seed
    return .yield (a + 1)
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

def dependentChoiceUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  (if _h : flag = (toString x == toString y) then flag else !flag).toUInt64

def dependentChoiceInactiveUnsupported (x y : UInt64) : UInt64 :=
  let _unused := if _h : true ≠ false then true else toString x == toString y
  x + y

def dependentChoiceCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let value := @dite Bool (flag = flag) (isTrue rfl) (fun _ => flag) (fun _ => !flag)
  value.toUInt64 + y

def rangeDependentChoiceUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := if _h : (a == seed) ≠ false then true else toString a == toString seed
    return .yield (a + 1)
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

def boolLetUnsupportedBound (x y : UInt64) : UInt64 :=
  (let _unused := toString x == toString y; true).toUInt64

def boolLetUnsupportedBody (x y : UInt64) : UInt64 :=
  let _unused := (let flag := x == 0; if flag then true else toString x == toString y)
  x + y

def rangeBoolLetUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := (let _flag := toString a == toString seed; false)
    return .yield (a + 1)
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

def boolWordLetUnsupportedBound (x y : UInt64) : UInt64 :=
  (let _word := UInt64.ofNat (toString x).length; true).toUInt64 + y

def boolWordLetUnsupportedBody (x y : UInt64) : UInt64 :=
  let _unused := (let word := x + y; if word == 0 then true else toString word == toString y)
  x + y

def boolWordLetUnsupportedType (x y : UInt64) : UInt64 :=
  (let number := x.toNat; number == y.toNat).toUInt64

def rangeBoolWordLetUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := (let _word := UInt64.ofNat (toString a).length; false)
    return .yield (a + 1)
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

def annotatedLetUnsupportedBound (x y : UInt64) : UInt64 :=
  (let _flag : Id (Id Bool) := toString x == toString y; true).toUInt64

def annotatedLetUnsupportedBody (x y : UInt64) : UInt64 :=
  let _unused := (let value : Id UInt64 := x + y
                 if Id.run value == 0 then true else toString x == toString y)
  x + y

def annotatedLetUnsupportedType (x y : UInt64) : UInt64 :=
  (let number : Id Nat := x.toNat; Id.run number == y.toNat).toUInt64

def rangeAnnotatedLetUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := (let _value : Id UInt64 := UInt64.ofNat (toString a).length; false)
    return .yield (a + 1)
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

def nestedIdUnsupportedBound (x y : UInt64) : UInt64 :=
  (let _flag := Id.run (pure (toString x == toString y)) && x != 0; true).toUInt64

def nestedIdUnsupportedBody (x y : UInt64) : UInt64 :=
  (Id.run (pure (toString x == toString y)) || x == 0).toUInt64

def nestedIdUnsupportedType (x y : UInt64) : UInt64 :=
  (Id.run (pure x.toNat) == y.toNat).toUInt64

def rangeNestedIdUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := Id.run (pure (toString a == toString seed)) && a != 0
    return .yield (a + 1)
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

def idLetUnsupportedBound (x y : UInt64) : UInt64 :=
  let _value : Id UInt64 := UInt64.ofNat (toString x).length
  x + y

def idLetUnsupportedBoolean (x y : UInt64) : UInt64 :=
  let _flag : Id Bool := toString x == toString y
  x + y

def idLetUnsupportedType (x y : UInt64) : UInt64 :=
  let _text : Id String := toString x
  x + y

def rangeIdLetUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _flag : Id Bool := toString a == toString seed
    return .yield (a + 1)
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

def idArithmeticCustom (x y : UInt64) : UInt64 :=
  @HAdd.hAdd (Id UInt64) UInt64 UInt64
    { hAdd := fun a b => Id.run a + b + 1 } x y

def idArithmeticUnsupported (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := UInt64.ofNat (toString x).length
  @HAdd.hAdd (Id UInt64) UInt64 UInt64 (@instHAdd UInt64 instAddUInt64) a y

def idArithmeticNat (x y : UInt64) : UInt64 :=
  let a : Id Nat := x.toNat
  UInt64.ofNat (@HAdd.hAdd (Id Nat) Nat Nat (@instHAdd Nat instAddNat) a y.toNat)

def rangeIdArithmeticCustom (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    return .yield (@HAdd.hAdd (Id UInt64) UInt64 UInt64
      { hAdd := fun a b => Id.run a + b + 1 } a (UInt64.ofNat i))
def binaryRangeHelper (x : UInt64) : UInt64 := x + 1

def rangeBinaryUnsupported (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => binaryRangeHelper x + y
    a := a + UInt64.ofNat i
  return a

def rangeBinaryPartial (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + y
    let g := f a
    a := g (UInt64.ofNat i)
  return a

def helper (x : UInt64) : UInt64 := expression x 3
def wrongType (x : Nat) : Nat := x + 1
def retain (x : UInt64) : UInt64 := x + 1
@[instance_reducible] def custom : HAdd UInt64 UInt64 UInt64 := ⟨UInt64.sub⟩
def customAdd (x y : UInt64) : UInt64 := @HAdd.hAdd _ _ _ custom x y

@[instance_reducible] def reversedLT : LT UInt64 := ⟨fun x y => y < x⟩
@[instance_reducible] def neverEqual : BEq UInt64 := ⟨fun _ _ => false⟩
def customOrder (x y : UInt64) : UInt64 :=
  if @LT.lt UInt64 reversedLT x y then x else y
def customEquality (x y : UInt64) : UInt64 :=
  if @BEq.beq UInt64 neverEqual x y then x else y
def customDecision (x y : UInt64) : Decidable (x = y) := inferInstance
def customDecisionBranch (x y : UInt64) : UInt64 := @ite UInt64 (x = y) (customDecision x y) x y
def rangeCustomOrder (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    if @LT.lt UInt64 reversedLT a (UInt64.ofNat i) then a := a + 1
  return a

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

def rangeUnusedStepValue (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun _ a =>
    let _bad : ForInStep UInt64 := .done (expression a seed)
    .yield (a + 1)

def rangeUnusedStepBind (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun _ a => do
    let _bad ← pure (ForInStep.done (expression a seed))
    return .yield (a + 1)

def rangeCustomStepPure (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun _ a =>
    @Pure.pure Id customPure (ForInStep UInt64)
      (if a < 7 then .done a else .yield (a + 1))

def rangeCustomStepBind (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun _ a =>
    @Bind.bind Id customBind (ForInStep UInt64) (ForInStep UInt64)
      (pure (.done a)) (fun result => pure result)

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

def rangeUnsupportedResultFunction (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun _ a =>
    let _bad : ForInStep UInt64 → ForInStep UInt64 := fun _ => .done (expression a seed)
    .yield (a + 1)

def rangeResultFunctionScalar (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun _ a =>
    let _bad : ForInStep UInt64 → UInt64 := fun _ => a + 1
    .yield (a + 1)

def rangeResultFunctionBool (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun _ a =>
    let _bad : Bool → ForInStep UInt64 := fun _ => .done a
    .yield (a + 1)

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

def customNegatedDecision (x y : UInt64) : Decidable (¬ x < y) := inferInstance
def customNegated (x y : UInt64) : UInt64 := @ite UInt64 (¬ x < y) (customNegatedDecision x y) x y
def customNeDecision (x y : UInt64) : Decidable (x ≠ y) := inferInstance
def customNe (x y : UInt64) : UInt64 := @ite UInt64 (x ≠ y) (customNeDecision x y) x y

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

def idComparisonCustomDecision (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq (Id UInt64) x y) ((fun d : Decidable (x = y) => d) (instDecidableEqUInt64 x y)) (x + 1) (y + 3)

def idComparisonCustomOrder (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LT.lt (Id UInt64) { lt := fun a b => a = b } x y)
    (instDecidableEqUInt64 x y) (x + 1) (y + 3)

def idComparisonUnsupported (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq (Id UInt64) (UInt64.ofNat (toString x).length) y)
    (instDecidableEqUInt64 (UInt64.ofNat (toString x).length) y) (x + 1) (y + 3)

def rangeIdComparisonUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64)) (@Eq (Id UInt64) (UInt64.ofNat (toString i).length) a)
      (instDecidableEqUInt64 (UInt64.ofNat (toString i).length) a)
      (pure (.done a)) (pure (.yield (a + 1)))

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


end ArithmeticModeTest

run_elab do
  let env ← Lean.getEnv
  for name in [`ArithmeticModeTest.expression, `ArithmeticModeTest.bits, `ArithmeticModeTest.literal,
      `ArithmeticModeTest.binding, `ArithmeticModeTest.branch, `ArithmeticModeTest.sequential,
      `ArithmeticModeTest.customBinding, `ArithmeticModeTest.joinedChoice,
      `ArithmeticModeTest.range, `ArithmeticModeTest.rangeLocal,
      `ArithmeticModeTest.rangeBind, `ArithmeticModeTest.rangeJoined,
      `ArithmeticModeTest.rangeBreak, `ArithmeticModeTest.rangeBindBreak, `ArithmeticModeTest.rangeUnusedDone, `ArithmeticModeTest.rangeDirect, `ArithmeticModeTest.rangeNatLiteral,
      `ArithmeticModeTest.rangeStepRun, `ArithmeticModeTest.rangeStepPure, `ArithmeticModeTest.rangeStepLet, `ArithmeticModeTest.rangeStepCapture, `ArithmeticModeTest.rangeStepBind, `ArithmeticModeTest.rangeStepIdLet, `ArithmeticModeTest.rangeStepUnused, `ArithmeticModeTest.rangeStepWrappedBind,
      `ArithmeticModeTest.rangeStepJoined, `ArithmeticModeTest.rangeResultFunction, `ArithmeticModeTest.rangeResultChained, `ArithmeticModeTest.rangeResultCapture, `ArithmeticModeTest.rangeResultUnused, `ArithmeticModeTest.rangeResultWrapped,
      `ArithmeticModeTest.compareNe, `ArithmeticModeTest.negatedEq, `ArithmeticModeTest.negatedLt, `ArithmeticModeTest.negatedLe, `ArithmeticModeTest.negatedGt, `ArithmeticModeTest.negatedGe, `ArithmeticModeTest.negatedBool, `ArithmeticModeTest.doubleNegation, `ArithmeticModeTest.negatedBindings, `ArithmeticModeTest.rangeNegatedBreak, `ArithmeticModeTest.rangeNegatedContinue, `ArithmeticModeTest.rangeNegatedJoin,
      `ArithmeticModeTest.rangeFromOne,
      `ArithmeticModeTest.rangeIntervalLiteral,
      `ArithmeticModeTest.rangeIntervalEmpty,
      `ArithmeticModeTest.rangeIntervalEqual,
      `ArithmeticModeTest.rangeIntervalBreak,
      `ArithmeticModeTest.rangeIntervalContinue,
      `ArithmeticModeTest.rangeIntervalCapture,
      `ArithmeticModeTest.rangeIntervalJoin,
      `ArithmeticModeTest.rangeIntervalHigh,
      `ArithmeticModeTest.rangeIntervalMaxEmpty,
      `ArithmeticModeTest.rangeIntervalHugeBreak, `ArithmeticModeTest.intervalDynamic,
      `ArithmeticModeTest.rangeDynamicStart,
      `ArithmeticModeTest.rangeDynamicLiteral,
      `ArithmeticModeTest.rangeDynamicComputed,
      `ArithmeticModeTest.rangeDynamicCapture,
      `ArithmeticModeTest.rangeDynamicHigh,
      `ArithmeticModeTest.rangeDynamicEmpty,
      `ArithmeticModeTest.rangeDynamicEqual,
      `ArithmeticModeTest.rangeDynamicHugeBreak,
      `ArithmeticModeTest.rangeDynamicContinue,
      `ArithmeticModeTest.rangeDynamicJoin,
      `ArithmeticModeTest.rangeDynamicChoice, `ArithmeticModeTest.rangeNonUnitStep,
      `ArithmeticModeTest.rangeStrideTwo,
      `ArithmeticModeTest.rangeStrideLiteral,
      `ArithmeticModeTest.rangeStrideDynamic,
      `ArithmeticModeTest.rangeStrideCapture,
      `ArithmeticModeTest.rangeStrideHigh,
      `ArithmeticModeTest.rangeStrideEmpty,
      `ArithmeticModeTest.rangeStrideHuge,
      `ArithmeticModeTest.rangeStrideHugeTwo,
      `ArithmeticModeTest.rangeStrideHugeBreak,
      `ArithmeticModeTest.rangeStrideContinue,
      `ArithmeticModeTest.rangeStrideJoin,
      `ArithmeticModeTest.rangeStrideOne, `ArithmeticModeTest.binaryLocalFunction, `ArithmeticModeTest.rangeBinaryFunction,
      `ArithmeticModeTest.binaryOrder,
      `ArithmeticModeTest.binaryCapture,
      `ArithmeticModeTest.binaryChained,
      `ArithmeticModeTest.binaryUnused,
      `ArithmeticModeTest.binaryDo,
      `ArithmeticModeTest.binaryNested,
      `ArithmeticModeTest.binaryChoice,
      `ArithmeticModeTest.binaryArguments,
      `ArithmeticModeTest.binaryWrapped,
      `ArithmeticModeTest.rangeBinaryLocal,
      `ArithmeticModeTest.rangeBinaryCapture,
      `ArithmeticModeTest.rangeBinaryNested,
      `ArithmeticModeTest.rangeBinaryDo,
      `ArithmeticModeTest.rangeBinaryContinue,
      `ArithmeticModeTest.rangeBinaryUnused,
      `ArithmeticModeTest.rangeBinaryStep,
      `ArithmeticModeTest.rangeBinaryStepOrder,
      `ArithmeticModeTest.rangeBinaryStepCapture,
      `ArithmeticModeTest.rangeBinaryStepChained,
      `ArithmeticModeTest.rangeBinaryStepNested,
      `ArithmeticModeTest.rangeBinaryStepDo,
      `ArithmeticModeTest.rangeBinaryStepScalar,
      `ArithmeticModeTest.rangeBinaryStepUnused,
      `ArithmeticModeTest.rangeBinaryStepResult,
      `ArithmeticModeTest.rangeBinaryStepWrapped,
      `ArithmeticModeTest.boolNotEqual,
      `ArithmeticModeTest.boolNotUnequal,
      `ArithmeticModeTest.boolNotTwice,
      `ArithmeticModeTest.boolNotThrice,
      `ArithmeticModeTest.boolNotNested,
      `ArithmeticModeTest.boolNotFunction,
      `ArithmeticModeTest.boolNotDo,
      `ArithmeticModeTest.boolNotProposition,
      `ArithmeticModeTest.rangeBoolNotBreak,
      `ArithmeticModeTest.rangeBoolNotContinue,
      `ArithmeticModeTest.rangeBoolNotJoin,
      `ArithmeticModeTest.rangeBoolNotFunction,
      `ArithmeticModeTest.rangeOuterUnary,
      `ArithmeticModeTest.rangeOuterBinary,
      `ArithmeticModeTest.rangeOuterUnit,
      `ArithmeticModeTest.rangeOuterCapture,
      `ArithmeticModeTest.rangeOuterBounds,
      `ArithmeticModeTest.rangeOuterChained,
      `ArithmeticModeTest.rangeOuterNested,
      `ArithmeticModeTest.rangeOuterDo,
      `ArithmeticModeTest.rangeOuterUnused,
      `ArithmeticModeTest.rangeOuterStep,
      `ArithmeticModeTest.rangeLetResult,
      `ArithmeticModeTest.rangeLetDirect,
      `ArithmeticModeTest.rangeLetCapture,
      `ArithmeticModeTest.rangeLetAliases,
      `ArithmeticModeTest.rangeLetUnused,
      `ArithmeticModeTest.rangeLetStride,
      `ArithmeticModeTest.rangeLetContinue,
      `ArithmeticModeTest.rangeLetMonadic,
      `ArithmeticModeTest.rangeLetHelper,
      `ArithmeticModeTest.rangeLetNested,
      `ArithmeticModeTest.complementDirect,
      `ArithmeticModeTest.complementOperator,
      `ArithmeticModeTest.complementTwice,
      `ArithmeticModeTest.complementMixed,
      `ArithmeticModeTest.complementChoice,
      `ArithmeticModeTest.complementFunction,
      `ArithmeticModeTest.complementDo,
      `ArithmeticModeTest.complementOperand,
      `ArithmeticModeTest.rangeComplement,
      `ArithmeticModeTest.rangeComplementContinue,
      `ArithmeticModeTest.rangeComplementHelper,
      `ArithmeticModeTest.rangeComplementStep,
      `ArithmeticModeTest.compoundAnd,
      `ArithmeticModeTest.compoundOr,
      `ArithmeticModeTest.compoundNested,
      `ArithmeticModeTest.compoundNegatedLeaves,
      `ArithmeticModeTest.compoundZeroDivisor,
      `ArithmeticModeTest.compoundFunction,
      `ArithmeticModeTest.compoundDo,
      `ArithmeticModeTest.compoundOperand,
      `ArithmeticModeTest.rangeCompoundBreak,
      `ArithmeticModeTest.rangeCompoundContinue,
      `ArithmeticModeTest.rangeCompoundJoined,
      `ArithmeticModeTest.rangeCompoundHelper,
      `ArithmeticModeTest.rangeCompoundStep,
      `ArithmeticModeTest.rangeCompoundResult,
      `ArithmeticModeTest.compoundNotAnd,
      `ArithmeticModeTest.compoundNotOr,
      `ArithmeticModeTest.compoundNotTwice,
      `ArithmeticModeTest.compoundNotThrice,
      `ArithmeticModeTest.compoundNotNested,
      `ArithmeticModeTest.compoundNotFunction,
      `ArithmeticModeTest.compoundNotDo,
      `ArithmeticModeTest.compoundNotOperand,
      `ArithmeticModeTest.rangeCompoundNotBreak,
      `ArithmeticModeTest.rangeCompoundNotContinue,
      `ArithmeticModeTest.rangeCompoundNotJoined,
      `ArithmeticModeTest.rangeCompoundNotStep,
      `ArithmeticModeTest.boolAndTruth,
      `ArithmeticModeTest.boolOrTruth,
      `ArithmeticModeTest.boolCompoundNot,
      `ArithmeticModeTest.boolCompoundTwice,
      `ArithmeticModeTest.boolCompoundNested,
      `ArithmeticModeTest.boolCompoundFunction,
      `ArithmeticModeTest.boolCompoundDo,
      `ArithmeticModeTest.boolCompoundOperand,
      `ArithmeticModeTest.rangeBoolCompoundBreak,
      `ArithmeticModeTest.rangeBoolCompoundContinue,
      `ArithmeticModeTest.rangeBoolCompoundJoined,
      `ArithmeticModeTest.rangeBoolCompoundStep,
      `ArithmeticModeTest.mixedGuardAnd,
      `ArithmeticModeTest.mixedGuardOr,
      `ArithmeticModeTest.mixedGuardNot,
      `ArithmeticModeTest.mixedGuardNegations,
      `ArithmeticModeTest.mixedGuardNested,
      `ArithmeticModeTest.mixedGuardFunction,
      `ArithmeticModeTest.mixedGuardDo,
      `ArithmeticModeTest.mixedGuardOperand,
      `ArithmeticModeTest.rangeMixedGuardBreak,
      `ArithmeticModeTest.rangeMixedGuardContinue,
      `ArithmeticModeTest.rangeMixedGuardJoined,
      `ArithmeticModeTest.rangeMixedGuardStep,
      `ArithmeticModeTest.minimumOrder,
      `ArithmeticModeTest.maximumOrder,
      `ArithmeticModeTest.extremaNested,
      `ArithmeticModeTest.extremaClamped,
      `ArithmeticModeTest.extremaFunction,
      `ArithmeticModeTest.extremaDo,
      `ArithmeticModeTest.extremaGuard,
      `ArithmeticModeTest.extremaWrapped,
      `ArithmeticModeTest.rangeExtremaCount,
      `ArithmeticModeTest.rangeExtremaExit,
      `ArithmeticModeTest.rangeExtremaBounds,
      `ArithmeticModeTest.rangeExtremaStep,
      `ArithmeticModeTest.literalBoolTrue,
      `ArithmeticModeTest.literalBoolFalse,
      `ArithmeticModeTest.literalPropTrue,
      `ArithmeticModeTest.literalPropFalse,
      `ArithmeticModeTest.literalNegations,
      `ArithmeticModeTest.literalCompound,
      `ArithmeticModeTest.literalFunction,
      `ArithmeticModeTest.literalDo,
      `ArithmeticModeTest.rangeLiteralBreak,
      `ArithmeticModeTest.rangeLiteralContinue,
      `ArithmeticModeTest.rangeLiteralJoined,
      `ArithmeticModeTest.rangeLiteralStep,
      `ArithmeticModeTest.punitExplicit,
      `ArithmeticModeTest.punitCapture,
      `ArithmeticModeTest.punitChain,
      `ArithmeticModeTest.punitUnused,
      `ArithmeticModeTest.punitDo,
      `ArithmeticModeTest.punitNested,
      `ArithmeticModeTest.rangePUnitJoined,
      `ArithmeticModeTest.rangePUnitStep,
      `ArithmeticModeTest.rangePUnitScalar,
      `ArithmeticModeTest.rangePUnitYield,
      `ArithmeticModeTest.rangePUnitOuter,
      `ArithmeticModeTest.rangePUnitStride,
      `ArithmeticModeTest.idReturnedHelper,
      `ArithmeticModeTest.idPureNested,
      `ArithmeticModeTest.idRunNested,
      `ArithmeticModeTest.idBindInput,
      `ArithmeticModeTest.idBindOutput,
      `ArithmeticModeTest.idConditional,
      `ArithmeticModeTest.idFunctions,
      `ArithmeticModeTest.idUnused,
      `ArithmeticModeTest.rangeIdWrapped,
      `ArithmeticModeTest.rangeIdBindLeft,
      `ArithmeticModeTest.rangeIdBindRight,
      `ArithmeticModeTest.rangeIdStepHelper,
      `ArithmeticModeTest.manyOrder,
      `ArithmeticModeTest.manyFour,
      `ArithmeticModeTest.manySix,
      `ArithmeticModeTest.manyCapture,
      `ArithmeticModeTest.manyChained,
      `ArithmeticModeTest.manyDo,
      `ArithmeticModeTest.manyId,
      `ArithmeticModeTest.manyUnused,
      `ArithmeticModeTest.rangeManyStep,
      `ArithmeticModeTest.rangeManyOuter,
      `ArithmeticModeTest.rangeManyYield,
      `ArithmeticModeTest.rangeManyStride,
      `ArithmeticModeTest.rangeManyGuard,
      `ArithmeticModeTest.rangeManyResult,
      `ArithmeticModeTest.rangeOuterThree,
      `ArithmeticModeTest.stepManyOrder,
      `ArithmeticModeTest.stepManyFour,
      `ArithmeticModeTest.stepManySix,
      `ArithmeticModeTest.stepManyCapture,
      `ArithmeticModeTest.stepManyChained,
      `ArithmeticModeTest.stepManyNested,
      `ArithmeticModeTest.stepManyBind,
      `ArithmeticModeTest.stepManyScalarMix,
      `ArithmeticModeTest.stepManyUnused,
      `ArithmeticModeTest.stepManyWrapped,
      `ArithmeticModeTest.dependentCompare,
      `ArithmeticModeTest.dependentMixed,
      `ArithmeticModeTest.dependentLiteral,
      `ArithmeticModeTest.dependentNested,
      `ArithmeticModeTest.dependentCapture,
      `ArithmeticModeTest.dependentDo,
      `ArithmeticModeTest.dependentOperand,
      `ArithmeticModeTest.dependentMany,
      `ArithmeticModeTest.rangeDependentYield,
      `ArithmeticModeTest.rangeDependentBreak,
      `ArithmeticModeTest.rangeDependentContinue,
      `ArithmeticModeTest.rangeDependentJoined,
      `ArithmeticModeTest.rangeDependentStep,
      `ArithmeticModeTest.rangeDependentResult,
      `ArithmeticModeTest.rangeDependentBounds,
      `ArithmeticModeTest.rangeDependentOuter,
      `ArithmeticModeTest.booleanLet,
      `ArithmeticModeTest.booleanAlias,
      `ArithmeticModeTest.booleanShadow,
      `ArithmeticModeTest.booleanCompound,
      `ArithmeticModeTest.booleanNestedOperand,
      `ArithmeticModeTest.booleanUnused,
      `ArithmeticModeTest.booleanMany,
      `ArithmeticModeTest.booleanDo,
      `ArithmeticModeTest.rangeBooleanYield,
      `ArithmeticModeTest.rangeBooleanBreak,
      `ArithmeticModeTest.rangeBooleanContinue,
      `ArithmeticModeTest.rangeBooleanCapture,
      `ArithmeticModeTest.rangeBooleanJoined,
      `ArithmeticModeTest.rangeBooleanOuter,
      `ArithmeticModeTest.rangeBooleanBounds,
      `ArithmeticModeTest.rangeBooleanStep,
      `ArithmeticModeTest.booleanDependentLet,
      `ArithmeticModeTest.booleanDependentAlias,
      `ArithmeticModeTest.booleanDependentShadow,
      `ArithmeticModeTest.booleanDependentCompound,
      `ArithmeticModeTest.booleanDependentNestedOperand,
      `ArithmeticModeTest.booleanDependentUnused,
      `ArithmeticModeTest.booleanDependentMany,
      `ArithmeticModeTest.booleanDependentDo,
      `ArithmeticModeTest.rangeBooleanDependentYield,
      `ArithmeticModeTest.rangeBooleanDependentBreak,
      `ArithmeticModeTest.rangeBooleanDependentContinue,
      `ArithmeticModeTest.rangeBooleanDependentCapture,
      `ArithmeticModeTest.rangeBooleanDependentJoined,
      `ArithmeticModeTest.rangeBooleanDependentOuter,
      `ArithmeticModeTest.rangeBooleanDependentBounds,
      `ArithmeticModeTest.rangeBooleanDependentStep,
      `ArithmeticModeTest.instanceDependentMany,
      `ArithmeticModeTest.instanceLet,
      `ArithmeticModeTest.instanceApplied,
      `ArithmeticModeTest.instanceNested,
      `ArithmeticModeTest.instanceShadow,
      `ArithmeticModeTest.instanceProof,
      `ArithmeticModeTest.instanceOverflow,
      `ArithmeticModeTest.instanceDo,
      `ArithmeticModeTest.rangeInstanceStep,
      `ArithmeticModeTest.rangeInstanceBreak,
      `ArithmeticModeTest.rangeInstanceBounds,
      `ArithmeticModeTest.rangeInstanceOuter,
      `ArithmeticModeTest.naturalConverted,
      `ArithmeticModeTest.naturalConvertedOverflow,
      `ArithmeticModeTest.naturalExplicitLet,
      `ArithmeticModeTest.naturalExplicitApplied,
      `ArithmeticModeTest.naturalExplicitNested,
      `ArithmeticModeTest.naturalDependentMany,
      `ArithmeticModeTest.naturalDo,
      `ArithmeticModeTest.naturalOperand,
      `ArithmeticModeTest.rangeNaturalStep,
      `ArithmeticModeTest.rangeNaturalBounds,
      `ArithmeticModeTest.rangeNaturalConversion,
      `ArithmeticModeTest.rangeNaturalOuter,
      `ArithmeticModeTest.boolBindLet,
      `ArithmeticModeTest.boolBindAlias,
      `ArithmeticModeTest.boolBindWrapped,
      `ArithmeticModeTest.boolBindShadow,
      `ArithmeticModeTest.boolBindCapture,
      `ArithmeticModeTest.boolBindDependent,
      `ArithmeticModeTest.boolBindDo,
      `ArithmeticModeTest.boolBindUnused,
      `ArithmeticModeTest.rangeBoolBindYield,
      `ArithmeticModeTest.rangeBoolBindBreak,
      `ArithmeticModeTest.rangeBoolBindContinue,
      `ArithmeticModeTest.rangeBoolBindJoined,
      `ArithmeticModeTest.rangeBoolBindCapture,
      `ArithmeticModeTest.rangeBoolBindBounds,
      `ArithmeticModeTest.rangeBoolBindStep,
      `ArithmeticModeTest.rangeBoolBindOuter,
      `ArithmeticModeTest.boolChoiceLet,
      `ArithmeticModeTest.boolChoiceNested,
      `ArithmeticModeTest.boolChoiceClosed,
      `ArithmeticModeTest.boolChoiceShadow,
      `ArithmeticModeTest.boolChoiceCapture,
      `ArithmeticModeTest.boolChoiceDependent,
      `ArithmeticModeTest.boolChoiceDo,
      `ArithmeticModeTest.boolChoiceUnused,
      `ArithmeticModeTest.rangeBoolChoiceYield,
      `ArithmeticModeTest.rangeBoolChoiceBreak,
      `ArithmeticModeTest.rangeBoolChoiceContinue,
      `ArithmeticModeTest.rangeBoolChoiceJoined,
      `ArithmeticModeTest.rangeBoolChoiceCapture,
      `ArithmeticModeTest.rangeBoolChoiceBounds,
      `ArithmeticModeTest.rangeBoolChoiceStep,
      `ArithmeticModeTest.rangeBoolChoiceOuter,
      `ArithmeticModeTest.propChoiceLet,
      `ArithmeticModeTest.propChoiceNested,
      `ArithmeticModeTest.propChoiceClosed,
      `ArithmeticModeTest.propChoiceShadow,
      `ArithmeticModeTest.propChoiceCapture,
      `ArithmeticModeTest.propChoiceDependent,
      `ArithmeticModeTest.propChoiceDo,
      `ArithmeticModeTest.propChoiceUnused,
      `ArithmeticModeTest.rangePropChoiceYield,
      `ArithmeticModeTest.rangePropChoiceBreak,
      `ArithmeticModeTest.rangePropChoiceContinue,
      `ArithmeticModeTest.rangePropChoiceJoined,
      `ArithmeticModeTest.rangePropChoiceCapture,
      `ArithmeticModeTest.rangePropChoiceBounds,
      `ArithmeticModeTest.rangePropChoiceStep,
      `ArithmeticModeTest.rangePropChoiceOuter,
      `ArithmeticModeTest.boolFnConditional,
      `ArithmeticModeTest.boolFnLocalGuard,
      `ArithmeticModeTest.boolFnNested,
      `ArithmeticModeTest.boolFnDirect,
      `ArithmeticModeTest.boolFnShadow,
      `ArithmeticModeTest.boolFnCapture,
      `ArithmeticModeTest.boolFnAnnotation,
      `ArithmeticModeTest.boolFnUnused,
      `ArithmeticModeTest.rangeBoolFnYield,
      `ArithmeticModeTest.rangeBoolFnBreak,
      `ArithmeticModeTest.rangeBoolFnContinue,
      `ArithmeticModeTest.rangeBoolFnJoined,
      `ArithmeticModeTest.rangeBoolFnCapture,
      `ArithmeticModeTest.rangeBoolFnBounds,
      `ArithmeticModeTest.rangeBoolFnStep,
      `ArithmeticModeTest.rangeBoolFnOuter,
      `ArithmeticModeTest.rangeResultFunctionBool,
      `ArithmeticModeTest.decideLet,
      `ArithmeticModeTest.decideImplicit,
      `ArithmeticModeTest.decideCompound,
      `ArithmeticModeTest.decideBoolean,
      `ArithmeticModeTest.decideChoices,
      `ArithmeticModeTest.decideCapture,
      `ArithmeticModeTest.decideDo,
      `ArithmeticModeTest.decideUnused,
      `ArithmeticModeTest.rangeDecideYield,
      `ArithmeticModeTest.rangeDecideBreak,
      `ArithmeticModeTest.rangeDecideContinue,
      `ArithmeticModeTest.rangeDecideJoined,
      `ArithmeticModeTest.rangeDecideCapture,
      `ArithmeticModeTest.rangeDecideBounds,
      `ArithmeticModeTest.rangeDecideStep,
      `ArithmeticModeTest.rangeDecideOuter,
      `ArithmeticModeTest.boolWordDirect,
      `ArithmeticModeTest.boolWordCaptured,
      `ArithmeticModeTest.boolWordAction,
      `ArithmeticModeTest.boolWordLiterals,
      `ArithmeticModeTest.boolWordChoice,
      `ArithmeticModeTest.boolWordNested,
      `ArithmeticModeTest.boolWordDependent,
      `ArithmeticModeTest.boolWordUnused,
      `ArithmeticModeTest.rangeBoolWordYield,
      `ArithmeticModeTest.rangeBoolWordBreak,
      `ArithmeticModeTest.rangeBoolWordContinue,
      `ArithmeticModeTest.rangeBoolWordJoined,
      `ArithmeticModeTest.rangeBoolWordCapture,
      `ArithmeticModeTest.rangeBoolWordBounds,
      `ArithmeticModeTest.rangeBoolWordStep,
      `ArithmeticModeTest.rangeBoolWordOuter,
      `ArithmeticModeTest.boolEqDirect,
      `ArithmeticModeTest.boolEqCalls,
      `ArithmeticModeTest.boolEqConditional,
      `ArithmeticModeTest.boolEqCapture,
      `ArithmeticModeTest.boolEqLiterals,
      `ArithmeticModeTest.boolEqChoices,
      `ArithmeticModeTest.boolEqNested,
      `ArithmeticModeTest.boolEqDo,
      `ArithmeticModeTest.rangeBoolEqYield,
      `ArithmeticModeTest.rangeBoolEqBreak,
      `ArithmeticModeTest.rangeBoolEqContinue,
      `ArithmeticModeTest.rangeBoolEqJoined,
      `ArithmeticModeTest.rangeBoolEqCapture,
      `ArithmeticModeTest.rangeBoolEqBounds,
      `ArithmeticModeTest.rangeBoolEqStep,
      `ArithmeticModeTest.rangeBoolEqOuter,
      `ArithmeticModeTest.boolPropEqual,
      `ArithmeticModeTest.boolPropUnequal,
      `ArithmeticModeTest.boolPropLiterals,
      `ArithmeticModeTest.boolPropDependent,
      `ArithmeticModeTest.boolPropTruth,
      `ArithmeticModeTest.boolPropChoices,
      `ArithmeticModeTest.boolPropDo,
      `ArithmeticModeTest.boolPropEarly,
      `ArithmeticModeTest.rangeBoolPropYield,
      `ArithmeticModeTest.rangeBoolPropBreak,
      `ArithmeticModeTest.rangeBoolPropContinue,
      `ArithmeticModeTest.rangeBoolPropJoined,
      `ArithmeticModeTest.rangeBoolPropCapture,
      `ArithmeticModeTest.rangeBoolPropBounds,
      `ArithmeticModeTest.rangeBoolPropStep,
      `ArithmeticModeTest.rangeBoolPropOuter,
      `ArithmeticModeTest.localDecideEqual,
      `ArithmeticModeTest.localDecideTruth,
      `ArithmeticModeTest.localDecideImplicit,
      `ArithmeticModeTest.localDecideNested,
      `ArithmeticModeTest.localDecideLiterals,
      `ArithmeticModeTest.localDecideCapture,
      `ArithmeticModeTest.localDecideDo,
      `ArithmeticModeTest.localDecideChoices,
      `ArithmeticModeTest.rangeLocalDecideYield,
      `ArithmeticModeTest.rangeLocalDecideJoined,
      `ArithmeticModeTest.rangeLocalDecideContinue,
      `ArithmeticModeTest.rangeLocalDecideCapture,
      `ArithmeticModeTest.rangeLocalDecideBounds,
      `ArithmeticModeTest.rangeLocalDecideStep,
      `ArithmeticModeTest.rangeLocalDecideOuter,
      `ArithmeticModeTest.rangeLocalDecideUnused,
      `ArithmeticModeTest.relationChoiceEqual,
      `ArithmeticModeTest.relationChoiceUnequal,
      `ArithmeticModeTest.relationChoiceNested,
      `ArithmeticModeTest.relationChoiceCapture,
      `ArithmeticModeTest.relationChoiceLiterals,
      `ArithmeticModeTest.relationChoiceDo,
      `ArithmeticModeTest.relationChoiceTruth,
      `ArithmeticModeTest.relationChoiceUnused,
      `ArithmeticModeTest.rangeRelationChoiceYield,
      `ArithmeticModeTest.rangeRelationChoiceJoined,
      `ArithmeticModeTest.rangeRelationChoiceContinue,
      `ArithmeticModeTest.rangeRelationChoiceCapture,
      `ArithmeticModeTest.rangeRelationChoiceBounds,
      `ArithmeticModeTest.rangeRelationChoiceStep,
      `ArithmeticModeTest.rangeRelationChoiceOuter,
      `ArithmeticModeTest.rangeRelationChoiceUnused,
      `ArithmeticModeTest.dependentChoiceEqual,
      `ArithmeticModeTest.dependentChoiceProposition,
      `ArithmeticModeTest.dependentChoiceNested,
      `ArithmeticModeTest.dependentChoiceCapture,
      `ArithmeticModeTest.dependentChoiceLiterals,
      `ArithmeticModeTest.dependentChoiceDo,
      `ArithmeticModeTest.dependentChoiceTruth,
      `ArithmeticModeTest.dependentChoiceUnused,
      `ArithmeticModeTest.rangeDependentChoiceYield,
      `ArithmeticModeTest.rangeDependentChoiceJoined,
      `ArithmeticModeTest.rangeDependentChoiceContinue,
      `ArithmeticModeTest.rangeDependentChoiceCapture,
      `ArithmeticModeTest.rangeDependentChoiceBounds,
      `ArithmeticModeTest.rangeDependentChoiceStep,
      `ArithmeticModeTest.rangeDependentChoiceOuter,
      `ArithmeticModeTest.rangeDependentChoiceUnused,
      `ArithmeticModeTest.boolLetNested,
      `ArithmeticModeTest.boolLetCapture,
      `ArithmeticModeTest.boolLetShadow,
      `ArithmeticModeTest.boolLetUnused,
      `ArithmeticModeTest.boolLetDependent,
      `ArithmeticModeTest.boolLetHelper,
      `ArithmeticModeTest.boolLetDo,
      `ArithmeticModeTest.boolLetNegated,
      `ArithmeticModeTest.rangeBoolLetYield,
      `ArithmeticModeTest.rangeBoolLetJoined,
      `ArithmeticModeTest.rangeBoolLetContinue,
      `ArithmeticModeTest.rangeBoolLetCapture,
      `ArithmeticModeTest.rangeBoolLetBounds,
      `ArithmeticModeTest.rangeBoolLetStep,
      `ArithmeticModeTest.rangeBoolLetOuter,
      `ArithmeticModeTest.rangeBoolLetUnused,
      `ArithmeticModeTest.boolWordLetOriginal,
      `ArithmeticModeTest.boolWordLetMixed,
      `ArithmeticModeTest.boolWordLetShadow,
      `ArithmeticModeTest.boolWordLetHelper,
      `ArithmeticModeTest.boolWordLetDependent,
      `ArithmeticModeTest.boolWordLetUnused,
      `ArithmeticModeTest.boolWordLetDo,
      `ArithmeticModeTest.boolWordLetNegated,
      `ArithmeticModeTest.rangeBoolWordLetYield,
      `ArithmeticModeTest.rangeBoolWordLetJoined,
      `ArithmeticModeTest.rangeBoolWordLetContinue,
      `ArithmeticModeTest.rangeBoolWordLetCapture,
      `ArithmeticModeTest.rangeBoolWordLetBounds,
      `ArithmeticModeTest.rangeBoolWordLetStep,
      `ArithmeticModeTest.rangeBoolWordLetOuter,
      `ArithmeticModeTest.rangeBoolWordLetUnused,
      `ArithmeticModeTest.annotatedLetBoolean,
      `ArithmeticModeTest.annotatedLetWord,
      `ArithmeticModeTest.annotatedLetNested,
      `ArithmeticModeTest.annotatedLetHelper,
      `ArithmeticModeTest.annotatedLetUnused,
      `ArithmeticModeTest.annotatedLetDo,
      `ArithmeticModeTest.annotatedLetNegated,
      `ArithmeticModeTest.annotatedLetShadow,
      `ArithmeticModeTest.rangeAnnotatedLetYield,
      `ArithmeticModeTest.rangeAnnotatedLetJoined,
      `ArithmeticModeTest.rangeAnnotatedLetContinue,
      `ArithmeticModeTest.rangeAnnotatedLetCapture,
      `ArithmeticModeTest.rangeAnnotatedLetBounds,
      `ArithmeticModeTest.rangeAnnotatedLetStep,
      `ArithmeticModeTest.rangeAnnotatedLetOuter,
      `ArithmeticModeTest.rangeAnnotatedLetUnused,
      `ArithmeticModeTest.nestedIdOperators,
      `ArithmeticModeTest.nestedIdBinding,
      `ArithmeticModeTest.nestedIdNested,
      `ArithmeticModeTest.nestedIdHelper,
      `ArithmeticModeTest.nestedIdDo,
      `ArithmeticModeTest.nestedIdDependent,
      `ArithmeticModeTest.nestedIdUnused,
      `ArithmeticModeTest.nestedIdShadow,
      `ArithmeticModeTest.rangeNestedIdYield,
      `ArithmeticModeTest.rangeNestedIdJoined,
      `ArithmeticModeTest.rangeNestedIdContinue,
      `ArithmeticModeTest.rangeNestedIdCapture,
      `ArithmeticModeTest.rangeNestedIdBounds,
      `ArithmeticModeTest.rangeNestedIdStep,
      `ArithmeticModeTest.rangeNestedIdOuter,
      `ArithmeticModeTest.rangeNestedIdUnused,
      `ArithmeticModeTest.idLetWord,
      `ArithmeticModeTest.idLetBoolean,
      `ArithmeticModeTest.idLetLiteral,
      `ArithmeticModeTest.idLetHelper,
      `ArithmeticModeTest.idLetShadow,
      `ArithmeticModeTest.idLetOverflow,
      `ArithmeticModeTest.idLetUnused,
      `ArithmeticModeTest.idLetDo,
      `ArithmeticModeTest.rangeIdLetYield,
      `ArithmeticModeTest.rangeIdLetJoined,
      `ArithmeticModeTest.rangeIdLetContinue,
      `ArithmeticModeTest.rangeIdLetCapture,
      `ArithmeticModeTest.rangeIdLetBounds,
      `ArithmeticModeTest.rangeIdLetStep,
      `ArithmeticModeTest.rangeIdLetOuter,
      `ArithmeticModeTest.rangeIdLetUnused,
      `ArithmeticModeTest.idArithmeticLeft,
      `ArithmeticModeTest.idArithmeticRight,
      `ArithmeticModeTest.idArithmeticBoth,
      `ArithmeticModeTest.idArithmeticBitwise,
      `ArithmeticModeTest.idArithmeticDivision,
      `ArithmeticModeTest.idArithmeticShifts,
      `ArithmeticModeTest.idArithmeticHelper,
      `ArithmeticModeTest.idArithmeticDo,
      `ArithmeticModeTest.rangeIdArithmeticYield,
      `ArithmeticModeTest.rangeIdArithmeticContinue,
      `ArithmeticModeTest.rangeIdArithmeticBounds,
      `ArithmeticModeTest.rangeIdArithmeticStep,
      `ArithmeticModeTest.idComparisonEq,
      `ArithmeticModeTest.idComparisonNe,
      `ArithmeticModeTest.idComparisonLt,
      `ArithmeticModeTest.idComparisonLe,
      `ArithmeticModeTest.idComparisonGt,
      `ArithmeticModeTest.idComparisonGe,
      `ArithmeticModeTest.rangeIdComparisonExit,
      `ArithmeticModeTest.idComparisonNegated,
      `ArithmeticModeTest.idComparisonCompound,
      `ArithmeticModeTest.idComparisonDependent,
      `ArithmeticModeTest.idComparisonDecide,
      `ArithmeticModeTest.idComparisonChoice,
      `ArithmeticModeTest.idComparisonDo,
      `ArithmeticModeTest.rangeIdComparisonDecide,
      `ArithmeticModeTest.rangeIdComparisonDependent,
      `ArithmeticModeTest.rangeBinaryStepThree] do
    match LeanExe.Extract.Arithmetic.compileEnvironment env `ArithmeticModeTest name with
    | .error message => throwError "arithmetic mode rejected {name}: {message}"
    | .ok module_ =>
      match LeanExe.Extract.Core.compileEnvironment env `ArithmeticModeTest name with
      | .error message => throwError "normal compiler rejected {name}: {message}"
      | .ok normal =>
        unless LeanExe.Wasm.Binary.CoreWasm.moduleBytes module_ ==
            LeanExe.Wasm.Binary.CoreWasm.moduleBytes normal do
          throwError "arithmetic mode changed production bytes for {name}"
  for name in [`ArithmeticModeTest.natBinding,
      `ArithmeticModeTest.rangeIdComparisonEvidenceAnnotations,
      `ArithmeticModeTest.idComparisonCustomDecision,
      `ArithmeticModeTest.idComparisonCustomOrder,
      `ArithmeticModeTest.idComparisonUnsupported,
      `ArithmeticModeTest.rangeIdComparisonUnsupported,

      `ArithmeticModeTest.unsupportedLocalBody,
      `ArithmeticModeTest.rangeTwice,
      `ArithmeticModeTest.rangeUnsupportedFunction,
      `ArithmeticModeTest.rangeCustomBind,
      `ArithmeticModeTest.rangeUnsupportedResultFunction, `ArithmeticModeTest.rangeResultFunctionScalar,
      `ArithmeticModeTest.rangeUnusedStepValue, `ArithmeticModeTest.rangeUnusedStepBind, `ArithmeticModeTest.rangeCustomStepPure, `ArithmeticModeTest.rangeCustomStepBind,
      `ArithmeticModeTest.boolNotCustomBEq, `ArithmeticModeTest.boolNotCustomDecision, `ArithmeticModeTest.boolNotHelper,
      `ArithmeticModeTest.stepManyUnusedUnsupported, `ArithmeticModeTest.stepManyWrongDomain, `ArithmeticModeTest.stepManyPartial, `ArithmeticModeTest.stepManyIgnoredOperand,
      `ArithmeticModeTest.dependentInactiveUnsupported, `ArithmeticModeTest.dependentCustomDecision, `ArithmeticModeTest.dependentUnusedUnsupported, `ArithmeticModeTest.rangeDependentInactiveUnsupported,
      `ArithmeticModeTest.booleanUnusedUnsupported, `ArithmeticModeTest.booleanCustomEquality, `ArithmeticModeTest.booleanIgnoredOperand, `ArithmeticModeTest.rangeBooleanUnusedUnsupported,
      `ArithmeticModeTest.booleanDependentInactiveUnsupported, `ArithmeticModeTest.booleanDependentCustomDecision, `ArithmeticModeTest.booleanDependentUnusedUnsupported, `ArithmeticModeTest.rangeBooleanDependentInactiveUnsupported,
      `ArithmeticModeTest.instanceCustom, `ArithmeticModeTest.instanceWrappedCustom, `ArithmeticModeTest.instanceWrappedVariable, `ArithmeticModeTest.rangeInstanceCustom,
      `ArithmeticModeTest.naturalCustomNat, `ArithmeticModeTest.naturalCustomWord, `ArithmeticModeTest.naturalNotLiteral, `ArithmeticModeTest.rangeNaturalCustomNat,
      `ArithmeticModeTest.boolBindCustomPure, `ArithmeticModeTest.boolBindCustomBind, `ArithmeticModeTest.boolBindUnusedUnsupported, `ArithmeticModeTest.rangeBoolBindUnusedUnsupported,
      `ArithmeticModeTest.boolChoiceUnsupportedArm, `ArithmeticModeTest.boolChoiceUnusedUnsupported, `ArithmeticModeTest.boolChoiceCustomDecision, `ArithmeticModeTest.rangeBoolChoiceUnsupportedArm,
      `ArithmeticModeTest.propChoiceUnsupportedArm, `ArithmeticModeTest.propChoiceUnusedUnsupported, `ArithmeticModeTest.propChoiceCustomDecision, `ArithmeticModeTest.rangePropChoiceUnsupportedArm,
      `ArithmeticModeTest.boolFnUnusedUnsupported, `ArithmeticModeTest.boolFnUnsupportedArgument, `ArithmeticModeTest.boolFnBooleanResult, `ArithmeticModeTest.rangeBoolFnUnusedUnsupported,
      `ArithmeticModeTest.decideUnsupportedOperand, `ArithmeticModeTest.decideUnusedUnsupported, `ArithmeticModeTest.decideCustomEvidence, `ArithmeticModeTest.rangeDecideUnsupported,
      `ArithmeticModeTest.boolWordUnsupported, `ArithmeticModeTest.boolWordUnusedUnsupported, `ArithmeticModeTest.boolWordUnknownHelper, `ArithmeticModeTest.rangeBoolWordUnsupported,
      `ArithmeticModeTest.boolEqUnsupported, `ArithmeticModeTest.boolEqUnusedUnsupported, `ArithmeticModeTest.boolEqCustomInstance, `ArithmeticModeTest.rangeBoolEqUnsupported,
      `ArithmeticModeTest.boolPropUnsupported, `ArithmeticModeTest.boolPropInactiveUnsupported, `ArithmeticModeTest.boolPropCustomDecision, `ArithmeticModeTest.rangeBoolPropUnsupported,
      `ArithmeticModeTest.localDecideUnsupported, `ArithmeticModeTest.localDecideInactiveUnsupported, `ArithmeticModeTest.localDecideCustomDecision, `ArithmeticModeTest.rangeLocalDecideUnsupported,
      `ArithmeticModeTest.relationChoiceUnsupported, `ArithmeticModeTest.relationChoiceInactiveUnsupported, `ArithmeticModeTest.relationChoiceCustomDecision, `ArithmeticModeTest.rangeRelationChoiceUnsupported,
      `ArithmeticModeTest.dependentChoiceUnsupported, `ArithmeticModeTest.dependentChoiceInactiveUnsupported, `ArithmeticModeTest.dependentChoiceCustomDecision, `ArithmeticModeTest.rangeDependentChoiceUnsupported,
      `ArithmeticModeTest.boolLetUnsupportedBound, `ArithmeticModeTest.boolLetUnsupportedBody, `ArithmeticModeTest.rangeBoolLetUnsupported,
      `ArithmeticModeTest.boolWordLetUnsupportedBound, `ArithmeticModeTest.boolWordLetUnsupportedBody, `ArithmeticModeTest.boolWordLetUnsupportedType, `ArithmeticModeTest.rangeBoolWordLetUnsupported,
      `ArithmeticModeTest.annotatedLetUnsupportedBound, `ArithmeticModeTest.annotatedLetUnsupportedBody, `ArithmeticModeTest.annotatedLetUnsupportedType, `ArithmeticModeTest.rangeAnnotatedLetUnsupported,
      `ArithmeticModeTest.nestedIdUnsupportedBound, `ArithmeticModeTest.nestedIdUnsupportedBody, `ArithmeticModeTest.nestedIdUnsupportedType, `ArithmeticModeTest.rangeNestedIdUnsupported,
      `ArithmeticModeTest.idLetUnsupportedBound, `ArithmeticModeTest.idLetUnsupportedBoolean, `ArithmeticModeTest.idLetUnsupportedType, `ArithmeticModeTest.rangeIdLetUnsupported,
      `ArithmeticModeTest.idArithmeticCustom, `ArithmeticModeTest.idArithmeticUnsupported, `ArithmeticModeTest.idArithmeticNat, `ArithmeticModeTest.rangeIdArithmeticCustom,
      `ArithmeticModeTest.manyUnusedUnsupported, `ArithmeticModeTest.manyWrongDomain, `ArithmeticModeTest.manyPartial, `ArithmeticModeTest.manyIgnoredOperand,
      `ArithmeticModeTest.idCustomPure, `ArithmeticModeTest.idCustomBind, `ArithmeticModeTest.idUnusedUnsupported,
      `ArithmeticModeTest.punitHigherUniverse, `ArithmeticModeTest.punitUnsupportedBody, `ArithmeticModeTest.punitUnusedUnsupported,
      `ArithmeticModeTest.literalInactiveUnsupported, `ArithmeticModeTest.literalCustomDecision, `ArithmeticModeTest.literalUnusedUnsupported,
      `ArithmeticModeTest.minimumCustom, `ArithmeticModeTest.maximumCustom, `ArithmeticModeTest.extremaUnusedCustom,
      `ArithmeticModeTest.mixedGuardCustom, `ArithmeticModeTest.mixedGuardDecision, `ArithmeticModeTest.mixedGuardUnusedCustom,
      `ArithmeticModeTest.boolCompoundCustom, `ArithmeticModeTest.boolCompoundDecision, `ArithmeticModeTest.boolCompoundUnusedCustom,
      `ArithmeticModeTest.compoundNotCustom, `ArithmeticModeTest.compoundNotInnerCustom, `ArithmeticModeTest.compoundNotUnusedCustom,
      `ArithmeticModeTest.compoundCustom, `ArithmeticModeTest.compoundUnsupported, `ArithmeticModeTest.compoundUnusedCustom,
      `ArithmeticModeTest.complementCustom, `ArithmeticModeTest.complementHelper, `ArithmeticModeTest.complementUnusedCustom,
      `ArithmeticModeTest.rangeLetUnsupported, `ArithmeticModeTest.rangeLetTwoLoops, `ArithmeticModeTest.rangeLetBool,
      `ArithmeticModeTest.rangeOuterUnsupported, `ArithmeticModeTest.rangeOuterNat, `ArithmeticModeTest.rangeOuterPartial,
      `ArithmeticModeTest.rangeBinaryStepUnsupported, `ArithmeticModeTest.rangeBinaryStepPartial, `ArithmeticModeTest.rangeBinaryStepBool, `ArithmeticModeTest.rangeBinaryStepNat,
      `ArithmeticModeTest.rangeBinaryUnsupported, `ArithmeticModeTest.rangeBinaryPartial,
      `ArithmeticModeTest.strideOverflow, `ArithmeticModeTest.strideCustom, `ArithmeticModeTest.strideDynamic,
      `ArithmeticModeTest.dynamicNatAddition, `ArithmeticModeTest.dynamicCalledStart,
      `ArithmeticModeTest.intervalOverflow, `ArithmeticModeTest.intervalCustom,
      `ArithmeticModeTest.rangeNatOverflow, `ArithmeticModeTest.rangeCustomNat,
      `ArithmeticModeTest.rangeUnsupportedDirect, `ArithmeticModeTest.rangeUnusedUnsupportedDone, `ArithmeticModeTest.rangeCustomOrder,
      `ArithmeticModeTest.customReturn, `ArithmeticModeTest.customSequence,
      `ArithmeticModeTest.customNegated, `ArithmeticModeTest.customNe,
      `ArithmeticModeTest.customOrder, `ArithmeticModeTest.customEquality, `ArithmeticModeTest.customDecisionBranch, `ArithmeticModeTest.helper,
      `ArithmeticModeTest.wrongType, `ArithmeticModeTest.retain, `ArithmeticModeTest.customAdd,
      `ArithmeticModeTest.missing] do
    match LeanExe.Extract.Arithmetic.compileEnvironment env `ArithmeticModeTest name with
    | .ok _ => throwError "arithmetic mode accepted excluded source {name}"
    | .error _ => pure ()
  let oversized : LeanExe.IR.Func :=
    { sourceName := `oversized, exportName := some "oversized", params := 2 ^ 32,
      locals := 0, body := .skip, results := [] }
  if LeanExe.Wasm.ArithmeticBounds.Fits oversized "oversized" then
    throwError "arithmetic format check accepted an out-of-range parameter count"
