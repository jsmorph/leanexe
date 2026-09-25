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
      `ArithmeticModeTest.rangeBoolNotFunction] do
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
      `ArithmeticModeTest.unsupportedLocalBody,
      `ArithmeticModeTest.rangeTwice,
      `ArithmeticModeTest.rangeUnsupportedFunction,
      `ArithmeticModeTest.rangeCustomBind,
      `ArithmeticModeTest.rangeUnsupportedResultFunction, `ArithmeticModeTest.rangeResultFunctionScalar, `ArithmeticModeTest.rangeResultFunctionBool,
      `ArithmeticModeTest.rangeUnusedStepValue, `ArithmeticModeTest.rangeUnusedStepBind, `ArithmeticModeTest.rangeCustomStepPure, `ArithmeticModeTest.rangeCustomStepBind,
      `ArithmeticModeTest.boolNotCustomBEq, `ArithmeticModeTest.boolNotCustomDecision, `ArithmeticModeTest.boolNotHelper,
      `ArithmeticModeTest.rangeBinaryStepUnsupported, `ArithmeticModeTest.rangeBinaryStepPartial, `ArithmeticModeTest.rangeBinaryStepThree, `ArithmeticModeTest.rangeBinaryStepBool, `ArithmeticModeTest.rangeBinaryStepNat,
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
