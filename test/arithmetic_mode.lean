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
      `ArithmeticModeTest.rangeOuterThree] do
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
