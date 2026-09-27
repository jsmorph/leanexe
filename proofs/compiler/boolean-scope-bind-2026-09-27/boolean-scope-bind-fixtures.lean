def booleanScopeBindWord (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (x + y) : Id UInt64)
    let f := fun n : Id UInt64 => (Id.run n) == saved
    return f x || f y).toUInt64 + x

def booleanScopeBindFlag (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (x == y) : Id Bool)
    let f := fun b : Id Bool => Id.run b || saved
    return f (x == 0) && f (y == 0)).toUInt64 + y

def booleanScopeBindNested (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (x + y) : Id UInt64)
    let flag ← (pure (saved == y) : Id Bool)
    let f := fun n : UInt64 => flag || n == saved
    return f x && f y).toUInt64 + x

def booleanScopeBindRetained (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (pure (x + y)) : Id (Id UInt64))
    let f := fun n : UInt64 => n == Id.run saved
    return f x || f y).toUInt64 + y

def booleanScopeBindUnused (x y : UInt64) : UInt64 :=
  (Id.run do
    let _unused ← (pure (x == y) : Id Bool)
    let f := fun n : UInt64 => n == y
    return f x || f 0).toUInt64 + x

def booleanScopeBindChoice (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (if x == 0 then pure y else pure (x + y) : Id UInt64)
    let f := fun n : UInt64 => n == saved
    return f x || f y).toUInt64 + y

def rangeBooleanScopeBindStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (Id.run do
      let saved ← (pure (a + i.toUInt64) : Id UInt64)
      let f := fun n : Id UInt64 => Id.run n == saved
      return f i.toUInt64 || f seed).toUInt64
  return a

def rangeBooleanScopeBindExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (Id.run do
      let saved ← (pure (a == seed) : Id Bool)
      let f := fun b : Id Bool => Id.run b || saved
      return f (a == 7) && f (i.toUInt64 == seed)) then break
  return a

def rangeBooleanScopeBindContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (Id.run do
      let saved ← (pure (pure (a + seed)) : Id (Id UInt64))
      let f := fun n : UInt64 => n == Id.run saved
      return f i.toUInt64 || f seed) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBooleanScopeBindTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (Id.run do
    let saved ← (pure (pure (a == seed)) : Id (Id Bool))
    let f := fun b : Bool => b != Id.run saved
    return f (a == 0) || f (seed == 0)).toUInt64
