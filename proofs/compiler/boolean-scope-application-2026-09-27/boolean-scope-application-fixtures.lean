def booleanScopeApplicationWord (x y : UInt64) : UInt64 :=
  ((fun saved : UInt64 =>
    let f := fun n : UInt64 => n == saved
    f x || f y) (x + y)).toUInt64 + x

def booleanScopeApplicationFlag (x y : UInt64) : UInt64 :=
  ((fun saved : Bool =>
    let f := fun b : Bool => b || saved
    f (x == 0) && f (y == 0)) (x == y)).toUInt64 + y

def booleanScopeApplicationNested (x y : UInt64) : UInt64 :=
  ((fun saved : UInt64 =>
    (fun flag : Bool =>
      let f := fun n : UInt64 => flag || n == saved
      f x && f y) (saved == y)) (x + y)).toUInt64 + x

def booleanScopeApplicationRetained (x y : UInt64) : UInt64 :=
  ((fun saved : Id (Id UInt64) =>
    let f := fun n : UInt64 => n == Id.run (Id.run saved)
    f x || f y) (pure (pure (x + y)))).toUInt64 + y

def booleanScopeApplicationUnused (x y : UInt64) : UInt64 :=
  ((fun _unused : Bool =>
    let f := fun n : UInt64 => n == y
    f x || f 0) (x == y)).toUInt64 + x

def booleanScopeApplicationChoice (x y : UInt64) : UInt64 :=
  ((fun saved : UInt64 =>
    let f := fun n : UInt64 => n == saved
    f x || f y) (if x == 0 then y else x + y)).toUInt64 + y

def rangeBooleanScopeApplicationStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + ((fun saved : UInt64 =>
      let f := fun n : Id UInt64 => Id.run n == saved
      f i.toUInt64 || f seed) (a + i.toUInt64)).toUInt64
  return a

def rangeBooleanScopeApplicationExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if ((fun saved : Bool =>
      let f := fun b : Id Bool => Id.run b || saved
      f (a == 7) && f (i.toUInt64 == seed)) (a == seed)) then break
  return a

def rangeBooleanScopeApplicationContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ((fun saved : Id (Id UInt64) =>
      let f := fun n : UInt64 => n == Id.run (Id.run saved)
      f i.toUInt64 || f seed) (pure (pure (a + seed)))) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBooleanScopeApplicationTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + ((fun saved : Id (Id Bool) =>
    let f := fun b : Bool => b != Id.run (Id.run saved)
    f (a == 0) || f (seed == 0)) (pure (pure (a == seed)))).toUInt64
