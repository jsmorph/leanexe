def booleanScopeBindingWord (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let f := fun n : Id UInt64 =>
     let g := fun b : Id Bool => (Id.run b) != (saved == y)
     g ((Id.run n) == saved) || g (x == 0)
   f x && f y).toUInt64 + y

def booleanScopeBindingFlag (x y : UInt64) : UInt64 :=
  (let saved := x == y
   let f := fun n : UInt64 => saved || n == y
   f x && f 0).toUInt64 + x

def booleanScopeBindingWordId (x y : UInt64) : UInt64 :=
  (let saved : Id (Id UInt64) := pure (pure (x + y))
   let f := fun n : Id UInt64 => (Id.run n) == Id.run (Id.run saved)
   f x || f y).toUInt64 + y

def booleanScopeBindingFlagId (x y : UInt64) : UInt64 :=
  (let saved : Id (Id Bool) := pure (pure (x == y))
   let f := fun b : Id Bool => Id.run b || Id.run (Id.run saved)
   f (x == 0) && f (y == 0)).toUInt64 + x

def booleanScopeBindingUnused (x y : UInt64) : UInt64 :=
  (let _unused := x + y
   let f := fun n : UInt64 => n == y
   f x || f 0).toUInt64 + x

def booleanScopeBindingNested (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let flag := saved == x
   let f := fun n : UInt64 => flag || n == saved
   f x && f y).toUInt64 + y

def rangeBooleanScopeBindingStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (let saved := a + i.toUInt64
              let f := fun n : Id UInt64 => (Id.run n) == saved
              f i.toUInt64 || f seed).toUInt64
  return a

def rangeBooleanScopeBindingExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let saved := a == seed
        let f := fun b : Id Bool => Id.run b || saved
        f (a == 7) && f (i.toUInt64 == seed)) then break
  return a

def rangeBooleanScopeBindingContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let saved : Id (Id UInt64) := pure (pure (a + seed))
        let f := fun n : UInt64 => n == Id.run (Id.run saved)
        f i.toUInt64 || f seed) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBooleanScopeBindingTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (let saved : Id (Id Bool) := pure (pure (a == seed))
              let f := fun b : Bool => b != Id.run (Id.run saved)
              f (a == 0) || f (seed == 0)).toUInt64

