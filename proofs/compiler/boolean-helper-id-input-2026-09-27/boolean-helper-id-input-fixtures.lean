def booleanHelperIdInputWord (x y : UInt64) : UInt64 :=
  (let f := fun n : Id UInt64 => (Id.run n) == y
   f x && f 0).toUInt64 + x

def booleanHelperIdInputBoolean (x y : UInt64) : UInt64 :=
  (let f := fun b : Id Bool => (Id.run b) != (x == y)
   f (x == 0) || f (y == 0)).toUInt64 + y

def booleanHelperIdInputNested (x y : UInt64) : UInt64 :=
  (let f := fun n : Id (Id UInt64) =>
    let g := fun b : Id (Id Bool) => (Id.run (Id.run b)) || y == 0
    g ((Id.run (Id.run n)) == y) && g false
   f x || f y).toUInt64 + x

def booleanHelperIdInputCapture (x y : UInt64) : UInt64 :=
  let saved := x + y
  (let f := fun n : Id UInt64 =>
     let g := fun b : Id Bool => (Id.run b) != (saved == y)
     g ((Id.run n) == saved) || g (x == 0)
   f x && f y).toUInt64 + y

def booleanHelperIdInputUnused (x y : UInt64) : UInt64 :=
  (let _unused := fun b : Id Bool =>
     let g := fun n : Id UInt64 => (Id.run n) == y
     (Id.run b) || g x || g 0
   x == y).toUInt64 + x

def booleanHelperIdInputProposition (x y : UInt64) : UInt64 :=
  if x < y ∧ (let f := fun n : Id UInt64 => (Id.run n) == y; f x || f y) then x + 7 else y + 3

def rangeBooleanHelperIdInputStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (let f := fun n : Id UInt64 => (Id.run n) == a; f i.toUInt64 || f seed).toUInt64
  return a

def rangeBooleanHelperIdInputExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let f := fun b : Id Bool => (Id.run b) != (a == seed); f (decide (a > 7)) && f (i.toUInt64 == seed)) then break
  return a

def rangeBooleanHelperIdInputContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : Id (Id UInt64) => (Id.run (Id.run n)) == a; f i.toUInt64 || f seed) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBooleanHelperIdInputTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (let f := fun b : Id Bool => (Id.run b) != (a == seed); f (a == 0) || f (seed == 0)).toUInt64
