def binaryBooleanHelperDirect (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a == b
  (f x y).toUInt64 + x

def binaryBooleanHelperRepeated (x y : UInt64) : UInt64 :=
  (let f := fun a b : UInt64 => a == b
   f x y || f y 0).toUInt64 + y

def binaryBooleanHelperCapture (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let f := fun a b : UInt64 => a + b == saved
   f x y && f y x).toUInt64 + x

def binaryBooleanHelperNested (x y : UInt64) : UInt64 :=
  (let f := fun a b : UInt64 =>
     let g := fun n : UInt64 => n == b
     g a || g x
   f x y && f y x).toUInt64 + y

def binaryBooleanHelperRetained (x y : UInt64) : UInt64 :=
  (let f := fun (a b : UInt64) => (pure (a == b) : Id Bool)
   Id.run (f x y) || Id.run (f y 0)).toUInt64 + x

def binaryBooleanHelperUnused (x y : UInt64) : UInt64 :=
  (let _f := fun a b : UInt64 => a == b
   x == y).toUInt64 + y

def binaryBooleanHelperOrder (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a + 3 * b == y
  ((f x y) != (f y x)).toUInt64 + x

def rangeBinaryBooleanHelperStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (let f := fun x y : UInt64 => x + 3 * y == a
              f i.toUInt64 seed || f seed i.toUInt64).toUInt64
  return a

def rangeBinaryBooleanHelperExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let f := fun x y : UInt64 => x + 3 * y == 7
        f a seed || f i.toUInt64 a) then break
  return a

def rangeBinaryBooleanHelperContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun x y : UInt64 => (pure (x + 3 * y == a) : Id Bool)
        Id.run (f i.toUInt64 seed) || Id.run (f seed a)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBinaryBooleanHelperTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (let f := fun x y : UInt64 =>
                let g := fun n : UInt64 => n == y
                g x || g seed
              f a seed && f seed a).toUInt64
