def rangeBinaryBooleanLoopHelperDirect (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := f i.toUInt64 a.toUInt64 || a
  return a

def rangeBinaryBooleanLoopHelperBound (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let n := if f count seed then count else count % 7
  let mut a := seed != 0
  for i in [:n.toNat] do
    a := (f i.toUInt64 seed) != a
  return a

def rangeBinaryBooleanLoopHelperInitial (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := f seed count
  for i in [:count.toNat] do
    a := (i.toUInt64 == seed) || !a
  return a

def rangeBinaryBooleanLoopHelperExit (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := !a
    if f i.toUInt64 a.toUInt64 || f seed i.toUInt64 then break
  return a

def rangeBinaryBooleanLoopHelperUnused (count seed : UInt64) : Id Bool := do
  let _f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := (i.toUInt64 == seed) || !a
  return a

def rangeBinaryBooleanLoopHelperWordTail (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := (i.toUInt64 == seed) || !a
  return a.toUInt64 + (f a.toUInt64 seed).toUInt64 + (f seed a.toUInt64).toUInt64

def rangeBinaryBooleanLoopHelperCapture (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let seed := seed + 1
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := (f i.toUInt64 seed) != a
    if f a.toUInt64 seed then break
  return a

def rangeBinaryBooleanLoopHelperNested (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let g := fun x y : UInt64 => (pure (f y x || x == y) : Id Bool)
  let mut a := seed != 0
  for i in [:count.toNat] do
    if Id.run (g i.toUInt64 a.toUInt64) then continue
    a := (i.toUInt64 == seed) || !a
  return a
