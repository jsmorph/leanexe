def rangeBinaryStepHelperDirect (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == a
    if f i.toUInt64 seed then a := a + 7 else a := a + 1
  return a

def rangeBinaryStepHelperExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == 7
    a := a + i.toUInt64 + 1
    if f a seed || f seed a then break
  return a

def rangeBinaryStepHelperContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (pure (x + 3 * y == a) : Id Bool)
    if Id.run (f i.toUInt64 seed) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBinaryStepHelperNested (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x == y
    let g := fun x y : UInt64 => f (x + 3 * y) a || f seed y
    a := a + (g i.toUInt64 seed).toUInt64 + (g seed i.toUInt64).toUInt64
  return a

def rangeBinaryStepHelperUnused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => x + 3 * y == a
    a := a + i.toUInt64 + 1
  return a

def rangeBinaryStepHelperWordTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == a
    let saved := (f i.toUInt64 seed).toUInt64
    if f seed a then a := saved + 5 else a := a + saved + 1
  return a * 3 + seed

def rangeBinaryStepHelperCapturedExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (x + 3 * y) % 7 == a % 7
    a := a + i.toUInt64 + 1
    if f seed a || f a seed then break
  return a

def rangeBinaryStepHelperChoice (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == a
    let first := if i.toUInt64 == 0 then seed else a
    if f first (a + i.toUInt64) then a := a + 7 else a := a * 3 + 1
    if f a first then break
  return a
