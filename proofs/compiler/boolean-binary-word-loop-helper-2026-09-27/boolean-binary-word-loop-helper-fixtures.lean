def rangeBinaryWordLoopHelperDirect (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (f i.toUInt64 a).toUInt64 + 1
  return a

def rangeBinaryWordLoopHelperBound (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let n := if f count seed then count else count % 7
  let mut a := seed
  for i in [:n.toNat] do
    a := a + i.toUInt64 + (f a seed).toUInt64
  return a

def rangeBinaryWordLoopHelperInitial (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := if f seed 0 then seed + 1 else seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a

def rangeBinaryWordLoopHelperExit (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if f a seed || f seed a then break
  return a

def rangeBinaryWordLoopHelperUnused (count seed : UInt64) : Id UInt64 := do
  let _f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a

def rangeBinaryWordLoopHelperTail (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (f a seed).toUInt64 + (f seed a).toUInt64

def rangeBinaryWordLoopHelperCapture (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let seed := seed + 1
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (f i.toUInt64 seed).toUInt64 + 1
    if f a seed then break
  return a + (f seed a).toUInt64

def rangeBinaryWordLoopHelperNested (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let g := fun x y : UInt64 => (pure (f y x || x == y) : Id Bool)
  let mut a := seed
  for i in [:count.toNat] do
    if Id.run (g i.toUInt64 a) then continue
    a := a + i.toUInt64 + 1
  return a + (Id.run (g a seed)).toUInt64
