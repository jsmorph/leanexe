def rangeBinaryFlagStepHelperDirect (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    a := f i.toUInt64 seed || a
  return a

def rangeBinaryFlagStepHelperExit (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
    a := !a
    if f i.toUInt64 seed || f seed i.toUInt64 then break
  return a

def rangeBinaryFlagStepHelperContinue (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (pure (x + 3 * y == seed + a.toUInt64) : Id Bool)
    if Id.run (f i.toUInt64 seed) then continue
    a := !a
  return a

def rangeBinaryFlagStepHelperNested (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x == y
    let g := fun x y : UInt64 => f (x + 3 * y) seed || a
    a := g i.toUInt64 seed && g seed i.toUInt64
  return a

def rangeBinaryFlagStepHelperUnused (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    a := (i.toUInt64 == seed) || !a
  return a

def rangeBinaryFlagStepHelperWordTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    let saved := f i.toUInt64 seed
    if f seed i.toUInt64 then a := saved else a := !saved
  return a.toUInt64 * 3 + seed

def rangeBinaryFlagStepHelperCapturedExit (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (x + 3 * y) % 7 == (seed + a.toUInt64) % 7
    a := !a
    if f seed (i.toUInt64 + a.toUInt64) || f i.toUInt64 seed then break
  return a

def rangeBinaryFlagStepHelperChoice (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    let first := if a then seed else i.toUInt64
    a := if f first (seed + i.toUInt64) then !a else f seed i.toUInt64
    if f a.toUInt64 first then break
  return a
