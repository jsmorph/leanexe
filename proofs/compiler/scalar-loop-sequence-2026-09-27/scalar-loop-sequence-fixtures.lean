def rangeSequenceDirect (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  for i in [:count.toNat] do a := a * 3 + i.toUInt64
  return a

def rangeSequenceDependent (count seed : UInt64) : Id UInt64 := do
  let mut a := seed % 7
  for i in [:count.toNat] do a := (a + i.toUInt64) % 7
  let mut b := seed
  for i in [:a.toNat] do b := b + a + i.toUInt64
  return a + b

def rangeSequenceExits (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64
    if a % 7 == 0 then break
  let mut b := a
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    b := b + i.toUInt64
    if b % 11 == 0 then break
  return a + b

def rangeSequenceUnused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := seed
  for i in [:count.toNat] do b := b + i.toUInt64 * 3
  return b

def rangeSequenceThree (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  for i in [:count.toNat] do a := a * 3 + i.toUInt64
  for i in [:count.toNat] do a := a ^^^ i.toUInt64
  return a

def rangeSequenceShadow (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let seed := seed + 7
  let mut b := seed
  for i in [:count.toNat] do b := b + a + i.toUInt64
  return a + b + seed

def rangeSequenceIdBind (count seed : UInt64) : Id UInt64 := do
  let first : Id (Id UInt64) := do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64
    return a
  let a ← first
  let b ← (do
    let mut b : UInt64 := a
    for i in [:count.toNat] do b := b * 3 + i.toUInt64
    return b : Id UInt64)
  return UInt64.add a b

def rangeSequenceBoolInput (count : UInt64) (flag : Bool) : Id UInt64 := do
  let mut a := flag.toUInt64
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := a
  for i in [:count.toNat] do b := if flag then b + i.toUInt64 else b + 3
  return a + b
