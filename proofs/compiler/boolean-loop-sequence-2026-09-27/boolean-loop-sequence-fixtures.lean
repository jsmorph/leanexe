def rangeBooleanSequenceDirect (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b

def rangeBooleanSequenceDependent (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := a == seed
  for i in [:(a % 7).toNat] do b := b != (i.toUInt64 == seed)
  return b

def rangeBooleanSequenceExits (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64
    if a % 7 == 0 then break
  let mut b := false
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    b := b || i.toUInt64 == a % 11
    if b then break
  return b

def rangeBooleanSequenceUnused (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == seed
  return b

def rangeBooleanSequenceThree (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  for i in [:count.toNat] do a := a * 3 + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b

def rangeBooleanSequenceRetained (count seed : UInt64) : Id (Id Bool) := do
  let first : Id (Id UInt64) := do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64
    return a
  let a ← first
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b


def rangeBooleanSequenceBoolInput (count : UInt64) (flag : Bool) : Id Bool := do
  let mut a := flag.toUInt64
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := flag
  for i in [:count.toNat] do b := b != (i.toUInt64 == a % 7)
  return b

def rangeBooleanSequenceWordTail (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := a
  for i in [:count.toNat] do b := b * 3 + i.toUInt64
  return b % 7 == a % 7
