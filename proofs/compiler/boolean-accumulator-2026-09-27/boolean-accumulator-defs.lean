def rangeBooleanAccumulatorToggle (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for _ in [:count.toNat] do
    flag := !flag
  return flag

def rangeBooleanAccumulatorIndex (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed % 3 == 0
  for i in [:count.toNat] do
    flag := flag != (i.toUInt64 % 3 == seed % 3)
  return flag

def rangeBooleanAccumulatorChoice (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    if i.toUInt64 % 2 == 0 then flag := !flag
    else flag := flag || i.toUInt64 == seed
  return flag

def rangeBooleanAccumulatorBreak (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    flag := flag != (i.toUInt64 == seed)
    if flag then break
  return flag

def rangeBooleanAccumulatorContinue (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    if i.toUInt64 % 2 == 0 then continue
    flag := !flag
  return flag

def rangeBooleanAccumulatorStride (count seed : UInt64) : Id Bool := do
  let mut flag := seed == 0
  for i in [1:count.toNat:3] do
    flag := flag != (i.toUInt64 % 5 == 0)
  return flag

def rangeBooleanAccumulatorPredicate (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut flag := seed == 0
  for i in [:count.toNat] do
    flag := f flag || i.toUInt64 == seed
  return flag

def rangeBooleanAccumulatorInitial (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut flag := f (seed == 0)
  for i in [:count.toNat] do
    if f flag then break
    flag := i.toUInt64 == seed
  return f flag

def rangeBooleanAccumulatorWordTail (count seed : UInt64) : UInt64 :=
  let flag := Id.run do
    let mut a := seed == 0
    for i in [:count.toNat] do
      a := a != (i.toUInt64 == seed)
      if a then break
    return a
  if flag then seed + count else seed * 3

def rangeBooleanAccumulatorInput (count : UInt64) (seed : Bool) : Id Bool := do
  let mut flag := seed
  for i in [:count.toNat] do
    flag := flag != (i.toUInt64 % 3 == 0 || seed)
  return flag

def rangeBooleanAccumulatorHigh (count seed : UInt64) : Bool :=
  forIn (m := Id) [(18446744073709551615 - count).toNat:18446744073709551615:2] (seed == 0) fun i flag =>
    .yield (flag != (i.toUInt64 % 3 == seed % 3))

def rangeBooleanAccumulatorHuge (count seed : UInt64) : Bool :=
  forIn (m := Id) [0:count.toNat:18446744073709551615] (seed == 0) fun i flag =>
    .done (flag != (i.toUInt64 == seed))
