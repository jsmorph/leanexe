def rangeBooleanStepBindWord (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let n ← pure (i.toUInt64 + seed)
    flag := flag != (n % 3 == 0)
  return flag

def rangeBooleanStepBindBoolean (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let b ← pure (i.toUInt64 == seed)
    flag := flag != b
  return flag

def rangeBooleanStepBindChain (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let n ← pure (i.toUInt64 + seed)
    let b ← pure (n % 3 == 0 || flag)
    let k ← pure (n + b.toUInt64)
    flag := flag != (b && k % 5 == 0)
  return flag

def rangeBooleanStepBindUnusedWord (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let _unused ← pure (i.toUInt64 + seed)
    flag := !flag
  return flag

def rangeBooleanStepBindUnusedBoolean (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let _unused ← pure (i.toUInt64 == seed)
    flag := !flag
  return flag

def rangeBooleanStepBindCaptured (count : UInt64) (seed : Bool) : Id Bool := do
  let f := fun n : UInt64 => (let g := fun b : Bool => b || seed; g (n % 3 == 0))
  let mut flag := seed
  for i in [:count.toNat] do
    let b ← pure (f i.toUInt64)
    flag := flag != b
    if flag then break
  return flag

def rangeBooleanStepBindContinue (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [1:count.toNat:3] do
    let b ← pure (i.toUInt64 % 2 == 0)
    if b then continue
    let n ← pure (i.toUInt64 + seed)
    flag := flag != (n % 3 == 0)
  return flag

def rangeBooleanStepBindWordTail (count seed : UInt64) : UInt64 :=
  let flag := Id.run do
    let mut a := seed == 0
    for i in [:count.toNat] do
      let b ← pure (i.toUInt64 == seed)
      a := a != b
      if a then break
    return a
  if flag then seed + count else seed * 3
