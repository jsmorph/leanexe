def rangeBooleanStepFunctionWord (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => if n % 3 == 0 then ForInStep.done (!flag) else .yield flag
    f (i.toUInt64 + seed)

def rangeBooleanStepFunctionBoolean (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun b : Bool => if b then ForInStep.done (!flag) else .yield flag
    f (i.toUInt64 == seed)

def rangeBooleanStepFunctionNested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => if n % 3 == 0 then ForInStep.done (!flag) else .yield flag
    let g := fun b : Bool => if b then f i.toUInt64 else f seed
    g (i.toUInt64 == seed)

def rangeBooleanStepFunctionRetained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let f : Id UInt64 → Id (ForInStep Bool) := fun n => pure (ForInStep.yield (flag != (Id.run n == seed)))
    Id.run (f (pure i.toUInt64))

def rangeBooleanStepFunctionChoiceWord (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let n ← if flag then pure (i.toUInt64 + seed) else pure (seed + 1)
    flag := n % 3 == 0
    if flag then break
  return flag

def rangeBooleanStepFunctionChoiceBoolean (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let b ← if flag then pure (i.toUInt64 == seed) else pure (seed == 0)
    flag := b != flag
  return flag

def rangeBooleanStepFunctionUnused (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let _unused := fun n : UInt64 => if n == seed then ForInStep.done (!flag) else .yield flag
    ForInStep.yield (flag != (i.toUInt64 % 3 == 0))

def rangeBooleanStepFunctionRepeated (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun b : Bool => if b then ForInStep.done (!flag) else .yield flag
    if i.toUInt64 % 2 == 0 then f (seed == 0) else f (i.toUInt64 == seed)

def rangeBooleanStepFunctionFlagInput (count : UInt64) (seed : Bool) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] seed fun i flag =>
    let f : Id Bool → Id (ForInStep Bool) := fun b => pure (ForInStep.yield (flag != (Id.run b || seed)))
    Id.run (f (pure (i.toUInt64 % 3 == 0)))

def rangeBooleanStepFunctionWordTail (count seed : UInt64) : UInt64 :=
  let flag : Bool := forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => if n % 3 == 0 then ForInStep.done (!flag) else .yield flag
    f (i.toUInt64 + seed)
  if flag then seed + count else seed * 3
