def rangeBooleanStepResultFunctionDirect (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool => result
    f (if i.toUInt64 == seed then .done (!flag) else .yield flag)

def rangeBooleanStepResultFunctionIgnored (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun _result : ForInStep Bool => ForInStep.yield (flag != (i.toUInt64 == seed))
    f (.done (!flag))

def rangeBooleanStepResultFunctionNested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool => if flag then result else ForInStep.yield true
    let g := fun result : ForInStep Bool => f result
    g (if i.toUInt64 == seed then .done (!flag) else .yield flag)

def rangeBooleanStepResultFunctionRetained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let f : Id (ForInStep Bool) → Id (Id (ForInStep Bool)) := fun result => pure result
    Id.run (Id.run (f (pure (ForInStep.yield (flag != (i.toUInt64 == seed))))))

def rangeBooleanStepResultFunctionJoined (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag => do
    let result ← if i.toUInt64 == seed then pure (ForInStep.done (!flag)) else pure (ForInStep.yield flag)
    return result

def rangeBooleanStepResultFunctionCapture (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let saved : ForInStep Bool := .done (!flag)
    let f := fun result : ForInStep Bool => if i.toUInt64 == seed then saved else result
    f (.yield flag)

def rangeBooleanStepResultFunctionRepeated (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool => if i.toUInt64 == seed then result else ForInStep.yield (!flag)
    let first : ForInStep Bool := f (.done flag)
    f first

def rangeBooleanStepResultFunctionMonadic (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag => do
    let f := fun result : ForInStep Bool => pure result
    let result ← pure (ForInStep.yield (flag != (i.toUInt64 == seed)))
    f result

def rangeBooleanStepResultFunctionFlagInput (count : UInt64) (seed : Bool) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] seed fun i flag =>
    let f := fun result : ForInStep Bool => if seed then result else ForInStep.yield (!flag)
    f (.yield (flag != (i.toUInt64 % 3 == 0)))

def rangeBooleanStepResultFunctionWordTail (count seed : UInt64) : UInt64 :=
  let flag : Bool := forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool => result
    f (if i.toUInt64 == seed then .done (!flag) else .yield flag)
  if flag then seed + count else seed * 3
