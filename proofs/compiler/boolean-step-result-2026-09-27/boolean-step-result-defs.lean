def rangeBooleanStepResultSaved (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    result

def rangeBooleanStepResultBound (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag => do
    let result ← pure (ForInStep.yield (flag != (i.toUInt64 == seed)))
    return result

def rangeBooleanStepResultIgnored (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let _unused : ForInStep Bool := .done (!flag)
    .yield (flag != (i.toUInt64 == seed))

def rangeBooleanStepResultShow (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let f := fun n : Id UInt64 => (show Id (ForInStep Bool) from pure (ForInStep.yield (flag != (Id.run n == seed))))
    Id.run (f (pure i.toUInt64))

def rangeBooleanStepResultAlias (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    let alias : Id (ForInStep Bool) := result
    Id.run alias

def rangeBooleanStepResultCapture (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    let f := fun b : Bool => if b then result else ForInStep.yield (!flag)
    f (i.toUInt64 % 3 == 0)

def rangeBooleanStepResultMonadicIgnored (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag => do
    let _unused ← pure (ForInStep.done (!flag))
    return ForInStep.yield (flag != (i.toUInt64 == seed))

def rangeBooleanStepResultNested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let first : ForInStep Bool := .done (!flag)
    let second : ForInStep Bool := .yield flag
    if i.toUInt64 == seed then first else second

def rangeBooleanStepResultFlagInput (count : UInt64) (seed : Bool) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] seed fun i flag =>
    let result : ForInStep Bool := .yield (flag != (seed || i.toUInt64 % 3 == 0))
    let alias : Id (ForInStep Bool) := pure result
    Id.run alias

def rangeBooleanStepResultWordTail (count seed : UInt64) : UInt64 :=
  let flag : Bool := forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    result
  if flag then seed + count else seed * 3
