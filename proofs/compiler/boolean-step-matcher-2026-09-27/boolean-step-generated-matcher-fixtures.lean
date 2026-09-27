def stepDispatcher (motive : ForInStep Bool → Sort u) (value : ForInStep Bool)
    (doneBody : ∀ flag, motive (.done flag)) (yieldBody : ∀ flag, motive (.yield flag)) : motive value :=
  ForInStep.casesOn (motive := fun value => motive value) value
    (fun flag => doneBody flag) (fun flag => yieldBody flag)

def rangeBooleanStepMatchDirect (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .yield value
    | .yield value => .done value

def rangeBooleanStepMatchHelper (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool =>
      match result with
      | .done value => if i.toUInt64 == seed then .done (!value) else .yield flag
      | .yield value => .yield (value != flag)
    f (if flag then .done false else .yield true)

def rangeBooleanStepMatchNested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value =>
      let inner : ForInStep Bool := .yield (!value)
      match inner with
      | .done value => .done (value != flag)
      | .yield value => .yield value
    | .yield value => .yield (value != flag)

def rangeBooleanStepMatchRetained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => pure (ForInStep.yield value)
    | .yield value => pure (ForInStep.done value)

def rangeBooleanStepMatchIdentity (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .done value
    | .yield value => .yield value

def rangeBooleanStepMatchContinue (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .yield value
    | .yield value => .yield value

def rangeBooleanStepMatchFlagInput (count : UInt64) (seed : Bool) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] seed fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 % (3 : UInt64) == 0 then .done (!flag) else .yield flag
    match result with
    | .done value => .yield (value != seed)
    | .yield value => .yield (!value)

def rangeBooleanStepMatchWordTail (count seed : UInt64) : UInt64 :=
  let flag : Bool := forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .yield value
    | .yield value => .done value
  if flag then seed + count else seed * 3

def rangeBooleanStepMatchDispatcher (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    stepDispatcher (fun _ => ForInStep Bool)
      (if i.toUInt64 == seed then .done (!flag) else .yield flag)
      (fun value => .yield value) (fun value => .done value)

