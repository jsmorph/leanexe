def rangeBooleanStepCasesDirect (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    ForInStep.casesOn (motive := fun _ => ForInStep Bool) result
      (fun value => .yield value) (fun value => .done value)

def rangeBooleanStepCasesHelper (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool =>
      ForInStep.casesOn (motive := fun _ => ForInStep Bool) result
        (fun value => if i.toUInt64 == seed then .done (!value) else .yield flag)
        (fun value => .yield (value != flag))
    f (if flag then .done false else .yield true)

def rangeBooleanStepCasesRetained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    ForInStep.casesOn (motive := fun _ => Id (ForInStep Bool))
      (if i.toUInt64 == seed then .done (!flag) else .yield flag)
      (fun value => pure (ForInStep.yield value))
      (fun value => pure (ForInStep.done value))

def rangeBooleanStepCasesIdentity (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    ForInStep.casesOn (motive := fun _ => ForInStep Bool)
      (if i.toUInt64 == seed then .done (!flag) else .yield flag)
      (fun value => .done value) (fun value => .yield value)

def rangeBooleanStepCasesContinue (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    ForInStep.casesOn (motive := fun _ => ForInStep Bool)
      (if i.toUInt64 == seed then .done (!flag) else .yield flag)
      (fun value => .yield value) (fun value => .yield value)

def rangeBooleanStepCasesNested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    ForInStep.casesOn (motive := fun _ => ForInStep Bool)
      (if i.toUInt64 == seed then .done (!flag) else .yield flag)
      (fun value => ForInStep.casesOn (motive := fun _ => ForInStep Bool) (.yield (!value))
        (fun inner => .done (inner != flag)) (fun inner => .yield inner))
      (fun value => .yield (value != flag))

def rangeBooleanStepCasesFlagInput (count : UInt64) (seed : Bool) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] seed fun i flag =>
    ForInStep.casesOn (motive := fun _ => ForInStep Bool)
      (if i.toUInt64 % 3 == 0 then .done (!flag) else .yield flag)
      (fun value => .yield (value != seed)) (fun value => .yield (!value))

def rangeBooleanStepCasesWordTail (count seed : UInt64) : UInt64 :=
  let flag : Bool := forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    ForInStep.casesOn (motive := fun _ => ForInStep Bool)
      (if i.toUInt64 == seed then .done (!flag) else .yield flag)
      (fun value => .yield value) (fun value => .done value)
  if flag then seed + count else seed * 3
