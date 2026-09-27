def rangeBooleanStepScalarWord (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => n + seed
    if f i.toUInt64 == 0 then .done (!flag) else .yield flag

def rangeBooleanStepScalarPredicate (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => n % 3 == seed
    if f i.toUInt64 then .done (!flag) else .yield flag

def rangeBooleanStepScalarBooleanWord (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun b : Bool => if b then seed + 1 else seed * 3
    if f flag == i.toUInt64 then .done (!flag) else .yield flag

def rangeBooleanStepScalarBooleanPredicate (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun b : Bool => b != (i.toUInt64 == seed)
    .yield (f flag)

def rangeBooleanStepScalarWordId (count seed : UInt64) : Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let f : Id UInt64 → Id UInt64 := fun n => pure (Id.run n + seed)
    if Id.run (f (pure i.toUInt64)) == 0 then .done (!flag) else .yield flag

def rangeBooleanStepScalarPredicateId (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f : Id UInt64 → Id (Id Bool) := fun n => pure (pure (Id.run n % 3 == seed))
    if Id.run (Id.run (f (pure i.toUInt64))) then .done (!flag) else .yield flag

def rangeBooleanStepScalarBooleanWordId (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f : Id Bool → Id UInt64 := fun b => pure (if Id.run b then seed + 1 else seed * 3)
    if Id.run (f (pure flag)) == i.toUInt64 then .done (!flag) else .yield flag

def rangeBooleanStepScalarBooleanPredicateId (count : UInt64) (seed : Bool) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] seed fun i flag =>
    let f : Id Bool → Id (Id Bool) := fun b => pure (pure (Id.run b != (i.toUInt64 % 3 == 0)))
    .yield (Id.run (Id.run (f (pure flag))))

def rangeBooleanStepScalarCapture (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let saved := flag
    let f := fun n : UInt64 => saved != (n == seed)
    let saved := !flag
    if saved then .yield (f i.toUInt64) else .done (f seed)

def rangeBooleanStepScalarUnused (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let _f := fun n : UInt64 => n + seed
    let _g := fun b : Bool => b != flag
    .yield (flag != (i.toUInt64 == seed))

def rangeBooleanStepScalarRepeated (count seed : UInt64) : UInt64 :=
  let flag : Bool := forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => n + seed
    if f (f i.toUInt64) == 0 then .done (!flag) else .yield flag
  if flag then seed + count else seed * 3

def rangeBooleanStepScalarNested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => n + seed
    let g := fun b : Bool => b != (f i.toUInt64 == 0)
    .yield (g flag)
