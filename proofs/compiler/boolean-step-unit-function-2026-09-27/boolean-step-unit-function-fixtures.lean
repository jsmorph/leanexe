def rangeBooleanStepUnitFunctionDirect (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f := fun (_u : Unit) (b : Bool) =>
      if i.toUInt64 == seed then ForInStep.done (!b) else ForInStep.yield b
    f () flag

def rangeBooleanStepUnitFunctionPUnit (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f := fun (_u : PUnit.{1}) (b : Bool) =>
      if i.toUInt64 % 3 == seed then ForInStep.done b else ForInStep.yield (!b)
    f PUnit.unit.{1} flag

def rangeBooleanStepUnitFunctionRetained (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f : Unit → Id Bool → Id (Id (ForInStep Bool)) := fun _u b =>
      pure (pure (if i.toUInt64 == seed then ForInStep.done (!b) else ForInStep.yield b))
    Id.run (Id.run (f () (pure flag)))

def rangeBooleanStepUnitFunctionCapture (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f := fun (_u : Unit) (b : Bool) =>
      if i.toUInt64 == seed then ForInStep.done (b != flag) else ForInStep.yield b
    f () (!flag)

def rangeBooleanStepUnitFunctionNested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f := fun (_u : Unit) (b : Bool) =>
      if i.toUInt64 == seed then ForInStep.done (!b) else ForInStep.yield b
    let g := fun (_u : PUnit.{1}) (b : Bool) => f () (b != flag)
    g PUnit.unit.{1} flag

def rangeBooleanStepUnitFunctionUnused (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let _f := fun (_u : Unit) (b : Bool) =>
      if i.toUInt64 == seed then ForInStep.done (!b) else ForInStep.yield b
    ForInStep.yield (!flag)
def rangeBooleanStepUnitFunctionGenerated (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    let first := if a then seed else i.toUInt64
    if f first (seed + i.toUInt64) then a := !a else a := f seed i.toUInt64
    if f a.toUInt64 first then break
  return a

def rangeBooleanStepUnitFunctionWordTail (count seed : UInt64) : UInt64 :=
  let flag : Bool := forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f := fun (_u : Unit) (b : Bool) =>
      if (i.toUInt64 + seed) % 7 == b.toUInt64 then ForInStep.done (!b) else ForInStep.yield b
    f () (flag != (i.toUInt64 % 3 == 0))
  if flag then seed + count else seed * 3 + 1
