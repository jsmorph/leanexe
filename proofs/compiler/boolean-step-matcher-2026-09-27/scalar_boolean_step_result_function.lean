import LeanExe.Extract.ScalarFunc

namespace BooleanStepResultFunctionTest

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

end BooleanStepResultFunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionDirect, (fun (x y : UInt64) => (BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionDirect x y).toUInt64)),
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionIgnored, (fun (x y : UInt64) => (BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionIgnored x y).toUInt64)),
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionNested, (fun (x y : UInt64) => (BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionNested x y).toUInt64)),
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionRetained, (fun (x y : UInt64) => (BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionRetained x y).toUInt64)),
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionJoined, (fun (x y : UInt64) => (BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionJoined x y).toUInt64)),
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionCapture, (fun (x y : UInt64) => (BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionCapture x y).toUInt64)),
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionRepeated, (fun (x y : UInt64) => (BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionRepeated x y).toUInt64)),
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionMonadic, (fun (x y : UInt64) => (BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionMonadic x y).toUInt64)),
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionFlagInput, (fun (x y : UInt64) => (BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionFlagInput x (y != 0)).toUInt64)),
    (`BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionWordTail, (fun (x y : UInt64) => BooleanStepResultFunctionTest.rangeBooleanStepResultFunctionWordTail x y))]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean step result function extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean step result function IR comparisons passed"
