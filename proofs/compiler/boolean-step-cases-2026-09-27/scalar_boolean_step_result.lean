import LeanExe.Extract.ScalarFunc

namespace BooleanStepResultTest

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

end BooleanStepResultTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanStepResultTest.rangeBooleanStepResultSaved, (fun (x y : UInt64) => (BooleanStepResultTest.rangeBooleanStepResultSaved x y).toUInt64)),
    (`BooleanStepResultTest.rangeBooleanStepResultBound, (fun (x y : UInt64) => (BooleanStepResultTest.rangeBooleanStepResultBound x y).toUInt64)),
    (`BooleanStepResultTest.rangeBooleanStepResultIgnored, (fun (x y : UInt64) => (BooleanStepResultTest.rangeBooleanStepResultIgnored x y).toUInt64)),
    (`BooleanStepResultTest.rangeBooleanStepResultShow, (fun (x y : UInt64) => (BooleanStepResultTest.rangeBooleanStepResultShow x y).toUInt64)),
    (`BooleanStepResultTest.rangeBooleanStepResultAlias, (fun (x y : UInt64) => (BooleanStepResultTest.rangeBooleanStepResultAlias x y).toUInt64)),
    (`BooleanStepResultTest.rangeBooleanStepResultCapture, (fun (x y : UInt64) => (BooleanStepResultTest.rangeBooleanStepResultCapture x y).toUInt64)),
    (`BooleanStepResultTest.rangeBooleanStepResultMonadicIgnored, (fun (x y : UInt64) => (BooleanStepResultTest.rangeBooleanStepResultMonadicIgnored x y).toUInt64)),
    (`BooleanStepResultTest.rangeBooleanStepResultNested, (fun (x y : UInt64) => (BooleanStepResultTest.rangeBooleanStepResultNested x y).toUInt64)),
    (`BooleanStepResultTest.rangeBooleanStepResultFlagInput, (fun (x y : UInt64) => (BooleanStepResultTest.rangeBooleanStepResultFlagInput x (y != 0)).toUInt64)),
    (`BooleanStepResultTest.rangeBooleanStepResultWordTail, (fun (x y : UInt64) => BooleanStepResultTest.rangeBooleanStepResultWordTail x y))]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean step result extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean step result IR comparisons passed"
