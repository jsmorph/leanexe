import LeanExe.Extract.ScalarFunc

namespace BooleanStepFunctionTest

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

end BooleanStepFunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionWord, (fun (x y : UInt64) => (BooleanStepFunctionTest.rangeBooleanStepFunctionWord x y).toUInt64)),
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionBoolean, (fun (x y : UInt64) => (BooleanStepFunctionTest.rangeBooleanStepFunctionBoolean x y).toUInt64)),
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionNested, (fun (x y : UInt64) => (BooleanStepFunctionTest.rangeBooleanStepFunctionNested x y).toUInt64)),
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionRetained, (fun (x y : UInt64) => (BooleanStepFunctionTest.rangeBooleanStepFunctionRetained x y).toUInt64)),
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionChoiceWord, (fun (x y : UInt64) => (BooleanStepFunctionTest.rangeBooleanStepFunctionChoiceWord x y).toUInt64)),
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionChoiceBoolean, (fun (x y : UInt64) => (BooleanStepFunctionTest.rangeBooleanStepFunctionChoiceBoolean x y).toUInt64)),
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionUnused, (fun (x y : UInt64) => (BooleanStepFunctionTest.rangeBooleanStepFunctionUnused x y).toUInt64)),
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionRepeated, (fun (x y : UInt64) => (BooleanStepFunctionTest.rangeBooleanStepFunctionRepeated x y).toUInt64)),
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionFlagInput, (fun (x y : UInt64) => (BooleanStepFunctionTest.rangeBooleanStepFunctionFlagInput x (y != 0)).toUInt64)),
    (`BooleanStepFunctionTest.rangeBooleanStepFunctionWordTail, (fun (x y : UInt64) => BooleanStepFunctionTest.rangeBooleanStepFunctionWordTail x y))]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean step function extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean step function IR comparisons passed"
