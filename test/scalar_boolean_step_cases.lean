import LeanExe.Extract.ScalarFunc

namespace BooleanStepCasesTest

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

end BooleanStepCasesTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanStepCasesTest.rangeBooleanStepCasesDirect, (fun (x y : UInt64) => (BooleanStepCasesTest.rangeBooleanStepCasesDirect x y).toUInt64)),
    (`BooleanStepCasesTest.rangeBooleanStepCasesHelper, (fun (x y : UInt64) => (BooleanStepCasesTest.rangeBooleanStepCasesHelper x y).toUInt64)),
    (`BooleanStepCasesTest.rangeBooleanStepCasesRetained, (fun (x y : UInt64) => (BooleanStepCasesTest.rangeBooleanStepCasesRetained x y).toUInt64)),
    (`BooleanStepCasesTest.rangeBooleanStepCasesIdentity, (fun (x y : UInt64) => (BooleanStepCasesTest.rangeBooleanStepCasesIdentity x y).toUInt64)),
    (`BooleanStepCasesTest.rangeBooleanStepCasesContinue, (fun (x y : UInt64) => (BooleanStepCasesTest.rangeBooleanStepCasesContinue x y).toUInt64)),
    (`BooleanStepCasesTest.rangeBooleanStepCasesNested, (fun (x y : UInt64) => (BooleanStepCasesTest.rangeBooleanStepCasesNested x y).toUInt64)),
    (`BooleanStepCasesTest.rangeBooleanStepCasesFlagInput, (fun (x y : UInt64) => (BooleanStepCasesTest.rangeBooleanStepCasesFlagInput x (y != 0)).toUInt64)),
    (`BooleanStepCasesTest.rangeBooleanStepCasesWordTail, (fun (x y : UInt64) => BooleanStepCasesTest.rangeBooleanStepCasesWordTail x y))]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean step cases extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean step cases IR comparisons passed"
