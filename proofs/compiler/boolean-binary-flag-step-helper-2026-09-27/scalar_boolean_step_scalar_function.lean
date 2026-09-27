import LeanExe.Extract.ScalarFunc

namespace BooleanStepScalarFunctionTest

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

end BooleanStepScalarFunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarWord, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarWord x y).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarPredicate, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarPredicate x y).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarBooleanWord, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarBooleanWord x y).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarBooleanPredicate, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarBooleanPredicate x y).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarWordId, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarWordId x y).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarPredicateId, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarPredicateId x y).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarBooleanWordId, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarBooleanWordId x y).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarBooleanPredicateId, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarBooleanPredicateId x (y != 0)).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarCapture, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarCapture x y).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarUnused, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarUnused x y).toUInt64)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarRepeated, (fun (x y : UInt64) => BooleanStepScalarFunctionTest.rangeBooleanStepScalarRepeated x y)),
    (`BooleanStepScalarFunctionTest.rangeBooleanStepScalarNested, (fun (x y : UInt64) => (BooleanStepScalarFunctionTest.rangeBooleanStepScalarNested x y).toUInt64))]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean step scalar function extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
  unless comparisons == 288 do throwError "unexpected count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean step scalar function IR comparisons passed"
