import LeanExe.Extract.ScalarEnvironmentFunc

namespace BooleanStepUnitFunctionTest

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

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanStepUnitFunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionDirect, (fun (x y : UInt64) => (BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionDirect x y).toUInt64), true),
    (`BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionPUnit, (fun (x y : UInt64) => (BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionPUnit x y).toUInt64), true),
    (`BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionRetained, (fun (x y : UInt64) => (BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionRetained x y).toUInt64), true),
    (`BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionCapture, (fun (x y : UInt64) => (BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionCapture x y).toUInt64), true),
    (`BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionNested, (fun (x y : UInt64) => (BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionNested x y).toUInt64), true),
    (`BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionUnused, (fun (x y : UInt64) => (BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionUnused x y).toUInt64), true),
    (`BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionGenerated, (fun (x y : UInt64) => (BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionGenerated x y).toUInt64), true),
    (`BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionWordTail, (fun (x y : UInt64) => BooleanStepUnitFunctionTest.rangeBooleanStepUnitFunctionWordTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarEnvironmentFunc env name (some "entry") info.type value |
      throwError "{name}: Unit-prefixed Boolean step function extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanStepUnitFunctionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Unit-prefixed Boolean step function IR comparisons passed"
