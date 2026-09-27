import LeanExe.Extract.ScalarFunc

namespace BooleanLoopMixedConditionTest

def rangeBoolMixedConditionScalarLeft (count seed : UInt64) : Bool :=
  if seed == 0 then
    true
  else
      let f := fun x : UInt64 => x + seed + 1
      let value := Id.run do
        let mut a := f seed
        for i in [:count.toNat] do
          a := f a + f i.toUInt64
        return a
      f value == f (f seed)

def rangeBoolMixedConditionScalarRight (count seed : UInt64) : Bool :=
  if count < seed then
      let f := fun x y : UInt64 => x + 3 * y + seed % 5 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := f a i.toUInt64
          if a % 7 == 0 then break
        return a
      f value 1 % 7 == 0
  else
    seed % 7 == 0

def rangeBoolMixedConditionFlag (count : UInt64) (flag : Bool) : Bool :=
  if flag then
      let f := fun input : Bool => if flag && input then count + 7 else count - 3
      let value := Id.run do
        let mut a := f flag
        for i in [:count.toNat] do
          a := a + f (i.toUInt64 % 2 == 0)
        return a
      flag && value == f flag
  else
    !flag

def rangeBoolMixedConditionNested (count seed : UInt64) : Bool :=
  if seed < count then
    if seed % 2 == 0 then
      false
    else
        let limit := fun x : UInt64 => x % 17
        let value := Id.run do
          let mut a := seed
          for i in [:(limit count).toNat] do
            a := a + i.toUInt64 + 1
          return a
        value == seed + limit count
  else
    seed == count

def rangeBoolMixedConditionHelper (count seed : UInt64) : Bool :=
  let p := fun x : UInt64 => x % 3 == seed % 3
  if p count then
    p (seed + 1) || p count
  else
      let f := fun x : UInt64 => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value == f seed

def rangeBoolMixedConditionBooleanHelper (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  if p (count % 2 == 0) then
      let f := fun flag : Bool => seed % 5 + flag.toUInt64 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := a + f (i.toUInt64 % 2 == 0)
          if a % 7 == 0 then break
        return a
      f (value % 7 == 0) == f true
  else
    p true

def rangeBoolMixedConditionContinue (count seed : UInt64) : Bool :=
  if seed % 3 == 0 then
    seed == count
  else
      let f := fun x y z : UInt64 => (x + 3 * y + 5 * z) % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 a seed == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value seed 1 == f seed value 1

def rangeBoolMixedConditionStride (count seed : UInt64) : Bool :=
  if count < seed then
      let f := fun (_unit : Unit) (x : UInt64) => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [(f () seed).toNat:count.toNat:3] do
          a := a + i.toUInt64 + 1
          if a % 5 == 0 then break
        return a
      f () value == f () seed
  else
    seed % 5 == 0

def rangeBoolMixedConditionId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  if Id.run count < seed then
    pure (seed == 0)
  else
      let f (a b c d e : UInt64) : Id (Id UInt64) := pure (pure (a + 3*b + 5*c + 7*d + 11*e + seed))
      let value : Id UInt64 := Id.run do
        let mut a := Id.run (Id.run (f seed 1 2 3 4))
        for i in [:(Id.run count).toNat] do
          a := Id.run (Id.run (f a i.toUInt64 1 2 3))
        return a
      pure (Id.run value == Id.run (Id.run (f seed 1 2 3 4)))

def rangeBoolMixedConditionCapture (count seed : UInt64) : Id Bool :=
  let threshold := seed + count
  let selected := threshold % 5 == 0
  if selected then
      let f := fun x : UInt64 => x + seed
      let g := fun x : UInt64 => f (x * 3) + f x
      let value := Id.run do
        let mut a := g 0
        for i in [:count.toNat] do
          a := g (a + i.toUInt64)
        return a
      pure (g value == g seed)
  else
    pure (threshold == seed)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopMixedConditionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionScalarLeft, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionScalarLeft x y).toUInt64), true),
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionScalarRight, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionScalarRight x y).toUInt64), true),
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionFlag, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionNested, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionNested x y).toUInt64), true),
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionHelper, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionHelper x y).toUInt64), true),
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionBooleanHelper, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionBooleanHelper x y).toUInt64), true),
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionContinue, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionContinue x y).toUInt64), true),
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionStride, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionStride x y).toUInt64), true),
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionId, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionId x y).toUInt64), true),
    (`BooleanLoopMixedConditionTest.rangeBoolMixedConditionCapture, (fun (x y : UInt64) => (BooleanLoopMixedConditionTest.rangeBoolMixedConditionCapture x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop mixed-condition extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopMixedConditionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop mixed-condition IR comparisons passed"
