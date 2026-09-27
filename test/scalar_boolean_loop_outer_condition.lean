import LeanExe.Extract.ScalarFunc

namespace BooleanLoopOuterConditionTest

def rangeBoolOuterConditionEqual (count seed : UInt64) : Bool :=
  if seed == 0 then
      let f := fun x : UInt64 => x + seed + 1
      let value := Id.run do
        let mut a := f seed
        for i in [:count.toNat] do
          a := f a + f i.toUInt64
        return a
      f value == f (f seed)
  else
      let f := fun x : UInt64 => x + seed % 5 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := f (a + i.toUInt64)
          if a % 7 == 0 then break
        return a
      f value % 7 == 0

def rangeBoolOuterConditionOrder (count seed : UInt64) : Bool :=
  if seed < count then
      let limit := fun x : UInt64 => x % 17
      let value := Id.run do
        let mut a := seed
        for i in [:(limit count).toNat] do
          a := a + i.toUInt64 + 1
        return a
      value == seed + limit count
  else
      let f := fun x : UInt64 => x * 3 + seed
      let value := Id.run do
        let mut a := f 0
        for i in [:count.toNat] do
          a := a + f i.toUInt64
        return a
      value == f 0

def rangeBoolOuterConditionFlag (count : UInt64) (flag : Bool) : Bool :=
  if flag then
      let f := fun x : UInt64 => if flag then x + 7 else x - 3
      let value := Id.run do
        let mut a := f count
        for i in [:count.toNat] do
          a := f (a + i.toUInt64)
        return a
      flag && value == f count
  else
      let f := fun input : Bool => if flag && input then count + 7 else count - 3
      let value := Id.run do
        let mut a := f flag
        for i in [:count.toNat] do
          a := a + f (i.toUInt64 % 2 == 0)
        return a
      flag && value == f flag

def rangeBoolOuterConditionNested (count seed : UInt64) : Bool :=
  if seed % 3 == 0 then
    if seed < count then
        let limit := fun x : UInt64 => x % 17
        let value := Id.run do
          let mut a := seed
          for i in [:(limit count).toNat] do
            a := a + i.toUInt64 + 1
          return a
        value == seed + limit count
    else
        let f := fun x : UInt64 => x * 3 + seed
        let value := Id.run do
          let mut a := f 0
          for i in [:count.toNat] do
            a := a + f i.toUInt64
          return a
        value == f 0
  else
      let f := fun x : UInt64 => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value == f seed

def rangeBoolOuterConditionHelper (count seed : UInt64) : Bool :=
  let p := fun x : UInt64 => x % 3 == seed % 3
  if p count then
      let f := fun x : UInt64 => x + seed + 1
      let value := Id.run do
        let mut a := f seed
        for i in [:count.toNat] do
          a := f a + f i.toUInt64
        return a
      f value == f (f seed)
  else
      let f := fun x : UInt64 => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value == f seed

def rangeBoolOuterConditionExit (count seed : UInt64) : Bool :=
  if count != 0 then
      let f := fun x y : UInt64 => x + 3 * y + seed % 5 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := f a i.toUInt64
          if a % 7 == 0 then break
        return a
      f value 1 % 7 == 0
  else
      let f := fun flag : Bool => seed % 5 + flag.toUInt64 + 1
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          a := a + f (i.toUInt64 % 2 == 0)
          if a % 7 == 0 then break
        return a
      f (value % 7 == 0) == f true

def rangeBoolOuterConditionContinue (count seed : UInt64) : Bool :=
  if seed % 2 == 0 then
      let f := fun x : UInt64 => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value == f seed
  else
      let f := fun x y z : UInt64 => (x + 3 * y + 5 * z) % 3
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do
          if f i.toUInt64 a seed == 0 then continue
          a := a + i.toUInt64 + 1
        return a
      f value seed 1 == f seed value 1

def rangeBoolOuterConditionStride (count seed : UInt64) : Bool :=
  if seed < count then
      let f := fun (_unit : Unit) (x : UInt64) => x % 3
      let value := Id.run do
        let mut a := seed
        for i in [(f () seed).toNat:count.toNat:3] do
          a := a + i.toUInt64 + 1
          if a % 5 == 0 then break
        return a
      f () value == f () seed
  else
      let f := fun a b c d e : UInt64 => (a + 3*b + 5*c + 7*d + 11*e) % 3
      let value := Id.run do
        let mut a := seed
        for i in [(f seed 1 2 3 4).toNat:count.toNat:3] do
          a := a + i.toUInt64 + 1
          if a % 5 == 0 then break
        return a
      f value 1 2 3 4 == f seed 1 2 3 4

def rangeBoolOuterConditionId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  if Id.run count < seed then
      let f (x : UInt64) : Id (Id UInt64) := pure (pure (x + seed + 1))
      let value : Id UInt64 := Id.run do
        let mut a := Id.run (Id.run (f 0))
        for i in [:(Id.run count).toNat] do
          a := Id.run (Id.run (f (a + i.toUInt64)))
        return a
      pure (Id.run (Id.run (f (Id.run value))) == seed)
  else
      let f (a b c d e : UInt64) : Id (Id UInt64) := pure (pure (a + 3*b + 5*c + 7*d + 11*e + seed))
      let value : Id UInt64 := Id.run do
        let mut a := Id.run (Id.run (f seed 1 2 3 4))
        for i in [:(Id.run count).toNat] do
          a := Id.run (Id.run (f a i.toUInt64 1 2 3))
        return a
      pure (Id.run value == Id.run (Id.run (f seed 1 2 3 4)))

def rangeBoolOuterConditionCapture (count seed : UInt64) : Id Bool :=
  let threshold := seed + count
  let selected := threshold % 5 == 0
  if selected then
      let f := fun flag : Bool => seed + flag.toUInt64
      let g := fun flag : Bool => f (!flag) + f flag
      let value := Id.run do
        let mut a := g false
        for i in [:count.toNat] do
          a := a + g (i.toUInt64 % 3 == 0)
        return a
      pure (value == g (seed == 0))
  else
      let f := fun x : UInt64 => x + seed
      let g := fun x : UInt64 => f (x * 3) + f x
      let value := Id.run do
        let mut a := g 0
        for i in [:count.toNat] do
          a := g (a + i.toUInt64)
        return a
      pure (g value == g seed)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopOuterConditionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionEqual, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionEqual x y).toUInt64), true),
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionOrder, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionOrder x y).toUInt64), true),
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionFlag, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionNested, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionNested x y).toUInt64), true),
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionHelper, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionHelper x y).toUInt64), true),
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionExit, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionExit x y).toUInt64), true),
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionContinue, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionContinue x y).toUInt64), true),
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionStride, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionStride x y).toUInt64), true),
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionId, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionId x y).toUInt64), true),
    (`BooleanLoopOuterConditionTest.rangeBoolOuterConditionCapture, (fun (x y : UInt64) => (BooleanLoopOuterConditionTest.rangeBoolOuterConditionCapture x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop outer-condition extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopOuterConditionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop outer-condition IR comparisons passed"
