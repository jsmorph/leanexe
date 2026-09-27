import LeanExe.Extract.ScalarFunc

namespace BooleanAccumulatorTest

def rangeBooleanAccumulatorToggle (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for _ in [:count.toNat] do
    flag := !flag
  return flag

def rangeBooleanAccumulatorIndex (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed % 3 == 0
  for i in [:count.toNat] do
    flag := flag != (i.toUInt64 % 3 == seed % 3)
  return flag

def rangeBooleanAccumulatorChoice (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    if i.toUInt64 % 2 == 0 then flag := !flag
    else flag := flag || i.toUInt64 == seed
  return flag

def rangeBooleanAccumulatorBreak (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    flag := flag != (i.toUInt64 == seed)
    if flag then break
  return flag

def rangeBooleanAccumulatorContinue (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    if i.toUInt64 % 2 == 0 then continue
    flag := !flag
  return flag

def rangeBooleanAccumulatorStride (count seed : UInt64) : Id Bool := do
  let mut flag := seed == 0
  for i in [1:count.toNat:3] do
    flag := flag != (i.toUInt64 % 5 == 0)
  return flag

def rangeBooleanAccumulatorPredicate (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut flag := seed == 0
  for i in [:count.toNat] do
    flag := f flag || i.toUInt64 == seed
  return flag

def rangeBooleanAccumulatorInitial (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut flag := f (seed == 0)
  for i in [:count.toNat] do
    if f flag then break
    flag := i.toUInt64 == seed
  return f flag

def rangeBooleanAccumulatorWordTail (count seed : UInt64) : UInt64 :=
  let flag := Id.run do
    let mut a := seed == 0
    for i in [:count.toNat] do
      a := a != (i.toUInt64 == seed)
      if a then break
    return a
  if flag then seed + count else seed * 3

def rangeBooleanAccumulatorInput (count : UInt64) (seed : Bool) : Id Bool := do
  let mut flag := seed
  for i in [:count.toNat] do
    flag := flag != (i.toUInt64 % 3 == 0 || seed)
  return flag

def rangeBooleanAccumulatorHigh (count seed : UInt64) : Bool :=
  forIn (m := Id) [(18446744073709551615 - count).toNat:18446744073709551615:2] (seed == 0) fun i flag =>
    .yield (flag != (i.toUInt64 % 3 == seed % 3))

def rangeBooleanAccumulatorHuge (count seed : UInt64) : Bool :=
  forIn (m := Id) [0:count.toNat:18446744073709551615] (seed == 0) fun i flag =>
    .done (flag != (i.toUInt64 == seed))

end BooleanAccumulatorTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorToggle, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorToggle x y).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorIndex, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorIndex x y).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorChoice, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorChoice x y).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorBreak, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorBreak x y).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorContinue, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorContinue x y).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorStride, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorStride x y).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorPredicate, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorPredicate x y).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorInitial, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorInitial x y).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorWordTail, (fun (x y : UInt64) => BooleanAccumulatorTest.rangeBooleanAccumulatorWordTail x y)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorInput, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorInput x (y != 0)).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorHigh, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorHigh x y).toUInt64)),
    (`BooleanAccumulatorTest.rangeBooleanAccumulatorHuge, (fun (x y : UInt64) => (BooleanAccumulatorTest.rangeBooleanAccumulatorHuge x y).toUInt64))]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean accumulator extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
  unless comparisons == 288 do throwError "unexpected count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean accumulator IR comparisons passed"
