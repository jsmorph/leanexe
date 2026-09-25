import LeanExe.Extract.Arithmetic

namespace ArithmeticModeTest

def expression (x y : UInt64) : UInt64 := ((x + 7) * (y - 3)) / (x % (y + 1))
def bits (x y : UInt64) : UInt64 := ((x &&& y) ||| (x ^^^ y)) <<< (x >>> y)
def literal : UInt64 := 18446744073709551616
def binding (x : UInt64) : UInt64 := let y := x + 1; y * 2
def natBinding (x : UInt64) : UInt64 := let n : Nat := 3; x + UInt64.ofNat n
def customBinding (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 => z + 1
  f (x + y)
def branch (x : UInt64) : UInt64 := if x = 0 then 1 else x
def sequential (x : UInt64) : UInt64 := Id.run do
  let mut y := x
  y := y + 1
  let z ← pure (y * 2)
  return z
@[instance_reducible] def customPure : Pure Id := ⟨fun value => value⟩
@[instance_reducible] def customBind : Bind Id := ⟨fun value next => next value⟩
def customReturn (x : UInt64) : UInt64 := Id.run (@Pure.pure Id customPure UInt64 x)
def customSequence (x : UInt64) : UInt64 :=
  Id.run (@Bind.bind Id customBind UInt64 UInt64 x (fun y => y + 1))
def joinedChoice (x y : UInt64) : UInt64 := Id.run do
  let a ← if x < y then pure (x + 1) else pure (y - 1)
  return a * x
def binaryLocalFunction (x : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a + b
  f x x
def unsupportedLocalBody (x : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => expression z x
  x

def range (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    a := a + UInt64.ofNat i
  return a
def rangeNonUnitStep (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [0:n.toNat:2] do
    a := a + UInt64.ofNat i
  return a
def rangeBreak (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    if a == 7 then break
    a := a + 1
  return a
def rangeTwice (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    a := a + 1
  for _ in [:n.toNat] do
    a := a * 3
  return a
def rangeLocal (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let f := fun x : UInt64 => x + UInt64.ofNat i
    a := f a
  return a
def rangeUnsupportedFunction (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    let _f := fun x : UInt64 => expression x a
    a := a + 1
  return a
def rangeBinaryFunction (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    let f := fun x y : UInt64 => x + y
    a := f a a
  return a
def rangeBind (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let delta ← pure (UInt64.ofNat i)
    a := a + delta
  return a
def rangeCustomBind (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun i a =>
    @Bind.bind Id customBind UInt64 (ForInStep UInt64)
      (pure (UInt64.ofNat i)) (fun delta => pure (.yield (a + delta)))
def rangeBindBreak (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let delta ← pure (UInt64.ofNat i)
    if delta == 2 then break
    a := a + delta
  return a
def rangeJoined (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    let index := UInt64.ofNat i
    let delta ← if a < 7 then pure (a + index) else pure (seed / index)
    a := a + delta
  return a
def rangeUnusedDone (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    let _bad : UInt64 → Id (ForInStep UInt64) := fun x => pure (.done x)
    a := a + 1
  return a

def helper (x : UInt64) : UInt64 := expression x 3
def wrongType (x : Nat) : Nat := x + 1
def retain (x : UInt64) : UInt64 := x + 1
@[instance_reducible] def custom : HAdd UInt64 UInt64 UInt64 := ⟨UInt64.sub⟩
def customAdd (x y : UInt64) : UInt64 := @HAdd.hAdd _ _ _ custom x y

@[instance_reducible] def reversedLT : LT UInt64 := ⟨fun x y => y < x⟩
@[instance_reducible] def neverEqual : BEq UInt64 := ⟨fun _ _ => false⟩
def customOrder (x y : UInt64) : UInt64 :=
  if @LT.lt UInt64 reversedLT x y then x else y
def customEquality (x y : UInt64) : UInt64 :=
  if @BEq.beq UInt64 neverEqual x y then x else y
def customDecision (x y : UInt64) : Decidable (x = y) := inferInstance
def customDecisionBranch (x y : UInt64) : UInt64 := @ite UInt64 (x = y) (customDecision x y) x y
def rangeCustomOrder (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    if @LT.lt UInt64 reversedLT a (UInt64.ofNat i) then a := a + 1
  return a

end ArithmeticModeTest

run_elab do
  let env ← Lean.getEnv
  for name in [`ArithmeticModeTest.expression, `ArithmeticModeTest.bits, `ArithmeticModeTest.literal,
      `ArithmeticModeTest.binding, `ArithmeticModeTest.branch, `ArithmeticModeTest.sequential,
      `ArithmeticModeTest.customBinding, `ArithmeticModeTest.joinedChoice,
      `ArithmeticModeTest.range, `ArithmeticModeTest.rangeLocal,
      `ArithmeticModeTest.rangeBind, `ArithmeticModeTest.rangeJoined] do
    match LeanExe.Extract.Arithmetic.compileEnvironment env `ArithmeticModeTest name with
    | .error message => throwError "arithmetic mode rejected {name}: {message}"
    | .ok module_ =>
      match LeanExe.Extract.Core.compileEnvironment env `ArithmeticModeTest name with
      | .error message => throwError "normal compiler rejected {name}: {message}"
      | .ok normal =>
        unless LeanExe.Wasm.Binary.CoreWasm.moduleBytes module_ ==
            LeanExe.Wasm.Binary.CoreWasm.moduleBytes normal do
          throwError "arithmetic mode changed production bytes for {name}"
  for name in [`ArithmeticModeTest.natBinding, `ArithmeticModeTest.binaryLocalFunction,
      `ArithmeticModeTest.unsupportedLocalBody, `ArithmeticModeTest.rangeNonUnitStep,
      `ArithmeticModeTest.rangeBreak, `ArithmeticModeTest.rangeTwice,
      `ArithmeticModeTest.rangeUnsupportedFunction, `ArithmeticModeTest.rangeBinaryFunction,
      `ArithmeticModeTest.rangeCustomBind, `ArithmeticModeTest.rangeBindBreak,
      `ArithmeticModeTest.rangeUnusedDone, `ArithmeticModeTest.rangeCustomOrder,
      `ArithmeticModeTest.customReturn, `ArithmeticModeTest.customSequence,
      `ArithmeticModeTest.customOrder, `ArithmeticModeTest.customEquality, `ArithmeticModeTest.customDecisionBranch, `ArithmeticModeTest.helper,
      `ArithmeticModeTest.wrongType, `ArithmeticModeTest.retain, `ArithmeticModeTest.customAdd,
      `ArithmeticModeTest.missing] do
    match LeanExe.Extract.Arithmetic.compileEnvironment env `ArithmeticModeTest name with
    | .ok _ => throwError "arithmetic mode accepted excluded source {name}"
    | .error _ => pure ()
  let oversized : LeanExe.IR.Func :=
    { sourceName := `oversized, exportName := some "oversized", params := 2 ^ 32,
      locals := 0, body := .skip, results := [] }
  if LeanExe.Wasm.ArithmeticBounds.Fits oversized "oversized" then
    throwError "arithmetic format check accepted an out-of-range parameter count"
