import LeanExe.Extract.Arithmetic

namespace ArithmeticModeTest

def expression (x y : UInt64) : UInt64 := ((x + 7) * (y - 3)) / (x % (y + 1))
def bits (x y : UInt64) : UInt64 := ((x &&& y) ||| (x ^^^ y)) <<< (x >>> y)
def literal : UInt64 := 18446744073709551616
def binding (x : UInt64) : UInt64 := let y := x + 1; y * 2
def branch (x : UInt64) : UInt64 := if x = 0 then 1 else x
def helper (x : UInt64) : UInt64 := expression x 3
def wrongType (x : Nat) : Nat := x + 1
def retain (x : UInt64) : UInt64 := x + 1
@[instance_reducible] def custom : HAdd UInt64 UInt64 UInt64 := ⟨UInt64.sub⟩
def customAdd (x y : UInt64) : UInt64 := @HAdd.hAdd _ _ _ custom x y

end ArithmeticModeTest

run_elab do
  let env ← Lean.getEnv
  for name in [`ArithmeticModeTest.expression, `ArithmeticModeTest.bits, `ArithmeticModeTest.literal] do
    match LeanExe.Extract.Arithmetic.compileEnvironment env `ArithmeticModeTest name with
    | .error message => throwError "arithmetic mode rejected {name}: {message}"
    | .ok module_ =>
      match LeanExe.Extract.Core.compileEnvironment env `ArithmeticModeTest name with
      | .error message => throwError "normal compiler rejected {name}: {message}"
      | .ok normal =>
        unless LeanExe.Wasm.Binary.CoreWasm.moduleBytes module_ ==
            LeanExe.Wasm.Binary.CoreWasm.moduleBytes normal do
          throwError "arithmetic mode changed production bytes for {name}"
  for name in [`ArithmeticModeTest.binding, `ArithmeticModeTest.branch, `ArithmeticModeTest.helper,
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
