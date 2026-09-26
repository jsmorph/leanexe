import LeanExe.Extract.ScalarExpr
import LeanExe.Extract.Syntax

namespace BinaryFunctionTest

def binaryOrder (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a - b
  f x y

def binaryCapture (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b : UInt64 => captured + a * 3 - b
  let captured := y * 11
  f captured x

def binaryChained (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a / b + a % b
  let g := fun a b : UInt64 => f (a + b) (a - b)
  g x y

def binaryUnused (x y : UInt64) : UInt64 :=
  let _f := fun a b : UInt64 => (a + x) / (b - y)
  x + y

def binaryDo (x y : UInt64) : UInt64 := Id.run do
  let f : UInt64 → UInt64 → Id UInt64 := fun a b => do
    let c ← pure (a + b)
    return c * x
  let result ← f x y
  return result + x

def binaryNested (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 =>
    let g := fun c d : UInt64 => a * c + b * d
    g x y
  f y x

def binaryChoice (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => if a < b then a + 7 else b - a
  if f x y = x then f y x else f (x + y) (x - y)

def binaryArguments (x y : UInt64) : UInt64 :=
  let g := fun a : UInt64 => a * 3 + 1
  let f := fun a b : UInt64 => a ^^^ (b <<< a)
  f (g x) (g y)

def binaryWrapped (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => Id.run do
    let c ← if a < b then pure (a + 1) else pure (b + 7)
    return c - a
  f x y

def helper (x : UInt64) : UInt64 := x + 1
def unusedUnsupported (x y : UInt64) : UInt64 :=
  let _f := fun a b : UInt64 => helper a + b
  x + y

def ternary (x y : UInt64) : UInt64 :=
  let f := fun a b c : UInt64 => a + b + c
  f x y x

def partiallyApplied (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a + b
  let g := f x
  g y

def wrongDomain (x y : UInt64) : UInt64 :=
  let f := fun (a : UInt64) (b : Bool) => if b then a else y
  f x true

end BinaryFunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BinaryFunctionTest.binaryOrder, BinaryFunctionTest.binaryOrder),
    (`BinaryFunctionTest.binaryCapture, BinaryFunctionTest.binaryCapture),
    (`BinaryFunctionTest.binaryChained, BinaryFunctionTest.binaryChained),
    (`BinaryFunctionTest.binaryUnused, BinaryFunctionTest.binaryUnused),
    (`BinaryFunctionTest.binaryDo, BinaryFunctionTest.binaryDo),
    (`BinaryFunctionTest.binaryNested, BinaryFunctionTest.binaryNested),
    (`BinaryFunctionTest.binaryChoice, BinaryFunctionTest.binaryChoice),
    (`BinaryFunctionTest.binaryArguments, BinaryFunctionTest.binaryArguments),
    (`BinaryFunctionTest.binaryWrapped, BinaryFunctionTest.binaryWrapped),
    (`BinaryFunctionTest.ternary, BinaryFunctionTest.ternary)]
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
     (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
     (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]
  let locals : List LeanExe.Extract.Core.ScalarBinding := [.word (.local 1), .word (.local 0)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some body := LeanExe.Extract.Core.collectLambdas value 2 | throwError "missing parameters"
    let some result := LeanExe.Extract.Core.extractScalarExprWith locals body |
      throwError "{name}: two-argument function extraction failed"
    let func : LeanExe.IR.Func := { sourceName := name, exportName := some "entry", params := 2, locals := 2, body := .skip, results := [result] }
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BinaryFunctionTest.unusedUnsupported,
      `BinaryFunctionTest.partiallyApplied, `BinaryFunctionTest.wrongDomain] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some body := LeanExe.Extract.Core.collectLambdas value 2 | throwError "missing parameters"
    unless (LeanExe.Extract.Core.extractScalarExprWith locals body).isNone do
      throwError "{name}: unsupported function accepted"
  Lean.logInfo "140 native/local-function IR comparisons and three rejection tests passed"
