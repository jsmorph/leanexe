import LeanExe.Extract.Core

/-! Test for source class evidence in the actual production extractor.
This executable check is not a compiler-correctness theorem. -/

namespace ScalarClassEvidence

@[instance_reducible] def subtractingAdd : HAdd UInt64 UInt64 UInt64 := ⟨UInt64.sub⟩
@[instance_reducible] def addingSub : HSub UInt64 UInt64 UInt64 := ⟨UInt64.add⟩
@[instance_reducible] def addingMul : HMul UInt64 UInt64 UInt64 := ⟨UInt64.add⟩
@[instance_reducible] def unusualLiteral : OfNat UInt64 3 := ⟨41⟩

def customAdd (x y : UInt64) : UInt64 := @HAdd.hAdd _ _ _ subtractingAdd x y
def customSub (x y : UInt64) : UInt64 := @HSub.hSub _ _ _ addingSub x y
def customMul (x y : UInt64) : UInt64 := @HMul.hMul _ _ _ addingMul x y
def customLiteral (_x _y : UInt64) : UInt64 := @OfNat.ofNat _ 3 unusualLiteral
def standardAdd (x y : UInt64) : UInt64 := x + y
def standardSub (x y : UInt64) : UInt64 := x - y
def standardMul (x y : UInt64) : UInt64 := x * y
def standardDiv (x y : UInt64) : UInt64 := x / y
def standardMod (x y : UInt64) : UInt64 := x % y
def standardBits (x y : UInt64) : UInt64 := ((x ^^^ y) &&& x) ||| y
def standardShift (x y : UInt64) : UInt64 := (x <<< y) >>> y
def standardBranch (x y : UInt64) : UInt64 := if x < y then x + 1 else y + 2
def affine (x y : UInt64) : UInt64 := x * 3 + y * 2 + 7
def largeLiteral (_x _y : UInt64) : UInt64 := 18446744073709551616

end ScalarClassEvidence

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`ScalarClassEvidence.customAdd, ScalarClassEvidence.customAdd),
    (`ScalarClassEvidence.customSub, ScalarClassEvidence.customSub),
    (`ScalarClassEvidence.customMul, ScalarClassEvidence.customMul),
    (`ScalarClassEvidence.customLiteral, ScalarClassEvidence.customLiteral),
    (`ScalarClassEvidence.standardAdd, ScalarClassEvidence.standardAdd),
    (`ScalarClassEvidence.standardSub, ScalarClassEvidence.standardSub),
    (`ScalarClassEvidence.standardMul, ScalarClassEvidence.standardMul),
    (`ScalarClassEvidence.standardDiv, ScalarClassEvidence.standardDiv),
    (`ScalarClassEvidence.standardMod, ScalarClassEvidence.standardMod),
    (`ScalarClassEvidence.standardBits, ScalarClassEvidence.standardBits),
    (`ScalarClassEvidence.standardShift, ScalarClassEvidence.standardShift),
    (`ScalarClassEvidence.standardBranch, ScalarClassEvidence.standardBranch),
    (`ScalarClassEvidence.affine, ScalarClassEvidence.affine),
    (`ScalarClassEvidence.largeLiteral, ScalarClassEvidence.largeLiteral)]
  let inputs : List (UInt64 × UInt64) := [(10, 3), (0, 0), (1, 64), (0xffffffffffffffff, 1)]
  for (name, source) in cases do
    let some info := env.find? name | throwError "missing declaration {name}"
    let some value := info.value? | throwError "missing body {name}"
    let some body := LeanExe.Extract.Core.collectLambdas value 2 |
      throwError "missing parameters {name}"
    let expectedTree := ![
      `ScalarClassEvidence.customAdd, `ScalarClassEvidence.customSub,
      `ScalarClassEvidence.customMul, `ScalarClassEvidence.customLiteral].contains name
    let actualTree := (LeanExe.Extract.Core.extractScalarExpr [1, 0] body).isSome
    unless actualTree == expectedTree do
      throwError "{name}: raw source traversal acceptance mismatch"
    match LeanExe.Extract.Core.compileEnvironment env `ScalarClassEvidence name with
    | .error error => throwError "{name}: extraction failed: {error}"
    | .ok ir =>
      for (x, y) in inputs do
        let actual := ir.evalFunc 0 [x, y]
        let expected := source x y
        unless actual == expected do
          throwError "{name}({x}, {y}): source={expected}, extracted={actual}"
