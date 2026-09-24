import LeanExe.Extract.Core

/-! Regression for source class evidence in the actual production extractor.
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
    (`ScalarClassEvidence.standardBranch, ScalarClassEvidence.standardBranch)]
  let inputs : List (UInt64 × UInt64) := [(10, 3), (0, 0), (1, 64), (0xffffffffffffffff, 1)]
  for (name, source) in cases do
    match LeanExe.Extract.Core.compileEnvironment env `ScalarClassEvidence name with
    | .error error => throwError "{name}: extraction failed: {error}"
    | .ok ir =>
      for (x, y) in inputs do
        let actual := ir.evalFunc 0 [x, y]
        let expected := source x y
        unless actual == expected do
          throwError "{name}({x}, {y}): source={expected}, extracted={actual}"
