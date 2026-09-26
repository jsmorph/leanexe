import LeanExe.Extract.Core

/-! Narrow numerals retain their selected instance; standard instances fold. -/
namespace NarrowNumeralEvidence

@[instance_reducible] def unusualByte : OfNat UInt8 300 := ⟨91⟩
@[instance_reducible] def unusualWord : OfNat UInt32 4294967297 := ⟨93⟩

def standardByte : UInt64 := (300 : UInt8).toUInt64
def customByte : UInt64 := (@OfNat.ofNat UInt8 300 unusualByte).toUInt64
def standardWord : UInt64 := (4294967297 : UInt32).toUInt64
def customWord : UInt64 := (@OfNat.ofNat UInt32 4294967297 unusualWord).toUInt64

end NarrowNumeralEvidence

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × UInt64) := [
    (`NarrowNumeralEvidence.standardByte, NarrowNumeralEvidence.standardByte),
    (`NarrowNumeralEvidence.customByte, NarrowNumeralEvidence.customByte),
    (`NarrowNumeralEvidence.standardWord, NarrowNumeralEvidence.standardWord),
    (`NarrowNumeralEvidence.customWord, NarrowNumeralEvidence.customWord)]
  for (name, expected) in cases do
    let some info := env.find? name | throwError "missing declaration {name}"
    let some value := info.value? | throwError "missing body {name}"
    let ctx : LeanExe.Extract.Core.Context := {
      env, root := `NarrowNumeralEvidence, names := #[], synthetics := #[],
      freshResultOwnerOffsets := #[], inlineStack := [] }
    match LeanExe.Extract.Core.extractExprFrom ctx [] 0 value with
    | .error error => throwError "{name}: extraction failed: {error}"
    | .ok (actual, nextLocal) =>
        if name == `NarrowNumeralEvidence.standardByte ||
            name == `NarrowNumeralEvidence.standardWord then
          unless actual == .u64 expected.toNat && nextLocal == 0 do
            throwError "{name}: expected folded source value {expected}, got {repr actual}"
    match LeanExe.Extract.Core.compileEnvironment env `NarrowNumeralEvidence name with
    | .error error => throwError "{name}: compilation failed: {error}"
    | .ok ir =>
        unless ir.evalFunc 0 [] == expected do
          throwError "{name}: compiled value differs from source"
