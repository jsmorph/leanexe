import LeanExe.Correct.Scalar64.Arithmetic
import LeanExe.Examples.ScalarHelper

namespace LeanExe.Correct.Scalar64
open LeanExe.TypeSafety

def combineBody : Expr := .wordBin .w64 .add
  (.wordBin .w64 .mul (.var 0) (.word .w64 5)) (.var 1)

def helperBody : Expr := .letE
  (.call 0 [.wordBin .w64 .add (.var 0) (.word .w64 1),
    .wordBin .w64 .mul (.var 1) (.word .w64 2)])
  (.wordBin .w64 .add (.var 0) (.var 1))

theorem combine_source (x y : UInt64) : Runs program combineBody (encodeArgs [x, y])
    (encodeWord (LeanExe.Examples.ScalarHelper.combine x y)) :=
  Runs.add (Runs.mul (Runs.var rfl) Runs.word) (Runs.var rfl)

theorem helper_source (x y : UInt64) :
    Runs [combineBody, helperBody] helperBody (encodeArgs [x, y])
      (encodeWord (LeanExe.Examples.ScalarHelper.caller x y)) := by
  unfold helperBody LeanExe.Examples.ScalarHelper.caller
  apply Runs.letE
    (Runs.call2 rfl (Runs.add (Runs.var rfl) Runs.word)
      (Runs.mul (Runs.var rfl) Runs.word) (combine_source (x + 1) (y * 2)))
  exact Runs.add (Runs.var rfl) (Runs.var rfl)

def helperCertificate : SourceCertificate (UInt64 × UInt64)
    (fun input => [input.1, input.2])
    (fun input => LeanExe.Examples.ScalarHelper.caller input.1 input.2)
    [combineBody, helperBody] [binarySignature, binarySignature] 1 where
  body := helperBody
  arity := 2
  admitted := by decide
  bodyAt := rfl
  signatureAt := rfl
  argsLength := fun _ => rfl
  computes := fun input => helper_source input.1 input.2

end LeanExe.Correct.Scalar64
