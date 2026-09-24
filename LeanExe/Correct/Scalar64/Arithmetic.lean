import LeanExe.Correct.Scalar64.Source
import LeanExe.Examples.Arithmetic

namespace LeanExe.Correct.Scalar64

open LeanExe.TypeSafety

theorem Runs.add (leftRun : Runs program left env (encodeWord a))
    (rightRun : Runs program right env (encodeWord b)) :
    Runs program (.wordBin .w64 .add left right) env (encodeWord (a + b)) := by
  simpa [encodeWord, evalWordBin, WordWidth.modulus, WordWidth.bits] using
    Runs.bin (op := .add) leftRun rightRun

theorem Runs.mul (leftRun : Runs program left env (encodeWord a))
    (rightRun : Runs program right env (encodeWord b)) :
    Runs program (.wordBin .w64 .mul left right) env (encodeWord (a * b)) := by
  simpa [encodeWord, evalWordBin, WordWidth.modulus, WordWidth.bits] using
    Runs.bin (op := .mul) leftRun rightRun

theorem Runs.eq (leftRun : Runs program left env (encodeWord a))
    (rightRun : Runs program right env (encodeWord b)) :
    Runs program (.wordCmp .w64 .eq left right) env (.bool (a == b)) := by
  have same : decide (a.toNat = b.toNat) = (a == b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq, UInt64.toNat_inj]
  simpa only [encodeWord, NatCmpOp.apply, same] using
    Runs.cmp (op := .eq) leftRun rightRun

def affineBody : Expr :=
  .wordBin .w64 .add
    (.wordBin .w64 .add
      (.wordBin .w64 .mul (.var 0) (.word .w64 3))
      (.wordBin .w64 .mul (.var 1) (.word .w64 2)))
    (.word .w64 7)

def chooseBody : Expr :=
  .ifE (.wordCmp .w64 .eq (.var 0) (.word .w64 0))
    (.wordBin .w64 .add (.var 1) (.word .w64 1))
    (.wordBin .w64 .add (.var 0) (.var 1))

def binarySignature : Signature :=
  { params := [.word .w64, .word .w64], result := .word .w64 }

theorem affine_source (x y : UInt64) :
    Runs program affineBody (encodeArgs [x, y])
      (encodeWord (LeanExe.Examples.Arithmetic.affine x y)) := by
  unfold affineBody LeanExe.Examples.Arithmetic.affine
  apply Runs.add
  · apply Runs.add
    · exact Runs.mul (Runs.var rfl) Runs.word
    · exact Runs.mul (Runs.var rfl) Runs.word
  · exact Runs.word

theorem choose_source (x y : UInt64) :
    Runs program chooseBody (encodeArgs [x, y])
      (encodeWord (LeanExe.Examples.Arithmetic.choose x y)) := by
  have condition : Runs program (.wordCmp .w64 .eq (.var 0) (.word .w64 0))
      (encodeArgs [x, y]) (.bool (x == 0)) := Runs.eq (Runs.var rfl) Runs.word
  unfold chooseBody LeanExe.Examples.Arithmetic.choose
  split
  next h =>
    apply Runs.ifTrue
    · simpa [h] using condition
    · exact Runs.add (Runs.var rfl) Runs.word
  next h =>
    apply Runs.ifFalse
    · simpa [h] using condition
    · exact Runs.add (Runs.var rfl) (Runs.var rfl)

def affineCertificate : SourceCertificate (UInt64 × UInt64)
    (fun input => [input.1, input.2])
    (fun input => LeanExe.Examples.Arithmetic.affine input.1 input.2)
    [affineBody] [binarySignature] 0 where
  body := affineBody
  arity := 2
  admitted := by decide
  bodyAt := rfl
  signatureAt := rfl
  argsLength := fun _ => rfl
  computes := fun input => affine_source input.1 input.2

def chooseCertificate : SourceCertificate (UInt64 × UInt64)
    (fun input => [input.1, input.2])
    (fun input => LeanExe.Examples.Arithmetic.choose input.1 input.2)
    [chooseBody] [binarySignature] 0 where
  body := chooseBody
  arity := 2
  admitted := by decide
  bodyAt := rfl
  signatureAt := rfl
  argsLength := fun _ => rfl
  computes := fun input => choose_source input.1 input.2

end LeanExe.Correct.Scalar64
