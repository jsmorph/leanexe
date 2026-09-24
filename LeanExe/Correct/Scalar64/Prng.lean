import LeanExe.Correct.Scalar64.Bits
import LeanExe.Examples.Prng

namespace LeanExe.Correct.Scalar64
open LeanExe.TypeSafety

def mixBody : Expr :=
  .letE (.wordBin .w64 .mul
    (.wordBin .w64 .bitXor (.var 0) (.wordBin .w64 .shiftRight (.var 0) (.word .w64 30)))
    (.word .w64 0xbf58476d1ce4e5b9))
  (.letE (.wordBin .w64 .mul
    (.wordBin .w64 .bitXor (.var 0) (.wordBin .w64 .shiftRight (.var 0) (.word .w64 27)))
    (.word .w64 0x94d049bb133111eb))
  (.wordBin .w64 .bitXor (.var 0) (.wordBin .w64 .shiftRight (.var 0) (.word .w64 31))))

def unarySignature : Signature := { params := [.word .w64], result := .word .w64 }

theorem mix_source (state : UInt64) : Runs program mixBody (encodeArgs [state])
    (encodeWord (LeanExe.Examples.Prng.mix state)) := by
  unfold mixBody LeanExe.Examples.Prng.mix
  let z1 := (state ^^^ (state >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  apply Runs.letE (v := encodeWord z1)
  · exact Runs.mul (Runs.bitXor (Runs.var rfl) (Runs.shiftRight (Runs.var rfl) Runs.word)) Runs.word
  apply Runs.letE (v := encodeWord z2)
  · exact Runs.mul (Runs.bitXor (Runs.var rfl) (Runs.shiftRight (Runs.var rfl) Runs.word)) Runs.word
  exact Runs.bitXor (Runs.var rfl) (Runs.shiftRight (Runs.var rfl) Runs.word)

def mixCertificate : SourceCertificate UInt64 (fun state => [state])
    LeanExe.Examples.Prng.mix [mixBody] [unarySignature] 0 where
  body := mixBody
  arity := 1
  admitted := by decide
  bodyAt := rfl
  signatureAt := rfl
  argsLength := fun _ => rfl
  computes := mix_source

end LeanExe.Correct.Scalar64
