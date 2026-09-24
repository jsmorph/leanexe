import LeanExe.Examples.TalosGcd
import Project.Correct.Scalar64.Gcd
import Project.Correct.Scalar64.Certificate

namespace ScalarPackageCheck
open Project.Correct.Scalar64
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def claim : Certificate (UInt64 × UInt64) (fun input => [input.1, input.2]) (fun input => LeanExe.Examples.TalosGcd.gcd input.1 input.2) := Project.Correct.Scalar64.Pilots.gcdCertificate
def bytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 126, 126, 1, 126, 3, 2, 1, 0, 7, 7, 1, 3, 103, 99, 100, 0, 0, 10, 58, 1, 56, 1, 3, 126, 2, 64, 3, 64, 32, 1, 66, 0, 82, 69, 13, 1, 32, 0, 33, 3, 32, 1, 33, 4, 32, 4, 66, 0, 81, 4, 126, 32, 3, 5, 32, 3, 32, 4, 130, 11, 33, 2, 32, 1, 33, 0, 32, 2, 33, 1, 12, 0, 11, 11, 32, 0, 11]
def raw : RawModule := { sections := [.type, .function, .export, .code], types := [{ params := List.replicate 2 .i64, results := [.i64] }], functionTypeIndices := [0], memories := [], globals := [], exports := [{ name := { bytes := [103, 99, 100], text := "gcd" }, desc := .func 0 }], codes := [{ locals := [{ count := 3, type := .i64 }], body := [(.block .empty [(.loop .empty [(.localGet 1), (.i64Const (0)), (.i64Ne), (.i32Eqz), (.brIf 1), (.localGet 0), (.localSet 3), (.localGet 1), (.localSet 4), (.localGet 4), (.i64Const (0)), (.i64Eq), (.iff (.value .i64) [(.localGet 3)] (some [(.localGet 3), (.localGet 4), (.i64RemU)])), (.localSet 2), (.localGet 1), (.localSet 0), (.localGet 2), (.localSet 1), (.br 0)])]), (.localGet 0)] }] }
theorem coreMatches : claim.core = [(.ifE (.wordCmp .w64 .eq (.var 1) (.word .w64 0)) (.var 0) (.call 0 [(.var 1), (.wordBin .w64 .mod (.var 0) (.var 1))]))] := by rfl
theorem signaturesMatch : claim.signatures = [{ params := List.replicate 2 (.word .w64), result := .word .w64 }] := by rfl
theorem coreEntryMatches : claim.coreEntry = 0 := by rfl
theorem irMatches : claim.functions = [{ arity := 2, localCount := 3, scratch := 3, body := (.loop (.ne (.get 1) (.const 0)) (.seq (.assign 2 (.bin .remU (.get 0) (.get 1))) (.seq (.assign 0 (.get 1)) (.assign 1 (.get 2))))), result := (.get 0) }] := by rfl
theorem entryMatches : claim.entry = 0 := by rfl
theorem exportMatches : claim.exportName = "gcd" := by rfl
theorem arityMatches : claim.function.arity = 2 := by rfl
theorem decoded : decode bytes = .ok raw := by cbv
theorem validated : Validator.validateRaw raw = .ok () := by rfl
theorem translated : Translation.module raw = claim.module := by rfl
theorem closed : Artifact claim bytes := Artifact.of_parts claim decoded validated translated

def correctness (α : Type) := Artifact.valid_and_correct (α := α) claim closed
#print axioms correctness
#print axioms coreMatches
#print axioms signaturesMatch
#print axioms irMatches
#print axioms closed
end ScalarPackageCheck
