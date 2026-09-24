import LeanExe.Examples.ScalarHelper
import Project.Correct.Scalar64.Pilots
import Project.Correct.Scalar64.Certificate

namespace ScalarPackageCheck
open Project.Correct.Scalar64
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def claim : Certificate (UInt64 × UInt64) (fun input => [input.1, input.2]) (fun input => LeanExe.Examples.ScalarHelper.caller input.1 input.2) := Project.Correct.Scalar64.Pilots.helperCertificate
def bytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 13, 2, 96, 2, 126, 126, 1, 126, 96, 2, 126, 126, 1, 126, 3, 3, 2, 0, 1, 7, 10, 1, 6, 104, 101, 108, 112, 101, 114, 0, 1, 10, 36, 2, 10, 0, 32, 0, 66, 5, 126, 32, 1, 124, 11, 23, 1, 1, 126, 32, 0, 66, 1, 124, 32, 1, 66, 2, 126, 16, 0, 33, 2, 32, 2, 32, 0, 124, 11]
def raw : RawModule := { sections := [.type, .function, .export, .code], types := [{ params := List.replicate 2 .i64, results := [.i64] }, { params := List.replicate 2 .i64, results := [.i64] }], functionTypeIndices := [0, 1], memories := [], globals := [], exports := [{ name := { bytes := [104, 101, 108, 112, 101, 114], text := "helper" }, desc := .func 1 }], codes := [{ locals := [], body := [(.localGet 0), (.i64Const (5)), (.i64Mul), (.localGet 1), (.i64Add)] }, { locals := [{ count := 1, type := .i64 }], body := [(.localGet 0), (.i64Const (1)), (.i64Add), (.localGet 1), (.i64Const (2)), (.i64Mul), (.call 0), (.localSet 2), (.localGet 2), (.localGet 0), (.i64Add)] }] }
theorem coreMatches : claim.core = [(.wordBin .w64 .add (.wordBin .w64 .mul (.var 0) (.word .w64 5)) (.var 1)), (.letE (.call 0 [(.wordBin .w64 .add (.var 0) (.word .w64 1)), (.wordBin .w64 .mul (.var 1) (.word .w64 2))]) (.wordBin .w64 .add (.var 0) (.var 1)))] := by rfl
theorem signaturesMatch : claim.signatures = [{ params := List.replicate 2 (.word .w64), result := .word .w64 }, { params := List.replicate 2 (.word .w64), result := .word .w64 }] := by rfl
theorem coreEntryMatches : claim.coreEntry = 1 := by rfl
theorem irMatches : claim.functions = [{ arity := 2, localCount := 0, scratch := 2, body := (.skip), result := (.bin .add (.bin .mul (.get 0) (.const 5)) (.get 1)) }, { arity := 2, localCount := 1, scratch := 3, body := (.call 2 0 [(.bin .add (.get 0) (.const 1)), (.bin .mul (.get 1) (.const 2))]), result := (.bin .add (.get 2) (.get 0)) }] := by rfl
theorem entryMatches : claim.entry = 1 := by rfl
theorem exportMatches : claim.exportName = "helper" := by rfl
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
