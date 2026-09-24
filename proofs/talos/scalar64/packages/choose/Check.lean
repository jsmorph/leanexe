import LeanExe.Examples.Arithmetic
import Project.Correct.Scalar64.Pilots
import Project.Correct.Scalar64.Certificate

namespace ScalarPackageCheck
open Project.Correct.Scalar64
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def claim : Certificate (UInt64 × UInt64) (fun input => [input.1, input.2]) (fun input => LeanExe.Examples.Arithmetic.choose input.1 input.2) := Project.Correct.Scalar64.Pilots.chooseCertificate
def bytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 126, 126, 1, 126, 3, 2, 1, 0, 7, 10, 1, 6, 99, 104, 111, 111, 115, 101, 0, 0, 10, 23, 1, 21, 0, 32, 0, 66, 0, 81, 4, 126, 32, 1, 66, 1, 124, 5, 32, 0, 32, 1, 124, 11, 11]
def raw : RawModule := { sections := [.type, .function, .export, .code], types := [{ params := List.replicate 2 .i64, results := [.i64] }], functionTypeIndices := [0], memories := [], globals := [], exports := [{ name := { bytes := [99, 104, 111, 111, 115, 101], text := "choose" }, desc := .func 0 }], codes := [{ locals := [], body := [(.localGet 0), (.i64Const (0)), (.i64Eq), (.iff (.value .i64) [(.localGet 1), (.i64Const (1)), (.i64Add)] (some [(.localGet 0), (.localGet 1), (.i64Add)]))] }] }
theorem coreMatches : claim.core = [(.ifE (.wordCmp .w64 .eq (.var 0) (.word .w64 0)) (.wordBin .w64 .add (.var 1) (.word .w64 1)) (.wordBin .w64 .add (.var 0) (.var 1)))] := by rfl
theorem signaturesMatch : claim.signatures = [{ params := List.replicate 2 (.word .w64), result := .word .w64 }] := by rfl
theorem coreEntryMatches : claim.coreEntry = 0 := by rfl
theorem irMatches : claim.functions = [{ arity := 2, localCount := 0, scratch := 2, body := (.skip), result := (.ite (.eq (.get 0) (.const 0)) (.bin .add (.get 1) (.const 1)) (.bin .add (.get 0) (.get 1))) }] := by rfl
theorem entryMatches : claim.entry = 0 := by rfl
theorem exportMatches : claim.exportName = "choose" := by rfl
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
