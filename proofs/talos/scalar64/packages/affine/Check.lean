import LeanExe.Examples.Arithmetic
import Project.Correct.Scalar64.Pilots
import Project.Correct.Scalar64.Certificate

namespace ScalarPackageCheck
open Project.Correct.Scalar64
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def claim : Certificate (UInt64 × UInt64) (fun input => [input.1, input.2]) (fun input => LeanExe.Examples.Arithmetic.affine input.1 input.2) := Project.Correct.Scalar64.Pilots.affineCertificate
def bytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 126, 126, 1, 126, 3, 2, 1, 0, 7, 10, 1, 6, 97, 102, 102, 105, 110, 101, 0, 0, 10, 18, 1, 16, 0, 32, 0, 66, 3, 126, 32, 1, 66, 2, 126, 124, 66, 7, 124, 11]
def raw : RawModule := { sections := [.type, .function, .export, .code], types := [{ params := List.replicate 2 .i64, results := [.i64] }], functionTypeIndices := [0], memories := [], globals := [], exports := [{ name := { bytes := [97, 102, 102, 105, 110, 101], text := "affine" }, desc := .func 0 }], codes := [{ locals := [], body := [(.localGet 0), (.i64Const (3)), (.i64Mul), (.localGet 1), (.i64Const (2)), (.i64Mul), (.i64Add), (.i64Const (7)), (.i64Add)] }] }
theorem coreMatches : claim.core = [(.wordBin .w64 .add (.wordBin .w64 .add (.wordBin .w64 .mul (.var 0) (.word .w64 3)) (.wordBin .w64 .mul (.var 1) (.word .w64 2))) (.word .w64 7))] := by rfl
theorem signaturesMatch : claim.signatures = [{ params := List.replicate 2 (.word .w64), result := .word .w64 }] := by rfl
theorem coreEntryMatches : claim.coreEntry = 0 := by rfl
theorem irMatches : claim.functions = [{ arity := 2, localCount := 0, scratch := 2, body := (.skip), result := (.bin .add (.bin .add (.bin .mul (.get 0) (.const 3)) (.bin .mul (.get 1) (.const 2))) (.const 7)) }] := by rfl
theorem entryMatches : claim.entry = 0 := by rfl
theorem exportMatches : claim.exportName = "affine" := by rfl
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
