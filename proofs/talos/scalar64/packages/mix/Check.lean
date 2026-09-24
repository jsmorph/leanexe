import LeanExe.Examples.Prng
import Project.Correct.Scalar64.Pilots
import Project.Correct.Scalar64.Certificate

namespace ScalarPackageCheck
open Project.Correct.Scalar64
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def claim : Certificate (UInt64) (fun input => [input]) (LeanExe.Examples.Prng.mix) := Project.Correct.Scalar64.Pilots.mixCertificate
def bytes : ByteArray := ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0, 1, 6, 1, 96, 1, 126, 1, 126, 3, 2, 1, 0, 7, 7, 1, 3, 109, 105, 120, 0, 0, 10, 58, 1, 56, 1, 2, 126, 32, 0, 32, 0, 66, 30, 136, 133, 66, 185, 203, 147, 231, 209, 237, 145, 172, 191, 127, 126, 33, 1, 32, 1, 32, 1, 66, 27, 136, 133, 66, 235, 163, 196, 153, 177, 183, 146, 232, 148, 127, 126, 33, 2, 32, 2, 32, 2, 66, 31, 136, 133, 11]
def raw : RawModule := { sections := [.type, .function, .export, .code], types := [{ params := List.replicate 1 .i64, results := [.i64] }], functionTypeIndices := [0], memories := [], globals := [], exports := [{ name := { bytes := [109, 105, 120], text := "mix" }, desc := .func 0 }], codes := [{ locals := [{ count := 2, type := .i64 }], body := [(.localGet 0), (.localGet 0), (.i64Const (30)), (.i64ShrU), (.i64Xor), (.i64Const (-4658895280553007687)), (.i64Mul), (.localSet 1), (.localGet 1), (.localGet 1), (.i64Const (27)), (.i64ShrU), (.i64Xor), (.i64Const (-7723592293110705685)), (.i64Mul), (.localSet 2), (.localGet 2), (.localGet 2), (.i64Const (31)), (.i64ShrU), (.i64Xor)] }] }
theorem coreMatches : claim.core = [(.letE (.wordBin .w64 .mul (.wordBin .w64 .bitXor (.var 0) (.wordBin .w64 .shiftRight (.var 0) (.word .w64 30))) (.word .w64 13787848793156543929)) (.letE (.wordBin .w64 .mul (.wordBin .w64 .bitXor (.var 0) (.wordBin .w64 .shiftRight (.var 0) (.word .w64 27))) (.word .w64 10723151780598845931)) (.wordBin .w64 .bitXor (.var 0) (.wordBin .w64 .shiftRight (.var 0) (.word .w64 31)))))] := by rfl
theorem signaturesMatch : claim.signatures = [{ params := List.replicate 1 (.word .w64), result := .word .w64 }] := by rfl
theorem coreEntryMatches : claim.coreEntry = 0 := by rfl
theorem irMatches : claim.functions = [{ arity := 1, localCount := 2, scratch := 3, body := (.seq (.assign 1 (.bin .mul (.bin .bitXor (.get 0) (.bin .shiftRight (.get 0) (.const 30))) (.const 13787848793156543929))) (.assign 2 (.bin .mul (.bin .bitXor (.get 1) (.bin .shiftRight (.get 1) (.const 27))) (.const 10723151780598845931)))), result := (.bin .bitXor (.get 2) (.bin .shiftRight (.get 2) (.const 31))) }] := by rfl
theorem entryMatches : claim.entry = 0 := by rfl
theorem exportMatches : claim.exportName = "mix" := by rfl
theorem arityMatches : claim.function.arity = 1 := by rfl
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
