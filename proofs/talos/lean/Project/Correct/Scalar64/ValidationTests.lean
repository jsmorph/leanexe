import Project.Artifact.Binary.Proof.Validate
import Project.Artifact.Binary.ValidationParts
import Project.Correct.Scalar64.Encode

namespace Project.Correct.Scalar64
open Wasm.Binary

def memorylessExample : RawModule :=
  { sections := [.type, .function, .export, .code]
    types := [{ params := [], results := [.i64] }]
    functionTypeIndices := [0]
    memories := [], globals := []
    exports := [{ name := { bytes := [114, 117, 110], text := "run" }, desc := .func 0 }]
    codes := [{ locals := [], body := [.i64Const 42] }] }

example : Validator.validateRaw memorylessExample = .ok () := rfl
example : CoreValid memorylessExample := Proof.validateRaw_sound rfl

def oneMemoryExample : RawModule :=
  { memorylessExample with
    sections := [.type, .function, .memory, .export, .code],
    memories := [{ limits := { min := 0, max := none } }] }

example : Validator.validateRaw oneMemoryExample = .ok () := rfl
example : CoreValid oneMemoryExample := Proof.validateRaw_sound rfl

example : (Validator.validateRaw { memorylessExample with
    codes := [{ locals := [], body := [.i32Const 0, .i64Load { align := 3, offset := 0 }] }] }).isOk = false := rfl

example : (Validator.validateRaw { memorylessExample with
    codes := [{ locals := [], body := [.localGet 8] }] }).isOk = false := rfl

example : (Validator.validateRaw { memorylessExample with
    codes := [{ locals := [], body := [.call 1] }] }).isOk = false := rfl

example : (Validator.validateRaw { oneMemoryExample with
    memories := oneMemoryExample.memories ++ oneMemoryExample.memories }).isOk = false := rfl

#print axioms Proof.validate_sound
#print axioms Executes.lower_spec
#print axioms assemble_implements

end Project.Correct.Scalar64
