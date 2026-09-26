import Project.Compiler.ModuleSections
import Project.Compiler.FixedPayloadBounds
import Project.Compiler.UserPayloads
import Project.Compiler.CodePayloads

namespace Project.Compiler.ArithmeticModule

open Project.Compiler.Parsing
open Wasm.Binary

/-- Explicit format limits on the variable portions of a single-source-function
production module. These contain no semantic or decoder-success assumptions. -/
structure Bounds (func : LeanExe.IR.Func) (entry : String) : Prop where
  params : func.params < 2 ^ 32
  results : func.results.length < 2 ^ 32
  name : entry.toUTF8.size < 2 ^ 32
  types : (typePayload func).length < 2 ^ 32
  exports : (exportPayload entry).length < 2 ^ 32
  code : (codePayload func).length < 2 ^ 32

def rawModule (func : LeanExe.IR.Func) (entry : String) (user : Code) : RawModule :=
  { sections := [.type, .function, .memory, .global, .export, .code]
    types := typeValues func, functionTypeIndices := functionValues, memories := memoryValues
    globals := globalValues, exports := exportValues entry, codes := codeValues user }

def payloads (func : LeanExe.IR.Func) (entry : String) (user : Code)
    (parsed : Parses code (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody 4 func) user)
    (bounds : Bounds func entry) : ModulePayloads :=
  { typeBytes := typePayload func, functionBytes := functionPayload
    memoryBytes := memoryPayload, globalBytes := globalPayload
    exportBytes := exportPayload entry, codeBytes := codePayload func
    types := typeValues func, functions := functionValues, memories := memoryValues
    globals := globalValues, exports := exportValues entry, codes := codeValues user
    typesParsed := types_parsed func bounds.params bounds.results
    functionsParsed := functions_parsed, memoriesParsed := memory_parsed
    globalsParsed := globals_parsed, exportsParsed := exports_parsed entry bounds.name
    codesParsed := codes_parsed func user parsed
    typeBound := bounds.types, functionBound := functions_bound
    memoryBound := memory_bound, globalBound := globals_bound
    exportBound := bounds.exports, codeBound := bounds.code }

theorem actual_bytes (func : LeanExe.IR.Func) (entry : String) (user : Code)
    (named : func.exportName = some entry)
    (parsed : Parses code (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody 4 func) user)
    (bounds : Bounds func entry) :
    LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] } =
      ByteArray.mk ([0, 97, 115, 109, 1, 0, 0, 0] ++ (payloads func entry user parsed bounds).bytes).toArray := by
  unfold LeanExe.Wasm.Binary.CoreWasm.moduleBytes LeanExe.Wasm.Binary.CoreWasm.legacyModuleBytes
  rw [type_section, function_section, memory_section, global_section, export_section func entry named,
    code_section]
  simp only [ModulePayloads.bytes, payloads, LeanExe.Wasm.Binary.ofNats,
    LeanExe.Wasm.Binary.byte, List.map_cons, List.map_nil, List.append_assoc]
  rfl

/-- The public decoder consumes the exact production module bytes. The user-body
parsing premise is supplied by the general original-source/body-bytes theorem. -/
theorem decode_actual_module (func : LeanExe.IR.Func) (entry : String) (user : Code)
    (named : func.exportName = some entry)
    (parsed : Parses code (LeanExe.Wasm.Binary.CoreWasm.emitFuncBody 4 func) user)
    (bounds : Bounds func entry) :
    Wasm.Binary.decode (LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] }) =
      .ok (rawModule func entry user) := by
  rw [actual_bytes func entry user named parsed bounds]
  exact (payloads func entry user parsed bounds).decode

end Project.Compiler.ArithmeticModule
