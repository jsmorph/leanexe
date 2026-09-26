import LeanExe.Wasm.Binary

namespace LeanExe.Wasm.ArithmeticBounds

def typeItems (func : LeanExe.IR.Func) : List (List UInt8) :=
  [LeanExe.Wasm.Binary.CoreWasm.typeForFunc func,
   LeanExe.Wasm.Binary.funcType [126] [126], LeanExe.Wasm.Binary.funcType [] [],
   LeanExe.Wasm.Binary.funcType [126] [126], LeanExe.Wasm.Binary.funcType [126] []]
def typePayload (func : LeanExe.IR.Func) : List UInt8 := LeanExe.Wasm.Binary.vec (typeItems func)

def exportItems (entry : String) : List (List UInt8) :=
  [LeanExe.Wasm.Binary.exportEntry "memory" 2 0,
   LeanExe.Wasm.Binary.exportEntry entry 0 0,
   LeanExe.Wasm.Binary.exportEntry "alloc" 0 1,
   LeanExe.Wasm.Binary.exportEntry "reset" 0 2,
   LeanExe.Wasm.Binary.exportEntry "retain" 0 3,
   LeanExe.Wasm.Binary.exportEntry "release" 0 4,
   LeanExe.Wasm.Binary.exportEntry "free" 0 4,
   LeanExe.Wasm.Binary.exportEntry "allocCount" 3 2,
   LeanExe.Wasm.Binary.exportEntry "retainCount" 3 3,
   LeanExe.Wasm.Binary.exportEntry "releaseCount" 3 4,
   LeanExe.Wasm.Binary.exportEntry "freeCount" 3 5]
def exportPayload (entry : String) : List UInt8 := LeanExe.Wasm.Binary.vec (exportItems entry)

def codeItems (func : LeanExe.IR.Func) : List (List UInt8) :=
  [LeanExe.Wasm.Binary.CoreWasm.emitFuncBody 4 func,
   LeanExe.Wasm.Binary.CoreWasm.coreAllocBody, LeanExe.Wasm.Binary.CoreWasm.coreResetBody,
   LeanExe.Wasm.Binary.CoreWasm.coreRetainBody, LeanExe.Wasm.Binary.CoreWasm.coreReleaseBody 4]
def codePayload (func : LeanExe.IR.Func) : List UInt8 := LeanExe.Wasm.Binary.vec (codeItems func)

/-- Numeric WebAssembly format limits for the actual arithmetic module layout.
These are size checks, not semantic or validator-success assumptions. -/
def Fits (func : LeanExe.IR.Func) (entry : String) : Prop :=
  func.params < 2 ^ 32 ∧
  func.results.length < 2 ^ 32 ∧
  entry.toUTF8.size < 2 ^ 32 ∧
  func.locals + Binary.CoreWasm.funcScratch func < 2 ^ 32 ∧
  (Binary.CoreWasm.localDecls func ++ Binary.CoreWasm.encodeInstrs
    (Binary.CoreWasm.emitFuncInstrs 4 func) ++ [11]).length < 2 ^ 32 ∧
  (typePayload func).length < 2 ^ 32 ∧
  (exportPayload entry).length < 2 ^ 32 ∧
  (codePayload func).length < 2 ^ 32

instance (func : LeanExe.IR.Func) (entry : String) : Decidable (Fits func entry) := by
  unfold Fits
  infer_instance

end LeanExe.Wasm.ArithmeticBounds
