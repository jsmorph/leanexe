import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Translate
import Interpreter.Wasm.Validate

/-! The exact, import-bearing Wasm bridge. This deliberately leaves the existing
import-free artifact decoder unchanged. Both decoding and the binary grammar
are checked here; runtime file identity is checked by the package driver. -/
namespace Project.WGSL.HostBinary

open Wasm.Binary

structure FunctionImport where
  moduleName : Name
  functionName : Name
  typeIndex : UInt32
  deriving Repr, DecidableEq, Inhabited

structure RawHost where
  base : RawModule
  imports : List FunctionImport

def RawHost.toTalos (raw : RawHost) : Wasm.Module :=
  { Translation.module raw.base with imports := raw.imports.map (fun entry =>
      let sig := raw.base.types[entry.typeIndex.toNat]!
      { «module» := entry.moduleName.text, name := entry.functionName.text,
        params := sig.params.map ValType.toTalos, results := sig.results.map ValType.toTalos }) }

def typePayload : List UInt8 := [1, 96, 3, 127, 127, 127, 1, 127]
def importPayload : List UInt8 :=
  [1, 14, 108, 101, 97, 110, 101, 120, 101, 46, 119, 101, 98, 103, 112, 117,
   8, 103, 101, 109, 109, 95, 102, 51, 50, 0, 0]
def functionPayload : List UInt8 := [1, 0]
def memoryPayload : List UInt8 := [1, 1, 1, 128, 2]
def exportPayload : List UInt8 := [2, 6, 109, 101, 109, 111, 114, 121, 2, 0, 3, 114, 117, 110, 0, 1]
def codePayload : List UInt8 := [1, 10, 0, 32, 0, 32, 1, 32, 2, 16, 0, 11]
def bytes : ByteArray :=
  ([0, 97, 115, 109, 1, 0, 0, 0, 1, 8] ++ typePayload ++ [2, 27] ++ importPayload ++
    [3, 2] ++ functionPayload ++ [5, 5] ++ memoryPayload ++
    [7, 16] ++ exportPayload ++ [10, 12] ++ codePayload).toByteArray

def raw : RawHost :=
  ⟨{ sections := [.type, .function, .memory, .export, .code],
     types := [⟨[.i32, .i32, .i32], [.i32]⟩], functionTypeIndices := [0],
     memories := [⟨⟨1, some 256⟩⟩], globals := [],
     exports := [⟨⟨[109, 101, 109, 111, 114, 121], "memory"⟩, .memory 0⟩,
       ⟨⟨[114, 117, 110], "run"⟩, .func 1⟩],
     codes := [⟨[], [.localGet 0, .localGet 1, .localGet 2, .call 0]⟩] },
   [⟨⟨[108, 101, 97, 110, 101, 120, 101, 46, 119, 101, 98, 103, 112, 117], "leanexe.webgpu"⟩,
     ⟨[103, 101, 109, 109, 95, 102, 51, 50], "gemm_f32"⟩, 0⟩]⟩

def module : Wasm.Module := raw.toTalos

/-- The additional WebAssembly grammar production: a function import consists
of two UTF-8 names, the function-kind byte, and a type index. -/
inductive ImportEncoding : List UInt8 → FunctionImport → Prop
  | function (moduleBytes nameBytes indexBytes : List UInt8) (entry : FunctionImport)
      (hm : Grammar.Name moduleBytes entry.moduleName)
      (hn : Grammar.Name nameBytes entry.functionName)
      (hi : Grammar.U32 indexBytes entry.typeIndex.toNat) :
      ImportEncoding (moduleBytes ++ nameBytes ++ [0] ++ indexBytes) entry

/-- Exact section encodings, including their explicit sizes and ordering. -/
structure Encodes : Prop where
  typeSection : Grammar.Sized (Grammar.Vector Grammar.FuncType) (8 :: typePayload) raw.base.types
  importSection : Grammar.Sized (Grammar.Vector ImportEncoding) (27 :: importPayload) raw.imports
  functionSection : Grammar.Sized (Grammar.Vector (fun b (i : UInt32) => Grammar.U32 b i.toNat))
    (2 :: functionPayload) raw.base.functionTypeIndices
  memorySection : Grammar.Sized (Grammar.Vector Grammar.MemoryType) (5 :: memoryPayload) raw.base.memories
  exportSection : Grammar.Sized (Grammar.Vector Grammar.Export) (16 :: exportPayload) raw.base.exports
  codeSection : Grammar.Sized (Grammar.Vector Grammar.Code) (12 :: codePayload) raw.base.codes

private theorem ok_of_option {E A} (result : Except E A) (value : A)
    (h : result.toOption = some value) : result = .ok value := by
  cases result with
  | error _ => cases h
  | ok actual => cases Option.some.inj h; rfl

private theorem typeEncoded : Grammar.Sized (Grammar.Vector Grammar.FuncType)
    (8 :: typePayload) raw.base.types :=
  Parser.runAll_sound (input := (8 :: typePayload).toByteArray)
    (Proof.sized_sound (Proof.vector_sound Proof.funcType_sound))
    (ok_of_option _ _ (by decide +kernel))

private theorem importEncoded : Grammar.Sized (Grammar.Vector ImportEncoding)
    (27 :: importPayload) raw.imports := by
  apply Grammar.Sized.intro [27] importPayload raw.imports (by
    simp [Grammar.U32, Grammar.continuationForm, Grammar.unsignedTerminalFits,
      Grammar.unsignedValue, importPayload])
  apply Grammar.Vector.intro [1] _ raw.imports (by
    simp [Grammar.U32, Grammar.continuationForm, Grammar.unsignedTerminalFits,
      Grammar.unsignedValue, raw])
  apply Grammar.Items.cons (importPayload.drop 1) [] raw.imports.head! [] ?_ .nil
  apply ImportEncoding.function
    [14, 108, 101, 97, 110, 101, 120, 101, 46, 119, 101, 98, 103, 112, 117]
    [8, 103, 101, 109, 109, 95, 102, 51, 50] [0]
  · exact Parser.runAll_sound (input := ([14, 108, 101, 97, 110, 101, 120, 101, 46, 119, 101, 98, 103, 112, 117] : List UInt8).toByteArray)
      Proof.name_sound (ok_of_option _ _ (by decide +kernel))
  · exact Parser.runAll_sound (input := ([8, 103, 101, 109, 109, 95, 102, 51, 50] : List UInt8).toByteArray)
      Proof.name_sound (ok_of_option _ _ (by decide +kernel))
  · simp [Grammar.U32, Grammar.continuationForm, Grammar.unsignedTerminalFits,
      Grammar.unsignedValue, raw]

private theorem functionEncoded : Grammar.Sized
    (Grammar.Vector (fun b (i : UInt32) => Grammar.U32 b i.toNat))
    (2 :: functionPayload) raw.base.functionTypeIndices :=
  Parser.runAll_sound (input := (2 :: functionPayload).toByteArray)
    (Proof.sized_sound (Proof.vector_sound Leb.Proof.u32_sound))
    (ok_of_option _ _ (by decide +kernel))

private theorem memoryEncoded : Grammar.Sized (Grammar.Vector Grammar.MemoryType)
    (5 :: memoryPayload) raw.base.memories :=
  Parser.runAll_sound (input := (5 :: memoryPayload).toByteArray)
    (Proof.sized_sound (Proof.vector_sound Proof.memoryType_sound))
    (ok_of_option _ _ (by decide +kernel))

private theorem exportEncoded : Grammar.Sized (Grammar.Vector Grammar.Export)
    (16 :: exportPayload) raw.base.exports :=
  Parser.runAll_sound (input := (16 :: exportPayload).toByteArray)
    (Proof.sized_sound (Proof.vector_sound Proof.exportEntry_sound))
    (ok_of_option _ _ (by decide +kernel))

private theorem codeEncoded : Grammar.Sized (Grammar.Vector Grammar.Code)
    (12 :: codePayload) raw.base.codes := by
  have u0 : Grammar.U32 [0] 0 := by
    simp [Grammar.U32, Grammar.continuationForm, Grammar.unsignedTerminalFits, Grammar.unsignedValue]
  have u1 : Grammar.U32 [1] 1 := by
    simp [Grammar.U32, Grammar.continuationForm, Grammar.unsignedTerminalFits, Grammar.unsignedValue]
  have u2 : Grammar.U32 [2] 2 := by
    simp [Grammar.U32, Grammar.continuationForm, Grammar.unsignedTerminalFits, Grammar.unsignedValue]
  apply Grammar.Sized.intro [12] codePayload raw.base.codes (by
    simp [Grammar.U32, Grammar.continuationForm, Grammar.unsignedTerminalFits, Grammar.unsignedValue, codePayload])
  apply Grammar.Vector.intro [1] (codePayload.drop 1) raw.base.codes u1
  apply Grammar.Items.cons (codePayload.drop 1) [] raw.base.codes.head! [] ?_ .nil
  apply Grammar.Sized.intro [10] [0, 32, 0, 32, 1, 32, 2, 16, 0, 11] _ (by
    simp [Grammar.U32, Grammar.continuationForm, Grammar.unsignedTerminalFits, Grammar.unsignedValue])
  apply Grammar.CodeBody.intro [0] [32, 0, 32, 1, 32, 2, 16, 0] [] _
    (Grammar.Vector.intro [0] [] [] u0 .nil)
  exact Grammar.Instrs.cons [32, 0] [32, 1, 32, 2, 16, 0] _ _ (.localGet [0] 0 u0)
    (Grammar.Instrs.cons [32, 1] [32, 2, 16, 0] _ _ (.localGet [1] 1 u1)
      (Grammar.Instrs.cons [32, 2] [16, 0] _ _ (.localGet [2] 2 u2)
        (Grammar.Instrs.cons [16, 0] [] _ [] (.call [0] 0 u0) .nil)))

theorem encoded : Encodes :=
  ⟨typeEncoded, importEncoded, functionEncoded, memoryEncoded, exportEncoded, codeEncoded⟩

theorem interface : module.checkInterface = .ok () :=
  ok_of_option _ _ (by decide +kernel)

#print axioms encoded
#print axioms interface

end Project.WGSL.HostBinary
