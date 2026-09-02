import LeanExe.Wasm.Image

/-!
# Final module-image emission

This module contains the pure byte emitter used by both the native compiler and
the self-hosted entry.  It accepts only the canonical library profile described
by `LeanExe.Wasm.Image.Module` and emits one complete WebAssembly module.
-/

namespace LeanExe.Wasm.Image

def wasmMagic : ByteArray :=
  ByteArray.mk #[0, 97, 115, 109, 1, 0, 0, 0]

def maxOutputBytes : Nat :=
  128 * 1024 * 1024

def errorOutputLimit : ByteArray :=
  "leanexe-image: output limit exceeded".toUTF8

def byte (value : Nat) : ByteArray :=
  ByteArray.empty.push value.toUInt8

def bytes2 (first second : Nat) : ByteArray :=
  (byte first).push second.toUInt8

def bytes3 (first second third : Nat) : ByteArray :=
  (bytes2 first second).push third.toUInt8

def vectorPrefix (count : Nat) : ByteArray :=
  LeanExe.Wasm.Leb.u32lebU64 (UInt64.ofNat count)

def sectionBytes (id : Nat) (payload : ByteArray) : ByteArray :=
  LeanExe.Wasm.Leb.sectionBytes (UInt64.ofNat id) payload

def appendRepeatedByte : Nat → UInt8 → ByteArray → ByteArray
  | 0, _, out => out
  | count + 1, value, out => appendRepeatedByte count value (out.push value)

def functionType (func : Function) : ByteArray :=
  let params := appendRepeatedByte func.params 126 (vectorPrefix func.params)
  let results := appendRepeatedByte func.results 126 (vectorPrefix func.results)
  byte 96 ++ params ++ results

def typeSection (module_ : Module) : ByteArray :=
  let payload := module_.functions.foldl
    (fun out func => out ++ functionType func)
    (vectorPrefix module_.functions.size)
  sectionBytes 1 payload

def appendTypeIndices : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | count + 1, index, out =>
      appendTypeIndices count (index + 1) (out ++ encodeNat index)

def functionSection (module_ : Module) : ByteArray :=
  sectionBytes 3 (appendTypeIndices module_.functions.size 0
    (vectorPrefix module_.functions.size))

def memorySection (module_ : Module) : ByteArray :=
  sectionBytes 5 (vectorPrefix 1 ++ byte 0 ++ encodeNat module_.memoryMinPages)

def globalEntry (global : Global) : ByteArray :=
  bytes2 126 (if global.mutable_ then 1 else 0) ++ byte 66 ++
    LeanExe.Wasm.Leb.s64lebU64 global.initial ++ byte 11

def globalSection (module_ : Module) : ByteArray :=
  let payload := module_.globals.foldl
    (fun out global => out ++ globalEntry global)
    (vectorPrefix module_.globals.size)
  sectionBytes 6 payload

def wasmExportKind : ExportKind → Nat
  | .func => 0
  | .memory => 2
  | .global => 3

def exportEntry (export_ : Export) : ByteArray :=
  encodeBytes export_.name ++ byte (wasmExportKind export_.kind) ++ encodeNat export_.index

def exportSection (module_ : Module) : ByteArray :=
  let payload := module_.exports.foldl
    (fun out export_ => out ++ exportEntry export_)
    (vectorPrefix module_.exports.size)
  sectionBytes 7 payload

mutual
  /-- The sole WASM opcode encoding for structured LeanExe instructions. -/
  def emitInstr : Instr → ByteArray
    | .constI64 value =>
        byte 66 ++ LeanExe.Wasm.Leb.s64lebU64 (UInt64.ofNat value)
    | .constI32 value => byte 65 ++ encodeNat value
    | .constI32NegOne => bytes2 65 127
    | .localGet index => byte 32 ++ encodeNat index
    | .localSet index => byte 33 ++ encodeNat index
    | .localTee index => byte 34 ++ encodeNat index
    | .globalGet index => byte 35 ++ encodeNat index
    | .globalSet index => byte 36 ++ encodeNat index
    | .call index => byte 16 ++ encodeNat index
    | .addI64 => byte 124
    | .subI64 => byte 125
    | .mulI64 => byte 126
    | .divUI64 => byte 128
    | .remUI64 => byte 130
    | .andI64 => byte 131
    | .orI64 => byte 132
    | .xorI64 => byte 133
    | .shlI64 => byte 134
    | .shrUI64 => byte 136
    | .eqI64 => byte 81
    | .neI64 => byte 82
    | .ltUI64 => byte 84
    | .leUI64 => byte 88
    | .geUI64 => byte 90
    | .eqzI64 => byte 80
    | .eqI32 => byte 70
    | .eqzI32 => byte 69
    | .andI32 => byte 113
    | .wrapI64 => byte 167
    | .extendUI32 => byte 173
    | .load64 => bytes3 41 3 0
    | .load32 => bytes3 40 2 0
    | .load8U => bytes3 45 0 0
    | .store64 => bytes3 55 3 0
    | .store32 => bytes3 54 2 0
    | .store8 => bytes3 58 0 0
    | .memorySize => bytes2 63 0
    | .memoryGrow => bytes2 64 0
    | .unreachable => byte 0
    | .ret => byte 15
    | .drop => byte 26
    | .block body => bytes2 2 64 ++ emitInstrs body ++ byte 11
    | .loop body => bytes2 3 64 ++ emitInstrs body ++ byte 11
    | .iff resultI64 thn els =>
        bytes2 4 (if resultI64 then 126 else 64) ++ emitInstrs thn ++
          (match els with
           | some body => byte 5 ++ emitInstrs body
           | none => ByteArray.empty) ++
          byte 11
    | .iffI32 thn els =>
        bytes2 4 127 ++ emitInstrs thn ++
          (match els with
           | some body => byte 5 ++ emitInstrs body
           | none => ByteArray.empty) ++
          byte 11
    | .br depth => byte 12 ++ encodeNat depth
    | .brIf depth => byte 13 ++ encodeNat depth

  def emitInstrs : List Instr → ByteArray
    | [] => ByteArray.empty
    | instr :: rest => emitInstr instr ++ emitInstrs rest
end

def localDeclarations (func : Function) : ByteArray :=
  if func.locals == 0 then
    byte 0
  else
    vectorPrefix 1 ++ encodeNat func.locals ++ byte 126

def functionBody (func : Function) : ByteArray :=
  let body := localDeclarations func ++ emitInstrs func.body ++ byte 11
  encodeNat body.size ++ body

def codeSection (module_ : Module) : ByteArray :=
  let payload := module_.functions.foldl
    (fun out func => out ++ functionBody func)
    (vectorPrefix module_.functions.size)
  sectionBytes 10 payload

def emitModuleUnchecked (module_ : Module) : ByteArray :=
  wasmMagic ++ typeSection module_ ++ functionSection module_ ++
    memorySection module_ ++ globalSection module_ ++ exportSection module_ ++
    codeSection module_

def emitModule (module_ : Module) : Except ByteArray ByteArray := do
  validateModule module_
  let output := emitModuleUnchecked module_
  if output.size > maxOutputBytes then
    Except.error errorOutputLimit
  else
    Except.ok output

/-- Public self-hosted emitter entry. -/
def emitImage (input : ByteArray) : Except ByteArray ByteArray := do
  let module_ ← decodeModule input
  emitModule module_

end LeanExe.Wasm.Image
