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
  ByteArray.empty.push (UInt8.ofNat value)

def bytes2 (first second : Nat) : ByteArray :=
  (byte first).push (UInt8.ofNat second)

def bytes3 (first second third : Nat) : ByteArray :=
  (bytes2 first second).push (UInt8.ofNat third)

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
    | .addF64 => byte 160
    | .mulF64 => byte 162
    | .i64ReinterpretF64 => byte 189
    | .f64ReinterpretI64 => byte 191
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

def indexedOpcode (tag : Nat) : Nat :=
  if tag == 3 then 32
  else if tag == 4 then 33
  else if tag == 5 then 34
  else if tag == 6 then 35
  else if tag == 7 then 36
  else 16

def scalarOpcode (tag : Nat) : Nat :=
  if tag == 9 then 124
  else if tag == 10 then 125
  else if tag == 11 then 126
  else if tag == 12 then 128
  else if tag == 13 then 130
  else if tag == 14 then 131
  else if tag == 15 then 132
  else if tag == 16 then 133
  else if tag == 17 then 134
  else if tag == 18 then 136
  else if tag == 19 then 81
  else if tag == 20 then 82
  else if tag == 21 then 84
  else if tag == 22 then 88
  else if tag == 23 then 90
  else if tag == 24 then 80
  else if tag == 25 then 70
  else if tag == 26 then 69
  else if tag == 27 then 113
  else if tag == 28 then 167
  else 173

def simpleInstructionBytes (tag : Nat) : ByteArray :=
  if tag <= 29 then
    byte (scalarOpcode tag)
  else if tag == 30 then bytes3 41 3 0
  else if tag == 31 then bytes3 40 2 0
  else if tag == 32 then bytes3 45 0 0
  else if tag == 33 then bytes3 55 3 0
  else if tag == 34 then bytes3 54 2 0
  else if tag == 35 then bytes3 58 0 0
  else if tag == 36 then bytes2 63 0
  else if tag == 37 then bytes2 64 0
  else if tag == 38 then byte 0
  else if tag == 39 then byte 15
  else byte 26

structure EmitCursorState where
  offset : Nat
  stack : Array UInt64
  output : ByteArray
  chunk : ByteArray

def instructionChunkBytes : Nat := 512

def appendInstructionBytes (offset : Nat) (stack : Array UInt64)
    (output chunk bytes : ByteArray) : EmitCursorState :=
  if chunk.size + bytes.size > instructionChunkBytes then
    EmitCursorState.mk offset stack (output ++ chunk) bytes
  else
    EmitCursorState.mk offset stack output (chunk ++ bytes)

def emitInstrStep (input : ByteArray) (offset : Nat) (stack : Array UInt64)
    (output chunk : ByteArray) : Except ByteArray EmitCursorState := do
  let cursor : Cursor := { input, offset }
  let (tag, next) ← readNat cursor
  if tag == 0 then
    let (value, rest) ← readNat next
    Except.ok (appendInstructionBytes rest.offset stack output chunk
      (byte 66 ++ LeanExe.Wasm.Leb.s64lebU64 (UInt64.ofNat value)))
  else if tag == 1 then
    let (value, rest) ← readNat next
    Except.ok (appendInstructionBytes rest.offset stack output chunk
      (byte 65 ++ encodeNat value))
  else if tag == 2 then
    Except.ok (appendInstructionBytes next.offset stack output chunk (bytes2 65 127))
  else if tag >= 3 && tag <= 8 then
    let (index, rest) ← readNat next
    let opcode := indexedOpcode tag
    Except.ok (appendInstructionBytes rest.offset stack output chunk
      (byte opcode ++ encodeNat index))
  else if tag >= 9 && tag <= 40 then
    let instructionBytes := simpleInstructionBytes tag
    Except.ok (appendInstructionBytes next.offset stack output chunk instructionBytes)
  else if tag == 41 then
    if stack.size >= maxNestingDepth then
      Except.error errorLimit
    else
      Except.ok (appendInstructionBytes next.offset (stack.push 0) output chunk (bytes2 2 64))
  else if tag == 42 then
    if stack.size >= maxNestingDepth then
      Except.error errorLimit
    else
      Except.ok (appendInstructionBytes next.offset (stack.push 0) output chunk (bytes2 3 64))
  else if tag == 43 then
    let (resultI64, rest) ← readBool next
    if stack.size >= maxNestingDepth then
      Except.error errorLimit
    else
      Except.ok (appendInstructionBytes rest.offset (stack.push 1) output chunk
        (bytes2 4 (if resultI64 then 126 else 64)))
  else if tag == 44 then
    if stack.size >= maxNestingDepth then
      Except.error errorLimit
    else
      Except.ok (appendInstructionBytes next.offset (stack.push 1) output chunk (bytes2 4 127))
  else if tag == 45 then
    let (branchDepth, rest) ← readNat next
    Except.ok (appendInstructionBytes rest.offset stack output chunk
      (byte 12 ++ encodeNat branchDepth))
  else if tag == 46 then
    let (branchDepth, rest) ← readNat next
    Except.ok (appendInstructionBytes rest.offset stack output chunk
      (byte 13 ++ encodeNat branchDepth))
  else if tag == 47 then
    if stack.size == 0 || stack[stack.size - 1]! != 1 then
      Except.error errorInstructionNesting
    else
      Except.ok (appendInstructionBytes next.offset (stack.set! (stack.size - 1) 2)
        output chunk (byte 5))
  else if tag == 48 then
    if stack.size == 0 then
      Except.error errorInstructionNesting
    else
      Except.ok (appendInstructionBytes next.offset stack.pop output chunk (byte 11))
  else
    Except.error errorInstructionTag

def emitInstrStream (input : ByteArray) : Except ByteArray (Nat × ByteArray) := Id.run do
  let mut offset := 0
  let mut stack : Array UInt64 := #[]
  let mut output := ByteArray.empty
  let mut chunk := ByteArray.empty
  let mut remaining := min input.size maxInstructionsPerList
  let mut running := true
  let mut result : Except ByteArray (Nat × ByteArray) := Except.error errorLimit
  while running do
    if offset == input.size then
      result := if stack.size == 0 then Except.ok (offset, output ++ chunk)
        else Except.error errorInstructionNesting
      running := false
    else if remaining == 0 then
      result := Except.error errorLimit
      running := false
    else
      match emitInstrStep input offset stack output chunk with
      | Except.error error =>
          result := Except.error error
          running := false
      | Except.ok state =>
          offset := state.offset
          stack := state.stack
          output := state.output
          chunk := state.chunk
          remaining := remaining - 1
  return result

def emitFunctionInstructions (func : Function) : Except ByteArray ByteArray := do
  let (finalOffset, output) ← emitInstrStream func.body
  if finalOffset == func.body.size then
    Except.ok output
  else
    Except.error errorInstructionTrailing

def localDeclarations (func : Function) : ByteArray :=
  if func.locals == 0 then
    byte 0
  else
    vectorPrefix 1 ++ encodeNat func.locals ++ byte 126

def functionBody (func : Function) : Except ByteArray ByteArray := do
  let instructions ← emitFunctionInstructions func
  let body := localDeclarations func ++ instructions ++ byte 11
  Except.ok (encodeNat body.size ++ body)

def appendFunctionBodiesFuel : Nat → Array Function → Nat → ByteArray →
    Except ByteArray ByteArray
  | 0, functions, index, output =>
      if index >= functions.size then Except.ok output else Except.error errorLimit
  | fuel + 1, functions, index, output => do
      if index >= functions.size then
        Except.ok output
      else
        let func := functions[index]!
        let emitted ← functionBody func
        let nextOutput := output ++ emitted
        appendFunctionBodiesFuel fuel functions (index + 1) nextOutput

def appendFunctionBodies (functions : Array Function) (output : ByteArray) :
    Except ByteArray ByteArray :=
  appendFunctionBodiesFuel functions.size functions 0 output

def codeSection (module_ : Module) : Except ByteArray ByteArray := do
  let payload ← appendFunctionBodies module_.functions
    (vectorPrefix module_.functions.size)
  Except.ok (sectionBytes 10 payload)

def emitModule (module_ : Module) : Except ByteArray ByteArray := do
  validateModule module_
  let code ← codeSection module_
  let output := wasmMagic ++ typeSection module_ ++ functionSection module_ ++
    memorySection module_ ++ globalSection module_ ++ exportSection module_ ++ code
  if output.size > maxOutputBytes then
    Except.error errorOutputLimit
  else
    Except.ok output

/-- Public self-hosted emitter entry. -/
def emitImage (input : ByteArray) : Except ByteArray ByteArray :=
  Except.casesOn (motive := fun _ => Except ByteArray ByteArray)
    (decodeModule input)
    (fun error => Except.error error)
    (fun module_ => emitModule module_)

end LeanExe.Wasm.Image
