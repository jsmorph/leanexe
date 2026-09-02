import LeanExe.Wasm.Instr
import LeanExe.Wasm.Leb

/-!
# Canonical final module image

This is the byte boundary consumed by the self-hosted binary emitter.  It is
deliberately smaller than `LeanExe.IR.Module`: lowering and runtime selection
have already happened, and all references are resolved numeric indices.

Version 2 of the wire format is:

* ASCII magic `LXEIMG`, canonical unsigned-LEB schema version, and profile;
* memory minimum in pages;
* a vector of globals (`mutable`, initial i64 bit pattern);
* a vector of functions (i64 parameter/result/additional-local counts and a
  structured instruction vector);
* a vector of exports (ASCII name bytes, kind, resolved index).

Every vector and byte string has a canonical unsigned-LEB length.  Function
bodies are bounded byte strings containing linear instruction records with
explicit structured-control delimiters.  No Lean runtime object representation
crosses this boundary.
-/

namespace LeanExe.Wasm.Image

abbrev Instr := LeanExe.Wasm.Instr

inductive ExportKind where
  | func
  | memory
  | global
  deriving BEq, Repr, Inhabited

structure Global where
  mutable_ : Bool
  initial : UInt64
  deriving BEq, Inhabited

  /-- `locals` counts i64 locals in addition to the parameters.  `body` is one
  canonical linear instruction stream with explicit control delimiters. -/
structure Function where
  params : Nat
  results : Nat
  locals : Nat
  body : ByteArray
  deriving BEq, Inhabited

structure Export where
  name : ByteArray
  kind : ExportKind
  index : Nat
  deriving BEq, Inhabited

structure Module where
  memoryMinPages : Nat
  globals : Array Global
  functions : Array Function
  exports : Array Export
  deriving BEq, Inhabited

def magic : ByteArray :=
  "LXEIMG".toUTF8

def schemaVersion : UInt64 := 2

def libraryProfile : UInt64 := 1

def maxInputBytes : Nat := 64 * 1024 * 1024
def maxFunctions : Nat := 65536
def maxGlobals : Nat := 256
def maxExports : Nat := 65536
def maxParams : Nat := 65536
def maxResults : Nat := 65536
def maxLocals : Nat := 1048576
def maxFunctionBodyBytes : Nat := 32 * 1024 * 1024
def maxInstructionsPerList : Nat := 1048576
def maxNestingDepth : Nat := 256
def maxExportNameBytes : Nat := 4096

def errorTruncated : ByteArray :=
  "leanexe-image: truncated field".toUTF8

def errorInteger : ByteArray :=
  "leanexe-image: invalid integer".toUTF8

def errorNoncanonicalInteger : ByteArray :=
  "leanexe-image: noncanonical integer".toUTF8

def errorMagic : ByteArray :=
  "leanexe-image: invalid magic".toUTF8

def errorVersion : ByteArray :=
  "leanexe-image: unsupported version".toUTF8

def errorProfile : ByteArray :=
  "leanexe-image: unsupported profile".toUTF8

def errorLimit : ByteArray :=
  "leanexe-image: profile limit exceeded".toUTF8

def errorBoolean : ByteArray :=
  "leanexe-image: invalid boolean".toUTF8

def errorInstructionTag : ByteArray :=
  "leanexe-image: unknown instruction tag".toUTF8

def errorExportKind : ByteArray :=
  "leanexe-image: unknown export kind".toUTF8

def errorExportName : ByteArray :=
  "leanexe-image: non-ascii export name".toUTF8

def errorMemory : ByteArray :=
  "leanexe-image: invalid memory minimum".toUTF8

def errorDuplicateExport : ByteArray :=
  "leanexe-image: duplicate export name".toUTF8

def errorExportIndex : ByteArray :=
  "leanexe-image: invalid export index".toUTF8

def errorLocalIndex : ByteArray :=
  "leanexe-image: invalid local index".toUTF8

def errorGlobalIndex : ByteArray :=
  "leanexe-image: invalid global index".toUTF8

def errorImmutableGlobal : ByteArray :=
  "leanexe-image: write to immutable global".toUTF8

def errorFunctionIndex : ByteArray :=
  "leanexe-image: invalid function index".toUTF8

def errorBranchDepth : ByteArray :=
  "leanexe-image: invalid branch depth".toUTF8

def errorInstructionTrailing : ByteArray :=
  "leanexe-image: trailing instruction bytes".toUTF8

def errorInstructionNesting : ByteArray :=
  "leanexe-image: invalid instruction nesting".toUTF8

def errorTrailing : ByteArray :=
  "leanexe-image: trailing bytes".toUTF8

structure Cursor where
  input : ByteArray
  offset : Nat

def readByte (cursor : Cursor) : Except ByteArray (UInt8 × Cursor) :=
  if cursor.offset < cursor.input.size then
    Except.ok (cursor.input[cursor.offset]!, { cursor with offset := cursor.offset + 1 })
  else
    Except.error errorTruncated

def readU64Fuel : Nat → UInt64 → UInt64 → Cursor →
    Except ByteArray (UInt64 × Cursor)
  | 0, _, _, _ => Except.error errorInteger
  | fuel + 1, factor, acc, cursor => do
      let (byte, next) ← readByte cursor
      let payload := byte.toUInt64 &&& 127
      if factor == 9223372036854775808 && payload > 1 then
        Except.error errorInteger
      else
        let value := acc + payload * factor
        if byte.toUInt64 < 128 then
          if factor != 1 && payload == 0 then
            Except.error errorNoncanonicalInteger
          else
            Except.ok (value, next)
        else
          readU64Fuel fuel (factor * 128) value next

def readU64 (cursor : Cursor) : Except ByteArray (UInt64 × Cursor) :=
  readU64Fuel 10 1 0 cursor

def readNat (cursor : Cursor) : Except ByteArray (Nat × Cursor) := do
  let (value, next) ← readU64 cursor
  Except.ok (value.toNat, next)

def readBool (cursor : Cursor) : Except ByteArray (Bool × Cursor) := do
  let (value, next) ← readU64 cursor
  if value == 0 then
    Except.ok (false, next)
  else if value == 1 then
    Except.ok (true, next)
  else
    Except.error errorBoolean

def readBytes (limit : Nat) (cursor : Cursor) :
    Except ByteArray (ByteArray × Cursor) := do
  let (size, next) ← readNat cursor
  if size > limit then
    Except.error errorLimit
  else if next.offset + size > next.input.size then
    Except.error errorTruncated
  else
    Except.ok
      (next.input.extract next.offset (next.offset + size),
        { next with offset := next.offset + size })

def readFixedBytes (size : Nat) (cursor : Cursor) :
    Except ByteArray (ByteArray × Cursor) :=
  if cursor.offset + size > cursor.input.size then
    Except.error errorTruncated
  else
    Except.ok
      (cursor.input.extract cursor.offset (cursor.offset + size),
        { cursor with offset := cursor.offset + size })

def encodeU64 (value : UInt64) : ByteArray :=
  LeanExe.Wasm.Leb.u32lebU64 value

def encodeNat (value : Nat) : ByteArray :=
  encodeU64 (UInt64.ofNat value)

def encodeBool (value : Bool) : ByteArray :=
  encodeU64 (if value then 1 else 0)

def encodeBytes (value : ByteArray) : ByteArray :=
  encodeNat value.size ++ value

mutual
  def encodeInstr : Instr → ByteArray
    | .constI64 value => encodeNat 0 ++ encodeNat value
    | .constI32 value => encodeNat 1 ++ encodeNat value
    | .constI32NegOne => encodeNat 2
    | .localGet index => encodeNat 3 ++ encodeNat index
    | .localSet index => encodeNat 4 ++ encodeNat index
    | .localTee index => encodeNat 5 ++ encodeNat index
    | .globalGet index => encodeNat 6 ++ encodeNat index
    | .globalSet index => encodeNat 7 ++ encodeNat index
    | .call index => encodeNat 8 ++ encodeNat index
    | .addI64 => encodeNat 9
    | .subI64 => encodeNat 10
    | .mulI64 => encodeNat 11
    | .divUI64 => encodeNat 12
    | .remUI64 => encodeNat 13
    | .andI64 => encodeNat 14
    | .orI64 => encodeNat 15
    | .xorI64 => encodeNat 16
    | .shlI64 => encodeNat 17
    | .shrUI64 => encodeNat 18
    | .eqI64 => encodeNat 19
    | .neI64 => encodeNat 20
    | .ltUI64 => encodeNat 21
    | .leUI64 => encodeNat 22
    | .geUI64 => encodeNat 23
    | .eqzI64 => encodeNat 24
    | .eqI32 => encodeNat 25
    | .eqzI32 => encodeNat 26
    | .andI32 => encodeNat 27
    | .wrapI64 => encodeNat 28
    | .extendUI32 => encodeNat 29
    | .load64 => encodeNat 30
    | .load32 => encodeNat 31
    | .load8U => encodeNat 32
    | .store64 => encodeNat 33
    | .store32 => encodeNat 34
    | .store8 => encodeNat 35
    | .memorySize => encodeNat 36
    | .memoryGrow => encodeNat 37
    | .unreachable => encodeNat 38
    | .ret => encodeNat 39
    | .drop => encodeNat 40
    | .block body => encodeNat 41 ++ encodeInstrItems body ++ encodeNat 48
    | .loop body => encodeNat 42 ++ encodeInstrItems body ++ encodeNat 48
    | .iff resultI64 thn els =>
        encodeNat 43 ++ encodeBool resultI64 ++ encodeInstrItems thn ++
          (match els with
           | some body => encodeNat 47 ++ encodeInstrItems body
           | none => ByteArray.empty) ++
          encodeNat 48
    | .iffI32 thn els =>
        encodeNat 44 ++ encodeInstrItems thn ++
          (match els with
           | some body => encodeNat 47 ++ encodeInstrItems body
           | none => ByteArray.empty) ++
          encodeNat 48
    | .br depth => encodeNat 45 ++ encodeNat depth
    | .brIf depth => encodeNat 46 ++ encodeNat depth

  def encodeInstrItems : List Instr → ByteArray
    | [] => ByteArray.empty
    | instr :: rest => encodeInstr instr ++ encodeInstrItems rest

end

def encodeInstrList (body : List Instr) : ByteArray :=
  encodeInstrItems body


def encodeGlobal (global : Global) : ByteArray :=
  encodeBool global.mutable_ ++ encodeU64 global.initial

def encodeGlobals (globals : Array Global) : ByteArray :=
  globals.foldl (fun out global => out ++ encodeGlobal global) (encodeNat globals.size)

def decodeGlobals : Nat → Cursor → Array Global →
    Except ByteArray (Array Global × Cursor)
  | 0, cursor, globals => Except.ok (globals, cursor)
  | count + 1, cursor, globals => do
      let (mutable_, afterMutable) ← readBool cursor
      let (initial, next) ← readU64 afterMutable
      decodeGlobals count next (globals.push { mutable_, initial })

def encodeFunction (func : Function) : ByteArray :=
  encodeNat func.params ++ encodeNat func.results ++ encodeNat func.locals ++
    encodeBytes func.body

def encodeFunctions (functions : Array Function) : ByteArray :=
  functions.foldl (fun out func => out ++ encodeFunction func) (encodeNat functions.size)

def decodeFunction (cursor : Cursor) :
    Except ByteArray (Function × Cursor) := do
  let (params, afterParams) ← readNat cursor
  let (results, afterResults) ← readNat afterParams
  let (locals, afterLocals) ← readNat afterResults
  if params > maxParams || results > maxResults || locals > maxLocals then
    Except.error errorLimit
  else
    let (body, next) ← readBytes maxFunctionBodyBytes afterLocals
    Except.ok ({ params, results, locals, body }, next)

def decodeFunctions : Nat → Cursor → Array Function →
    Except ByteArray (Array Function × Cursor)
  | 0, cursor, functions => Except.ok (functions, cursor)
  | count + 1, cursor, functions => do
      let (func, next) ← decodeFunction cursor
      decodeFunctions count next (functions.push func)

def exportKindTag : ExportKind → UInt64
  | .func => 0
  | .memory => 1
  | .global => 2

def encodeExport (export_ : Export) : ByteArray :=
  encodeBytes export_.name ++ encodeU64 (exportKindTag export_.kind) ++ encodeNat export_.index

def encodeExports (exports : Array Export) : ByteArray :=
  exports.foldl (fun out export_ => out ++ encodeExport export_) (encodeNat exports.size)

def isAscii (bytes : ByteArray) : Bool :=
  bytes.foldl (fun valid byte => valid && byte.toNat < 128) true

def decodeExportKind (cursor : Cursor) : Except ByteArray (ExportKind × Cursor) := do
  let (tag, next) ← readU64 cursor
  if tag == 0 then
    Except.ok (.func, next)
  else if tag == 1 then
    Except.ok (.memory, next)
  else if tag == 2 then
    Except.ok (.global, next)
  else
    Except.error errorExportKind

def decodeExports : Nat → Cursor → Array Export →
    Except ByteArray (Array Export × Cursor)
  | 0, cursor, exports => Except.ok (exports, cursor)
  | count + 1, cursor, exports => do
      let (name, afterName) ← readBytes maxExportNameBytes cursor
      if !isAscii name then
        Except.error errorExportName
      else
        let (kind, afterKind) ← decodeExportKind afterName
        let (index, next) ← readNat afterKind
        decodeExports count next (exports.push { name, kind, index })

def containsExportNameFuel : Nat → ByteArray → Array Export → Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, name, exports, index =>
      if index >= exports.size then
        false
      else
        let export_ := exports[index]!
        export_.name == name || containsExportNameFuel fuel name exports (index + 1)

def hasDuplicateExportNameFuel : Nat → Array Export → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, exports, index =>
      if index >= exports.size then
        false
      else
        let export_ := exports[index]!
        containsExportNameFuel (exports.size - index - 1) export_.name exports (index + 1) ||
          hasDuplicateExportNameFuel fuel exports (index + 1)

def hasDuplicateExportName (exports : Array Export) : Bool :=
  hasDuplicateExportNameFuel exports.size exports 0

def validExportIndex (functionCount globalCount : Nat) (export_ : Export) : Bool :=
  match export_.kind with
  | .func => export_.index < functionCount
  | .memory => export_.index == 0
  | .global => export_.index < globalCount

def validateExportsFuel : Nat → Nat → Nat → Array Export → Nat → Except ByteArray Unit
  | 0, _, _, exports, index =>
      if index >= exports.size then Except.ok () else Except.error errorLimit
  | fuel + 1, functionCount, globalCount, exports, index => do
      if index >= exports.size then
        Except.ok ()
      else
        let export_ := exports[index]!
        if export_.name.size > maxExportNameBytes then
          Except.error errorLimit
        else if !isAscii export_.name then
          Except.error errorExportName
        else if !validExportIndex functionCount globalCount export_ then
          Except.error errorExportIndex
        else
          validateExportsFuel fuel functionCount globalCount exports (index + 1)

def validateExports (functionCount globalCount : Nat) (exports : Array Export) :
    Except ByteArray Unit :=
  validateExportsFuel exports.size functionCount globalCount exports 0

structure InstrCursorState where
  offset : Nat
  stack : Array UInt64

def validateInstrStep (functionCount : Nat) (globals : Array Global)
    (localCount : Nat) (input : ByteArray) (offset : Nat) (stack : Array UInt64) :
    Except ByteArray InstrCursorState := do
  let cursor : Cursor := { input, offset }
  let (tag, next) ← readNat cursor
  if tag <= 1 then
    let (_, rest) ← readNat next
    Except.ok { offset := rest.offset, stack }
  else if tag == 2 then
    Except.ok { offset := next.offset, stack }
  else if tag >= 3 && tag <= 5 then
    let (index, rest) ← readNat next
    if index < localCount then
      Except.ok { offset := rest.offset, stack }
    else
      Except.error errorLocalIndex
  else if tag == 6 then
    let (index, rest) ← readNat next
    if index < globals.size then
      Except.ok { offset := rest.offset, stack }
    else
      Except.error errorGlobalIndex
  else if tag == 7 then
    let (index, rest) ← readNat next
    if index >= globals.size then
      Except.error errorGlobalIndex
    else if globals[index]!.mutable_ then
      Except.ok { offset := rest.offset, stack }
    else
      Except.error errorImmutableGlobal
  else if tag == 8 then
    let (index, rest) ← readNat next
    if index < functionCount then
      Except.ok { offset := rest.offset, stack }
    else
      Except.error errorFunctionIndex
  else if tag >= 9 && tag <= 40 then
    Except.ok { offset := next.offset, stack }
  else if tag == 41 || tag == 42 then
    if stack.size >= maxNestingDepth then
      Except.error errorLimit
    else
      Except.ok { offset := next.offset, stack := stack.push 0 }
  else if tag == 43 then
    let (_, rest) ← readBool next
    if stack.size >= maxNestingDepth then
      Except.error errorLimit
    else
      Except.ok { offset := rest.offset, stack := stack.push 1 }
  else if tag == 44 then
    if stack.size >= maxNestingDepth then
      Except.error errorLimit
    else
      Except.ok { offset := next.offset, stack := stack.push 1 }
  else if tag == 45 || tag == 46 then
    let (branchDepth, rest) ← readNat next
    if branchDepth < stack.size then
      Except.ok { offset := rest.offset, stack }
    else
      Except.error errorBranchDepth
  else if tag == 47 then
    if stack.size == 0 || stack[stack.size - 1]! != 1 then
      Except.error errorInstructionNesting
    else
      Except.ok { offset := next.offset, stack := stack.set! (stack.size - 1) 2 }
  else if tag == 48 then
    if stack.size == 0 then
      Except.error errorInstructionNesting
    else
      Except.ok { offset := next.offset, stack := stack.pop }
  else
    Except.error errorInstructionTag

def validateInstrStream (functionCount : Nat) (globals : Array Global)
    (localCount : Nat) (input : ByteArray) : Except ByteArray Nat := Id.run do
  let mut offset := 0
  let mut stack : Array UInt64 := #[]
  let mut remaining := min input.size maxInstructionsPerList
  let mut running := true
  let mut result : Except ByteArray Nat := Except.error errorLimit
  while running do
    if offset == input.size then
      result := if stack.size == 0 then Except.ok offset
        else Except.error errorInstructionNesting
      running := false
    else if remaining == 0 then
      result := Except.error errorLimit
      running := false
    else
      match validateInstrStep functionCount globals localCount input offset stack with
      | Except.error error =>
          result := Except.error error
          running := false
      | Except.ok state =>
          offset := state.offset
          stack := state.stack
          remaining := remaining - 1
  return result

def validateFunctionBody (functionCount : Nat) (globals : Array Global)
    (func : Function) : Except ByteArray Unit := do
  if func.body.size > maxFunctionBodyBytes then
    Except.error errorLimit
  else
    let finalOffset ← validateInstrStream functionCount globals
      (func.params + func.locals) func.body
    if finalOffset == func.body.size then
      Except.ok ()
    else
      Except.error errorInstructionTrailing

def validateFunctionsFuel : Nat → Nat → Array Global → Array Function → Nat →
    Except ByteArray Unit
  | 0, _, _, functions, index =>
      if index >= functions.size then Except.ok () else Except.error errorLimit
  | fuel + 1, functionCount, globals, functions, index => do
      if index >= functions.size then
        Except.ok ()
      else
        let func := functions[index]!
        if func.params > maxParams || func.results > maxResults || func.locals > maxLocals then
          Except.error errorLimit
        else
          validateFunctionBody functionCount globals func
          validateFunctionsFuel fuel functionCount globals functions (index + 1)

def validateFunctions (functionCount : Nat) (globals : Array Global)
    (functions : Array Function) : Except ByteArray Unit :=
  validateFunctionsFuel functions.size functionCount globals functions 0

def validateModule (module_ : Module) : Except ByteArray Unit := do
  if module_.memoryMinPages == 0 || module_.memoryMinPages > 65536 then
    Except.error errorMemory
  else if module_.globals.size > maxGlobals || module_.functions.size > maxFunctions ||
      module_.exports.size > maxExports then
    Except.error errorLimit
  else if hasDuplicateExportName module_.exports then
    Except.error errorDuplicateExport
  else
    validateFunctions module_.functions.size module_.globals module_.functions
    validateExports module_.functions.size module_.globals.size module_.exports

def encodeModule (module_ : Module) : ByteArray :=
  magic ++ encodeU64 schemaVersion ++ encodeU64 libraryProfile ++
    encodeNat module_.memoryMinPages ++ encodeGlobals module_.globals ++
    encodeFunctions module_.functions ++ encodeExports module_.exports

def decodeModule (input : ByteArray) : Except ByteArray Module := do
  if input.size > maxInputBytes then
    Except.error errorLimit
  else
    let start : Cursor := { input, offset := 0 }
    let (actualMagic, afterMagic) ← readFixedBytes magic.size start
    if actualMagic != magic then
      Except.error errorMagic
    else
      let (version, afterVersion) ← readU64 afterMagic
      if version != schemaVersion then
        Except.error errorVersion
      else
        let (profile, afterProfile) ← readU64 afterVersion
        if profile != libraryProfile then
          Except.error errorProfile
        else
          let (memoryMinPages, afterMemory) ← readNat afterProfile
          let (globalCount, afterGlobalCount) ← readNat afterMemory
          if globalCount > maxGlobals then
            Except.error errorLimit
          else
            let (globals, afterGlobals) ← decodeGlobals globalCount afterGlobalCount #[]
            let (functionCount, afterFunctionCount) ← readNat afterGlobals
            if functionCount > maxFunctions then
              Except.error errorLimit
            else
              let (functions, afterFunctions) ←
                decodeFunctions functionCount afterFunctionCount #[]
              let (exportCount, afterExportCount) ← readNat afterFunctions
              if exportCount > maxExports then
                Except.error errorLimit
              else
                let (exports, finalCursor) ← decodeExports exportCount afterExportCount #[]
                if finalCursor.offset != input.size then
                  Except.error errorTrailing
                else
                  let module_ : Module := { memoryMinPages, globals, functions, exports }
                  validateModule module_
                  Except.ok module_

end LeanExe.Wasm.Image
