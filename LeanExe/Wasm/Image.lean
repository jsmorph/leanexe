import LeanExe.Wasm.Instr
import LeanExe.Wasm.Leb

/-!
# Canonical final module image

This is the byte boundary consumed by the self-hosted binary emitter.  It is
deliberately smaller than `LeanExe.IR.Module`: lowering and runtime selection
have already happened, and all references are resolved numeric indices.

Version 1 of the wire format is:

* ASCII magic `LXEIMG`, canonical unsigned-LEB schema version, and profile;
* memory minimum in pages;
* a vector of globals (`mutable`, initial i64 bit pattern);
* a vector of functions (i64 parameter/result/additional-local counts and a
  structured instruction vector);
* a vector of exports (ASCII name bytes, kind, resolved index).

Every vector and byte string has a canonical unsigned-LEB length.  Instruction
records have canonical unsigned-LEB tags and operands.  Nested instruction
vectors carry their own counts.  No Lean runtime object representation crosses
this boundary.
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

/-- `locals` counts i64 locals in addition to the parameters. -/
structure Function where
  params : Nat
  results : Nat
  locals : Nat
  body : List Instr
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

def schemaVersion : UInt64 := 1

def libraryProfile : UInt64 := 1

def maxInputBytes : Nat := 64 * 1024 * 1024
def maxFunctions : Nat := 65536
def maxGlobals : Nat := 256
def maxExports : Nat := 65536
def maxParams : Nat := 65536
def maxResults : Nat := 65536
def maxLocals : Nat := 1048576
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
    | .block body => encodeNat 41 ++ encodeInstrList body
    | .loop body => encodeNat 42 ++ encodeInstrList body
    | .iff resultI64 thn els =>
        encodeNat 43 ++ encodeBool resultI64 ++ encodeInstrList thn ++
          (match els with
           | some body => encodeBool true ++ encodeInstrList body
           | none => encodeBool false)
    | .iffI32 thn els =>
        encodeNat 44 ++ encodeInstrList thn ++
          (match els with
           | some body => encodeBool true ++ encodeInstrList body
           | none => encodeBool false)
    | .br depth => encodeNat 45 ++ encodeNat depth
    | .brIf depth => encodeNat 46 ++ encodeNat depth

  def encodeInstrItems : List Instr → ByteArray
    | [] => ByteArray.empty
    | instr :: rest => encodeInstr instr ++ encodeInstrItems rest

  def encodeInstrList (body : List Instr) : ByteArray :=
    encodeNat body.length ++ encodeInstrItems body
end

mutual
  def decodeInstr : Nat → Nat → Cursor → Except ByteArray (Instr × Cursor)
    | 0, _, _ => Except.error errorLimit
    | fuel + 1, depth, cursor => do
        if depth > maxNestingDepth then
          Except.error errorLimit
        else
          let (tag, next) ← readNat cursor
          match tag with
          | 0 =>
              let (value, rest) ← readNat next
              Except.ok (.constI64 value, rest)
          | 1 =>
              let (value, rest) ← readNat next
              Except.ok (.constI32 value, rest)
          | 2 => Except.ok (.constI32NegOne, next)
          | 3 =>
              let (index, rest) ← readNat next
              Except.ok (.localGet index, rest)
          | 4 =>
              let (index, rest) ← readNat next
              Except.ok (.localSet index, rest)
          | 5 =>
              let (index, rest) ← readNat next
              Except.ok (.localTee index, rest)
          | 6 =>
              let (index, rest) ← readNat next
              Except.ok (.globalGet index, rest)
          | 7 =>
              let (index, rest) ← readNat next
              Except.ok (.globalSet index, rest)
          | 8 =>
              let (index, rest) ← readNat next
              Except.ok (.call index, rest)
          | 9 => Except.ok (.addI64, next)
          | 10 => Except.ok (.subI64, next)
          | 11 => Except.ok (.mulI64, next)
          | 12 => Except.ok (.divUI64, next)
          | 13 => Except.ok (.remUI64, next)
          | 14 => Except.ok (.andI64, next)
          | 15 => Except.ok (.orI64, next)
          | 16 => Except.ok (.xorI64, next)
          | 17 => Except.ok (.shlI64, next)
          | 18 => Except.ok (.shrUI64, next)
          | 19 => Except.ok (.eqI64, next)
          | 20 => Except.ok (.neI64, next)
          | 21 => Except.ok (.ltUI64, next)
          | 22 => Except.ok (.leUI64, next)
          | 23 => Except.ok (.geUI64, next)
          | 24 => Except.ok (.eqzI64, next)
          | 25 => Except.ok (.eqI32, next)
          | 26 => Except.ok (.eqzI32, next)
          | 27 => Except.ok (.andI32, next)
          | 28 => Except.ok (.wrapI64, next)
          | 29 => Except.ok (.extendUI32, next)
          | 30 => Except.ok (.load64, next)
          | 31 => Except.ok (.load32, next)
          | 32 => Except.ok (.load8U, next)
          | 33 => Except.ok (.store64, next)
          | 34 => Except.ok (.store32, next)
          | 35 => Except.ok (.store8, next)
          | 36 => Except.ok (.memorySize, next)
          | 37 => Except.ok (.memoryGrow, next)
          | 38 => Except.ok (.unreachable, next)
          | 39 => Except.ok (.ret, next)
          | 40 => Except.ok (.drop, next)
          | 41 =>
              let (body, rest) ← decodeInstrList fuel (depth + 1) next
              Except.ok (.block body, rest)
          | 42 =>
              let (body, rest) ← decodeInstrList fuel (depth + 1) next
              Except.ok (.loop body, rest)
          | 43 =>
              let (resultI64, afterResult) ← readBool next
              let (thn, afterThen) ← decodeInstrList fuel (depth + 1) afterResult
              let (hasElse, afterFlag) ← readBool afterThen
              if hasElse then
                let (els, rest) ← decodeInstrList fuel (depth + 1) afterFlag
                Except.ok (.iff resultI64 thn (some els), rest)
              else
                Except.ok (.iff resultI64 thn none, afterFlag)
          | 44 =>
              let (thn, afterThen) ← decodeInstrList fuel (depth + 1) next
              let (hasElse, afterFlag) ← readBool afterThen
              if hasElse then
                let (els, rest) ← decodeInstrList fuel (depth + 1) afterFlag
                Except.ok (.iffI32 thn (some els), rest)
              else
                Except.ok (.iffI32 thn none, afterFlag)
          | 45 =>
              let (depth, rest) ← readNat next
              Except.ok (.br depth, rest)
          | 46 =>
              let (depth, rest) ← readNat next
              Except.ok (.brIf depth, rest)
          | _ => Except.error errorInstructionTag

  def decodeInstrItems : Nat → Nat → Nat → Cursor → List Instr →
      Except ByteArray (List Instr × Cursor)
    | 0, _, _, _, _ => Except.error errorLimit
    | _ + 1, _, 0, cursor, reversed => Except.ok (reversed.reverse, cursor)
    | fuel + 1, depth, count + 1, cursor, reversed => do
        let (instr, next) ← decodeInstr fuel depth cursor
        decodeInstrItems fuel depth count next (instr :: reversed)

  def decodeInstrList : Nat → Nat → Cursor → Except ByteArray (List Instr × Cursor)
    | 0, _, _ => Except.error errorLimit
    | fuel + 1, depth, cursor => do
        let (count, next) ← readNat cursor
        if count > maxInstructionsPerList then
          Except.error errorLimit
        else
          decodeInstrItems fuel depth count next []
end

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
    encodeInstrList func.body

def encodeFunctions (functions : Array Function) : ByteArray :=
  functions.foldl (fun out func => out ++ encodeFunction func) (encodeNat functions.size)

def decodeFunction (fuel : Nat) (cursor : Cursor) :
    Except ByteArray (Function × Cursor) := do
  let (params, afterParams) ← readNat cursor
  let (results, afterResults) ← readNat afterParams
  let (locals, afterLocals) ← readNat afterResults
  if params > maxParams || results > maxResults || locals > maxLocals then
    Except.error errorLimit
  else
    let (body, next) ← decodeInstrList fuel 0 afterLocals
    Except.ok ({ params, results, locals, body }, next)

def decodeFunctions (fuel : Nat) : Nat → Cursor → Array Function →
    Except ByteArray (Array Function × Cursor)
  | 0, cursor, functions => Except.ok (functions, cursor)
  | count + 1, cursor, functions => do
      let (func, next) ← decodeFunction fuel cursor
      decodeFunctions fuel count next (functions.push func)

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
  match tag with
  | 0 => Except.ok (.func, next)
  | 1 => Except.ok (.memory, next)
  | 2 => Except.ok (.global, next)
  | _ => Except.error errorExportKind

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

def containsExportName (name : ByteArray) : List Export → Bool
  | [] => false
  | export_ :: rest => export_.name == name || containsExportName name rest

def hasDuplicateExportName : List Export → Bool
  | [] => false
  | export_ :: rest =>
      containsExportName export_.name rest || hasDuplicateExportName rest

def validExportIndex (module_ : Module) (export_ : Export) : Bool :=
  match export_.kind with
  | .func => export_.index < module_.functions.size
  | .memory => export_.index == 0
  | .global => export_.index < module_.globals.size

def validateExports (module_ : Module) : List Export → Except ByteArray Unit
  | [] => Except.ok ()
  | export_ :: rest => do
      if export_.name.size > maxExportNameBytes then
        Except.error errorLimit
      else if !isAscii export_.name then
        Except.error errorExportName
      else if !validExportIndex module_ export_ then
        Except.error errorExportIndex
      else
        validateExports module_ rest

mutual
  def validateInstr (functionCount : Nat) (globals : Array Global)
      (localCount controlDepth : Nat) : Instr → Except ByteArray Unit
    | .localGet index | .localSet index | .localTee index =>
        if index < localCount then Except.ok () else Except.error errorLocalIndex
    | .globalGet index =>
        if index < globals.size then Except.ok () else Except.error errorGlobalIndex
    | .globalSet index =>
        if index >= globals.size then
          Except.error errorGlobalIndex
        else if globals[index]!.mutable_ then
          Except.ok ()
        else
          Except.error errorImmutableGlobal
    | .call index =>
        if index < functionCount then Except.ok () else Except.error errorFunctionIndex
    | .block body | .loop body =>
        validateInstrList functionCount globals localCount (controlDepth + 1) body
    | .iff _ thn els | .iffI32 thn els => do
        validateInstrList functionCount globals localCount (controlDepth + 1) thn
        match els with
        | some body =>
            validateInstrList functionCount globals localCount (controlDepth + 1) body
        | none => Except.ok ()
    | .br branchDepth | .brIf branchDepth =>
        if branchDepth < controlDepth then Except.ok () else Except.error errorBranchDepth
    | _ => Except.ok ()

  def validateInstrItems (functionCount : Nat) (globals : Array Global)
      (localCount controlDepth : Nat) : List Instr → Except ByteArray Unit
    | [] => Except.ok ()
    | instr :: rest => do
        validateInstr functionCount globals localCount controlDepth instr
        validateInstrItems functionCount globals localCount controlDepth rest

  def validateInstrList (functionCount : Nat) (globals : Array Global)
      (localCount controlDepth : Nat) (body : List Instr) : Except ByteArray Unit := do
    if body.length > maxInstructionsPerList || controlDepth > maxNestingDepth then
      Except.error errorLimit
    else
      validateInstrItems functionCount globals localCount controlDepth body
end

def validateFunctions (functionCount : Nat) (globals : Array Global) :
    List Function → Except ByteArray Unit
  | [] => Except.ok ()
  | func :: rest => do
      if func.params > maxParams || func.results > maxResults || func.locals > maxLocals then
        Except.error errorLimit
      else
        validateInstrList functionCount globals (func.params + func.locals) 0 func.body
        validateFunctions functionCount globals rest

def validateModule (module_ : Module) : Except ByteArray Unit := do
  if module_.memoryMinPages == 0 || module_.memoryMinPages > 65536 then
    Except.error errorMemory
  else if module_.globals.size > maxGlobals || module_.functions.size > maxFunctions ||
      module_.exports.size > maxExports then
    Except.error errorLimit
  else if hasDuplicateExportName module_.exports.toList then
    Except.error errorDuplicateExport
  else
    validateFunctions module_.functions.size module_.globals module_.functions.toList
    validateExports module_ module_.exports.toList

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
                decodeFunctions (input.size + 1) functionCount afterFunctionCount #[]
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
