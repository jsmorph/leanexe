import Interpreter.Wasm.Syntax

/-!
Binary decoder for the subset of WebAssembly that `Wasm.Encoding.encode` produces:
numeric value types, function types, function imports, one 32-bit memory, integer
globals with constant initializers, function, memory, and global exports, and the
instructions listed in `plain`, `index`, and `memory`.  It follows the binary format
of the WebAssembly 3.0 specification
(https://webassembly.github.io/spec/core/binary/index.html) for that subset and
accepts every encoding the format allows there: optional and custom sections,
non-minimal LEB128 integers, grouped locals, and `if` without `else`.

Errors distinguish input the format rejects (`malformed`), well-formed input outside
the subset (`unsupported`), and index errors that prevent building the module
(`invalid`).  The decoder omits validation otherwise.
-/

namespace Wasm.Encoding.Decoder

inductive Error where
  | malformed (message : String)
  | unsupported (message : String)
  | invalid (message : String)
  deriving Repr, BEq, Inhabited

abbrev Parser := StateT (List UInt8) (Except Error)

def malformed (message : String) : Parser α := throw (.malformed message)
def unsupported (message : String) : Parser α := throw (.unsupported message)
def invalid (message : String) : Parser α := throw (.invalid message)

def byte : Parser UInt8 := do
  match ← get with
  | head :: tail => set tail; pure head
  | [] => malformed "unexpected end"

def take (count : Nat) : Parser (List UInt8) := do
  let input ← get
  if count ≤ input.length then
    set (input.drop count)
    pure (input.take count)
  else malformed "unexpected end"

/-- Eight bytes, least significant first, as a 64-bit word. -/
def fixed64 : Parser UInt64 := do
  let bytes ← take 8
  pure (UInt64.ofNat (bytes.foldr (fun b acc => b.toNat + 256 * acc) 0))

def remaining : Parser Nat := do
  return (← get).length

/-- `uN`: unsigned LEB128 with at most `⌈N/7⌉` bytes and no bits above `N`. -/
def unsigned (width : Nat) : Parser Nat := do
  let b ← byte
  if b.toNat < 128 then
    if b.toNat < 2 ^ width then pure b.toNat else malformed "integer too large"
  else if h : 7 < width then
    let rest ← unsigned (width - 7)
    pure (b.toNat - 128 + 128 * rest)
  else malformed "integer representation too long"
termination_by width

/-- `sN`: signed LEB128 with at most `⌈N/7⌉` bytes, sign-extended from the last. -/
def signed (width : Nat) : Parser Int := do
  let b ← byte
  if b.toNat < 64 then
    if b.toNat < 2 ^ (width - 1) then pure b.toNat else malformed "integer too large"
  else if b.toNat < 128 then
    if 128 - 2 ^ (width - 1) ≤ b.toNat then pure ((b.toNat : Int) - 128)
    else malformed "integer too large"
  else if h : 7 < width then
    let rest ← signed (width - 7)
    pure ((b.toNat : Int) - 128 + 128 * rest)
  else malformed "integer representation too long"
termination_by width

def wrap32 (value : Int) : UInt32 := UInt32.ofNat (value % 4294967296).toNat

def wrap64 (value : Int) : UInt64 := UInt64.ofNat (value % 18446744073709551616).toNat

def many (item : Parser α) : Nat → Parser (List α)
  | 0 => pure []
  | count + 1 => do
      let head ← item
      let tail ← many item count
      pure (head :: tail)

/-- `vec(B)`.  Every item in this subset occupies at least one byte, so a count
larger than the remaining input is malformed. -/
def vec (item : Parser α) : Parser (List α) := do
  let count ← unsigned 32
  let available ← remaining
  if available < count then malformed "unexpected end" else many item count

def name : Parser String := do
  let length ← unsigned 32
  let bytes ← take length
  match String.fromUTF8? ⟨bytes.toArray⟩ with
  | some value => pure value
  | none => malformed "malformed UTF-8 encoding"

/-- Runs `parser` on exactly the next `size` bytes. -/
def within (size : Nat) (parser : Parser α) : Parser α := do
  let contents ← take size
  match parser.run contents with
  | .ok (value, []) => pure value
  | .ok (_, _ :: _) => malformed "section size mismatch"
  | .error error => throw error

def valueType : Parser ValueType := do
  let b ← byte
  match b with
  | 0x7f => pure .i32
  | 0x7e => pure .i64
  | 0x7d => pure .f32
  | 0x7c => pure .f64
  | _ =>
      if b = 0x7b ∨ (0x63 ≤ b ∧ b ≤ 0x74) then unsupported "vector or reference type"
      else malformed "malformed value type"

def funcType : Parser FuncType := do
  let b ← byte
  match b with
  | 0x60 => do
      let params ← vec valueType
      let results ← vec valueType
      pure { params, results }
  | 0x4e | 0x4f | 0x50 | 0x5e | 0x5f => unsupported "GC type definition"
  | _ => malformed "malformed function type"

def importDecl (types : List FuncType) : Parser ImportDecl := do
  let moduleName ← name
  let fieldName ← name
  let kind ← byte
  match kind with
  | 0x00 => do
      let index ← unsigned 32
      match types[index]? with
      | some type =>
          pure { «module» := moduleName, name := fieldName,
                 params := type.params, results := type.results }
      | none => invalid "unknown type"
  | 0x01 | 0x02 | 0x03 | 0x04 => unsupported "non-function import"
  | _ => malformed "malformed import kind"

def memType : Parser MemDecl := do
  let flags ← byte
  match flags with
  | 0x00 => do
      let minimum ← unsigned 32
      pure { pagesMin := UInt32.ofNat minimum }
  | 0x01 => do
      let minimum ← unsigned 32
      let maximum ← unsigned 32
      pure { pagesMin := UInt32.ofNat minimum, pagesMax := some (UInt32.ofNat maximum) }
  | 0x02 | 0x03 | 0x04 | 0x05 | 0x06 | 0x07 => unsupported "shared or 64-bit memory"
  | _ => malformed "malformed limits flags"

def memories : Parser (Option MemDecl) := do
  match ← vec memType with
  | [] => pure none
  | [memory] => pure (some memory)
  | _ => unsupported "multiple memories"

def constEnd : Parser Unit := do
  if (← byte) ≠ 0x0b then unsupported "global initializer"

def mutability : Parser Bool := do
  match ← byte with
  | 0x00 => pure false
  | 0x01 => pure true
  | _ => malformed "malformed mutability"

def global : Parser GlobalDecl := do
  let type ← valueType
  let mutable ← mutability
  let opcode ← byte
  match type, opcode with
  | .i32, 0x41 => do
      let value := wrap32 (← signed 32)
      constEnd
      pure { init := .i32 value, declaredType := some .i32, isMut := mutable,
             sourceInit := some [.const value] }
  | .i64, 0x42 => do
      let value := wrap64 (← signed 64)
      constEnd
      pure { init := .i64 value, declaredType := some .i64, isMut := mutable,
             sourceInit := some [.constI64 value] }
  | _, _ => unsupported "global initializer"

def exportEntry : Parser (UInt8 × String × Nat) := do
  let exportName ← name
  let kind ← byte
  let index ← unsigned 32
  match kind with
  | 0x00 | 0x02 | 0x03 => pure (kind, exportName, index)
  | 0x01 | 0x04 => unsupported "table or tag export"
  | _ => malformed "malformed export kind"

def blockType : Parser (List ValueType) := do
  match ← byte with
  | 0x40 => pure []
  | 0x7f => pure [.i32]
  | 0x7e => pure [.i64]
  | 0x7d => pure [.f32]
  | 0x7c => pure [.f64]
  | _ => unsupported "block type"

/-- `memarg` for an access whose natural alignment is `2 ^ natural` bytes. -/
def memArg (natural : Nat) : Parser UInt32 := do
  let alignment ← unsigned 32
  if 64 ≤ alignment then unsupported "memory index in memarg"
  let offset ← unsigned 64
  if natural < alignment then invalid "alignment must not be larger than natural"
  if 4294967296 ≤ offset then invalid "offset out of range for a 32-bit memory"
  pure (UInt32.ofNat offset)

def plain : UInt8 → Option Instruction
  | 0x00 => some .unreachable
  | 0x01 => some .nop
  | 0x0f => some .ret
  | 0x1a => some .drop
  | 0x45 => some .eqz
  | 0x46 => some .eq
  | 0x49 => some .ltU
  | 0x4b => some .gtU
  | 0x4d => some .leU
  | 0x4f => some .geU
  | 0x50 => some .eqzI64
  | 0x51 => some .eqI64
  | 0x52 => some .neI64
  | 0x54 => some .ltUI64
  | 0x58 => some .leUI64
  | 0x61 => some .f64Eq
  | 0x63 => some .f64Lt
  | 0x65 => some .f64Le
  | 0x5a => some .geUI64
  | 0x6a => some .add
  | 0x71 => some .and
  | 0x7c => some .addI64
  | 0x7d => some .subI64
  | 0x7e => some .mulI64
  | 0x80 => some .divUI64
  | 0x82 => some .remUI64
  | 0x83 => some .andI64
  | 0x84 => some .orI64
  | 0x85 => some .xorI64
  | 0x86 => some .shlI64
  | 0x88 => some .shrUI64
  | 0x90 => some .f32Nearest
  | 0x91 => some .f32Sqrt
  | 0x92 => some .f32Add
  | 0x93 => some .f32Sub
  | 0x94 => some .f32Mul
  | 0x95 => some .f32Div
  | 0x99 => some .f64Abs
  | 0xba => some .f64ConvertI64U
  | 0x9f => some .f64Sqrt
  | 0xa0 => some .f64Add
  | 0xa1 => some .f64Sub
  | 0xa2 => some .f64Mul
  | 0xa3 => some .f64Div
  | 0xa7 => some .wrapI64
  | 0xad => some .extendUI32
  | 0xb2 => some .f32ConvertI32S
  | 0xb6 => some .f32DemoteF64
  | 0xbb => some .f64PromoteF32
  | 0xbc => some .i32ReinterpretF32
  | 0xbd => some .i64ReinterpretF64
  | 0xbe => some .f32ReinterpretI32
  | 0xbf => some .f64ReinterpretI64
  | 0xc0 => some .extend8S
  | _ => none

def index : UInt8 → Option (Nat → Instruction)
  | 0x0c => some .br
  | 0x0d => some .br_if
  | 0x10 => some .call
  | 0x20 => some .localGet
  | 0x21 => some .localSet
  | 0x22 => some .localTee
  | 0x23 => some .globalGet
  | 0x24 => some .globalSet
  | _ => none

/-- Memory accesses: the natural alignment exponent and the constructor. -/
def memory : UInt8 → Option (Nat × (UInt32 → Instruction))
  | 0x28 => some (2, .load32)
  | 0x29 => some (3, .load64)
  | 0x2d => some (0, .load8U)
  | 0x36 => some (2, .store32)
  | 0x37 => some (3, .store64)
  | 0x3a => some (0, .store8)
  | _ => none

inductive Terminator where
  | «end»
  | «else»
  deriving DecidableEq

/-- Decodes instructions up to and including the next `end` or `else` at this
nesting level.  Every call consumes at least one byte before recursing, so `fuel`
equal to the remaining input suffices. -/
def instructions : Nat → Parser (List Instruction × Terminator)
  | 0 => malformed "unexpected end"
  | fuel + 1 => do
      let opcode ← byte
      match opcode with
      | 0x0b => pure ([], .end)
      | 0x05 => pure ([], .else)
      | 0x02 | 0x03 => do
          let types ← blockType
          let (body, terminator) ← instructions fuel
          if terminator = .else then malformed "else outside if"
          let instruction : Instruction :=
            if opcode = 0x02 then .block 0 types.length body [] types
            else .loop 0 types.length body [] types
          let (rest, last) ← instructions fuel
          pure (instruction :: rest, last)
      | 0x04 => do
          let types ← blockType
          let (thenBody, terminator) ← instructions fuel
          let elseBody ←
            if terminator = .else then do
              let (elseBody, elseTerminator) ← instructions fuel
              if elseTerminator = .else then malformed "else outside if"
              pure elseBody
            else pure []
          let (rest, last) ← instructions fuel
          pure (.iff 0 types.length thenBody elseBody [] types :: rest, last)
      | _ => do
          let instruction ← decodeOther opcode
          let (rest, last) ← instructions fuel
          pure (instruction :: rest, last)
where
  decodeOther (opcode : UInt8) : Parser Instruction := do
    if let some instruction := plain opcode then return instruction
    if let some make := index opcode then return make (← unsigned 32)
    if let some (natural, make) := memory opcode then return make (← memArg natural)
    match opcode with
    | 0x41 => return .const (wrap32 (← signed 32))
    | 0x42 => return .constI64 (wrap64 (← signed 64))
    | 0x44 => return .f64Const (← fixed64)
    | 0x3f | 0x40 => do
        if (← unsigned 32) ≠ 0 then unsupported "memory index"
        return if opcode = 0x3f then .memorySize else .memoryGrow
    | 0xfc => do
        match ← unsigned 32 with
        | 0 => return .i32TruncSatF32S
        | 7 => return .i64TruncSatF64U
        | _ => unsupported "0xfc instruction"
    | _ => unsupported s!"opcode {opcode}"

/-- Wasmtime's per-function limit on locals. -/
def maxLocals : Nat := 50000

def localGroup : Parser (Nat × ValueType) := do
  let count ← unsigned 32
  let type ← valueType
  pure (count, type)

def codeBody : Parser (List ValueType × Program) := do
  let groups ← vec localGroup
  let total := (groups.map (·.1)).sum
  if 2 ^ 32 ≤ total then malformed "too many locals"
  else if maxLocals < total then unsupported "more locals than the implementation limit"
  else do
    let locals := groups.flatMap fun (count, type) => List.replicate count type
    let available ← remaining
    let (body, terminator) ← instructions available
    if terminator = .else then malformed "else outside if" else pure (locals, body)

def code : Parser (List ValueType × Program) := do
  let size ← unsigned 32
  within size codeBody

structure Sections where
  types : List FuncType := []
  imports : List ImportDecl := []
  functions : List Nat := []
  memory : Option MemDecl := none
  globals : List GlobalDecl := []
  exports : List (UInt8 × String × Nat) := []
  codes : List (List ValueType × Program) := []

/-- Position of a section id in the required order, or 0 for an unknown id. -/
def sectionOrder : UInt8 → Nat
  | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 13 => 6 | 6 => 7
  | 7 => 8 | 8 => 9 | 9 => 10 | 12 => 11 | 10 => 12 | 11 => 13
  | _ => 0

def customSection : Parser Unit := do
  let _ ← name
  let rest ← remaining
  let _ ← take rest

def sectionContents (id : UInt8) (size : Nat) (acc : Sections) : Parser Sections :=
  match id with
  | 1 => return { acc with types := ← within size (vec funcType) }
  | 2 => return { acc with imports := ← within size (vec (importDecl acc.types)) }
  | 3 => return { acc with functions := ← within size (vec (unsigned 32)) }
  | 5 => return { acc with memory := ← within size memories }
  | 6 => return { acc with globals := ← within size (vec global) }
  | 7 => return { acc with exports := ← within size (vec exportEntry) }
  | 10 => return { acc with codes := ← within size (vec code) }
  | _ => unsupported s!"section {id}"

def sections : Nat → Nat → Sections → Parser Sections
  | 0, _, acc => pure acc
  | fuel + 1, last, acc => do
      let available ← remaining
      if available = 0 then pure acc else do
        let id ← byte
        let size ← unsigned 32
        if id = 0 then do
          within size customSection
          sections fuel last acc
        else if sectionOrder id = 0 then malformed "malformed section id"
        else if sectionOrder id ≤ last then malformed "unexpected content after last section"
        else do
          let acc ← sectionContents id size acc
          sections fuel (sectionOrder id) acc

def function (types : List FuncType) (typeIndex : Nat)
    (body : List ValueType × Program) : Parser Function := do
  match types[typeIndex]? with
  | some type =>
      pure { params := type.params, locals := body.1, body := body.2,
             results := type.results, typeIdx := some typeIndex }
  | none => invalid "unknown type"

def functions (types : List FuncType) :
    List Nat → List (List ValueType × Program) → Parser (List Function)
  | [], [] => pure []
  | typeIndex :: indices, body :: bodies => do
      let head ← function types typeIndex body
      let tail ← functions types indices bodies
      pure (head :: tail)
  | _, _ => malformed "function and code section have inconsistent lengths"

def assemble (found : Sections) (funcs : List Function) : Module :=
  { funcs
    exports := found.exports.filterMap fun (kind, exportName, index) =>
      if kind = 0x00 then some { name := exportName, funcIdx := index } else none
    memory := found.memory
    globals := found.globals
    imports := found.imports
    types := found.types
    gcTypes := found.types.map fun type => { comp := .func type }
    globalExports := found.exports.filterMap fun (kind, exportName, index) =>
      if kind = 0x03 then some (exportName, index) else none
    memoryExports := found.exports.filterMap fun (kind, exportName, index) =>
      if kind = 0x02 then some (exportName, index) else none }

def moduleParser : Parser Module := do
  let magic ← take 4
  if magic ≠ [0x00, 0x61, 0x73, 0x6d] then malformed "magic header not detected" else do
    let version ← take 4
    if version ≠ [0x01, 0x00, 0x00, 0x00] then malformed "unknown binary version" else do
      let available ← remaining
      let found ← sections available 0 {}
      let funcs ← functions found.types found.functions found.codes
      pure (assemble found funcs)

end Wasm.Encoding.Decoder

namespace Wasm.Encoding

def decode (bytes : ByteArray) : Except Decoder.Error Wasm.Module :=
  match Decoder.moduleParser.run bytes.data.toList with
  | .ok (module_, []) => .ok module_
  | .ok (_, _ :: _) => .error (.malformed "unexpected content after last section")
  | .error error => .error error

end Wasm.Encoding
