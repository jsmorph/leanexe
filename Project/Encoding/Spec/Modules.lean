import Project.Encoding.Spec.Instructions

namespace Wasm.Encoding.Spec

def signature (func : Wasm.Function) : Wasm.FuncType :=
  { params := func.params, results := func.results }

inductive FunctionIndex (types : List Wasm.FuncType) : Bytes → Wasm.Function → Prop
  | intro (bytes : Bytes) (index : Nat) (func : Wasm.Function)
      (encoding : Unsigned 32 bytes index)
      (declaredIndex : func.typeIdx = some index)
      (declaredType : types[index]? = some (signature func)) :
      FunctionIndex types bytes func

inductive Import (types : List Wasm.FuncType) : Bytes → Wasm.ImportDecl → Prop
  | intro (moduleBytes nameBytes indexBytes : Bytes) (decl : Wasm.ImportDecl) (index : Nat)
      (moduleName : Name moduleBytes decl.module)
      (fieldName : Name nameBytes decl.name)
      (encoding : Unsigned 32 indexBytes index)
      (declaredType : types[index]? = some { params := decl.params, results := decl.results }) :
      Import types (moduleBytes ++ nameBytes ++ 0 :: indexBytes) decl

inductive Local : Bytes → Wasm.ValueType → Prop
  | intro (bytes : Bytes) (type : Wasm.ValueType) (encoding : ValType bytes type) :
      Local (1 :: bytes) type

inductive CodeBody : Bytes → Wasm.Function → Prop
  | intro (localBytes instructionBytes : Bytes) (func : Wasm.Function)
      (locals : Vector Local localBytes func.locals)
      (instructions : Instrs instructionBytes func.body) :
      CodeBody (localBytes ++ instructionBytes ++ [0x0b]) func

inductive Export : Bytes → (UInt8 × String × Nat) → Prop
  | intro (nameBytes indexBytes : Bytes) (kind : UInt8) (name : String) (index : Nat)
      (kindValid : kind = 0 ∨ kind = 2 ∨ kind = 3)
      (nameEncoding : Name nameBytes name)
      (indexEncoding : Unsigned 32 indexBytes index) :
      Export (nameBytes ++ kind :: indexBytes) (kind, name, index)

def exports (m : Wasm.Module) : List (UInt8 × String × Nat) :=
  m.exports.map (fun e => (0, e.name, e.funcIdx)) ++
  m.globalExports.map (fun e => (3, e.1, e.2)) ++
  m.memoryExports.map (fun e => (2, e.1, e.2))

structure Shape (m : Wasm.Module) : Prop where
  extraMemories : m.extraMemories = []
  dataWithoutMemory : m.dataWithoutMemory = false
  start : m.startFunc = none
  gcTypes : m.gcTypes = m.types.map (fun type => { comp := .func type })
  tables : m.tables = []
  elements : m.elements = []
  importedGlobals : m.importedGlobals = []
  importedTables : m.importedTables = []
  importedMemories : m.importedMemories = []
  importedTags : m.importedTags = []
  tableExports : m.tableExports = []
  tagExports : m.tagExports = []
  tags : m.tags = []

inductive Section (id : UInt8) (relation : Bytes → α → Prop) : Bytes → α → Prop
  | intro (sizeBytes payload : Bytes) (value : α)
      (size : Unsigned 32 sizeBytes payload.length)
      (encoding : relation payload value) :
      Section id relation (id :: (sizeBytes ++ payload)) value

inductive ModuleBytes : Bytes → Wasm.Module → Prop
  | intro (m : Wasm.Module) (types imports functions memories globals exports codes : Bytes)
      (shape : Shape m)
      (typeSection : Section 1 (Vector FuncType) types m.types)
      (importSection : Section 2 (Vector (Import m.types)) imports m.imports)
      (functionSection : Section 3 (Vector (FunctionIndex m.types)) functions m.funcs)
      (memorySection : Section 5 (Vector Memory) memories m.memory.toList)
      (globalSection : Section 6 (Vector Global) globals m.globals)
      (exportSection : Section 7 (Vector Export) exports (Spec.exports m))
      (codeSection : Section 10 (Vector (Sized CodeBody)) codes m.funcs) :
      ModuleBytes ([0, 97, 115, 109, 1, 0, 0, 0] ++ types ++ imports ++ functions ++
        memories ++ globals ++ exports ++ codes) m

end Wasm.Encoding.Spec

namespace Wasm.Encoding

def Encodes (m : Wasm.Module) (bytes : ByteArray) : Prop :=
  Spec.ModuleBytes bytes.data.toList m

end Wasm.Encoding
