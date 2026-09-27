import Project.Encoding.Instructions
import Project.Encoding.Spec.Modules

deriving instance DecidableEq for Wasm.GcTypeDef

namespace Wasm.Encoding

def signatureIndex (signature : Wasm.FuncType) : (types : List Wasm.FuncType) →
    Except String { index : Nat // types[index]? = some signature }
  | [] => .error "function signature is absent from the type section"
  | head :: tail =>
      if same : head = signature then
        .ok ⟨0, by simp [same]⟩
      else do
        let index ← signatureIndex signature tail
        pure ⟨index.val + 1, by simpa using index.property⟩

def functionIndex (types : List Wasm.FuncType) (func : Wasm.Function) :
    Result (Spec.FunctionIndex types) func :=
  match declared : func.typeIdx with
  | none => .error "function has no declared type index"
  | some index =>
      if agrees : types[index]? = some (Spec.signature func) then do
        let encoded ← u32 index
        pure ⟨encoded.val, .intro _ _ _ encoded.property declared agrees⟩
      else .error "function signature disagrees with its declared type index"

def importFunction (types : List Wasm.FuncType) (decl : Wasm.ImportDecl) :
    Result (Spec.Import types) decl := do
  let index ← signatureIndex { params := decl.params, results := decl.results } types
  let moduleName ← name decl.module
  let fieldName ← name decl.name
  let encodedIndex ← u32 index.val
  pure ⟨moduleName.val ++ fieldName.val ++ 0 :: encodedIndex.val,
    .intro _ _ _ _ _ moduleName.property fieldName.property encodedIndex.property index.property⟩

def localEntry (type : Wasm.ValueType) : Result Spec.Local type := do
  let encoded ← valueType type
  pure ⟨1 :: encoded.val, .intro _ _ encoded.property⟩

def functionBody (func : Wasm.Function) : Result (Spec.Sized Spec.CodeBody) func := do
  let locals ← vector localEntry func.locals
  let body ← program func.body
  sized ⟨locals.val ++ body.val ++ [0x0b], .intro _ _ _ locals.property body.property⟩

def exportEntry : (entry : UInt8 × String × Nat) → Result Spec.Export entry
  | (kind, exportName, index) => do
      if valid : kind = 0 ∨ kind = 2 ∨ kind = 3 then
        let nameBytes ← name exportName
        let indexBytes ← u32 index
        pure ⟨nameBytes.val ++ kind :: indexBytes.val,
          .intro _ _ _ _ _ valid nameBytes.property indexBytes.property⟩
      else .error "export kind is outside LeanExe's emitted WASM"

def require (condition : Prop) [Decidable condition] (message : String) :
    Except String (PLift condition) :=
  if proof : condition then .ok ⟨proof⟩ else .error message

def requireEmpty (message : String) : (values : List α) → Except String (PLift (values = []))
  | [] => .ok ⟨rfl⟩
  | _ :: _ => .error message

def shape (m : Wasm.Module) : Except String (PLift (Spec.Shape m)) := do
  let extraMemories ← requireEmpty "module has additional memories" m.extraMemories
  let dataWithoutMemory ← require (m.dataWithoutMemory = false) "module has data without memory"
  let start ← require (m.startFunc = none) "module has a start section"
  let gcTypes ← require (m.gcTypes = m.types.map (fun t => { comp := .func t }))
    "GC type metadata disagrees with the function type section"
  let tables ← requireEmpty "module has tables" m.tables
  let elements ← requireEmpty "module has element segments" m.elements
  let importedGlobals ← requireEmpty "module imports globals" m.importedGlobals
  let importedTables ← requireEmpty "module imports tables" m.importedTables
  let importedMemories ← requireEmpty "module imports memories" m.importedMemories
  let importedTags ← requireEmpty "module imports exception tags" m.importedTags
  let tableExports ← requireEmpty "module exports tables" m.tableExports
  let tagExports ← requireEmpty "module exports exception tags" m.tagExports
  let tags ← requireEmpty "module has exception tags" m.tags
  pure ⟨{
    extraMemories := extraMemories.down
    dataWithoutMemory := dataWithoutMemory.down
    start := start.down
    gcTypes := gcTypes.down
    tables := tables.down
    elements := elements.down
    importedGlobals := importedGlobals.down
    importedTables := importedTables.down
    importedMemories := importedMemories.down
    importedTags := importedTags.down
    tableExports := tableExports.down
    tagExports := tagExports.down
    tags := tags.down }⟩

def sectionBytes (id : UInt8) (payload : Encoded relation value) :
    Result (Spec.Section id relation) value := do
  let size ← u32 payload.val.length
  pure ⟨id :: (size.val ++ payload.val), .intro _ _ _ size.property payload.property⟩

def module (m : Wasm.Module) : Result Spec.ModuleBytes m := do
  let fields ← shape m
  let types ← vector functionType m.types >>= sectionBytes 1
  let imports ← vector (importFunction m.types) m.imports >>= sectionBytes 2
  let functions ← vector (functionIndex m.types) m.funcs >>= sectionBytes 3
  let memories ← vector memory m.memory.toList >>= sectionBytes 5
  let globals ← vector global m.globals >>= sectionBytes 6
  let exports ← vector exportEntry (Spec.exports m) >>= sectionBytes 7
  let codes ← vector functionBody m.funcs >>= sectionBytes 10
  pure ⟨[0, 97, 115, 109, 1, 0, 0, 0] ++ types.val ++ imports.val ++ functions.val ++
    memories.val ++ globals.val ++ exports.val ++ codes.val,
    .intro _ _ _ _ _ _ _ _ fields.down types.property imports.property functions.property
      memories.property globals.property exports.property codes.property⟩

def encode (m : Wasm.Module) : Except String ByteArray :=
  (module m).map fun encoded => ⟨encoded.val.toArray⟩

theorem encode_correct (m : Wasm.Module) (bytes : ByteArray)
    (success : encode m = .ok bytes) : Encodes m bytes := by
  unfold encode at success
  cases encoded : module m with
  | error message => simp [encoded, Except.map] at success
  | ok output =>
      simp only [encoded, Except.map, Except.ok.injEq] at success
      subst bytes
      simpa [Encodes] using output.property

theorem encode_preserves (property : Wasm.Module → Prop) (m : Wasm.Module)
    (bytes : ByteArray) (holds : property m) (success : encode m = .ok bytes) :
    ∃ represented, Encodes represented bytes ∧ property represented :=
  ⟨m, encode_correct m bytes success, holds⟩

def writeModule (path : System.FilePath) (m : Wasm.Module) : IO Unit := do
  match encode m with
  | .ok bytes => IO.FS.writeBinFile path bytes
  | .error message => throw (IO.userError message)

end Wasm.Encoding
