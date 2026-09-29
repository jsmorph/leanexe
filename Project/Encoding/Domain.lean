import Project.Encoding.Spec.Modules
import Project.Encoding.Values

namespace Wasm.Encoding

mutual
  inductive InstructionForm : Wasm.Instruction → Prop
    | unreachable : InstructionForm .unreachable
    | nop : InstructionForm .nop
    | ret : InstructionForm .ret
    | drop : InstructionForm .drop
    | eqz : InstructionForm .eqz
    | eq : InstructionForm .eq
    | ltU : InstructionForm .ltU
    | gtU : InstructionForm .gtU
    | leU : InstructionForm .leU
    | geU : InstructionForm .geU
    | eqzI64 : InstructionForm .eqzI64
    | eqI64 : InstructionForm .eqI64
    | neI64 : InstructionForm .neI64
    | ltUI64 : InstructionForm .ltUI64
    | leUI64 : InstructionForm .leUI64
    | f64Eq : InstructionForm .f64Eq
    | f64Lt : InstructionForm .f64Lt
    | f64Le : InstructionForm .f64Le
    | f64Abs : InstructionForm .f64Abs
    | f64ConvertI64U : InstructionForm .f64ConvertI64U
    | geUI64 : InstructionForm .geUI64
    | add : InstructionForm .add
    | and : InstructionForm .and
    | addI64 : InstructionForm .addI64
    | subI64 : InstructionForm .subI64
    | mulI64 : InstructionForm .mulI64
    | divUI64 : InstructionForm .divUI64
    | remUI64 : InstructionForm .remUI64
    | andI64 : InstructionForm .andI64
    | orI64 : InstructionForm .orI64
    | xorI64 : InstructionForm .xorI64
    | shlI64 : InstructionForm .shlI64
    | shrUI64 : InstructionForm .shrUI64
    | f32Nearest : InstructionForm .f32Nearest
    | f32Sqrt : InstructionForm .f32Sqrt
    | f32Add : InstructionForm .f32Add
    | f32Sub : InstructionForm .f32Sub
    | f32Mul : InstructionForm .f32Mul
    | f32Div : InstructionForm .f32Div
    | f64Sqrt : InstructionForm .f64Sqrt
    | f64Add : InstructionForm .f64Add
    | f64Sub : InstructionForm .f64Sub
    | f64Mul : InstructionForm .f64Mul
    | f64Div : InstructionForm .f64Div
    | wrapI64 : InstructionForm .wrapI64
    | extendUI32 : InstructionForm .extendUI32
    | f32ConvertI32S : InstructionForm .f32ConvertI32S
    | f32DemoteF64 : InstructionForm .f32DemoteF64
    | f64PromoteF32 : InstructionForm .f64PromoteF32
    | i32ReinterpretF32 : InstructionForm .i32ReinterpretF32
    | i64ReinterpretF64 : InstructionForm .i64ReinterpretF64
    | f32ReinterpretI32 : InstructionForm .f32ReinterpretI32
    | f64ReinterpretI64 : InstructionForm .f64ReinterpretI64
    | extend8S : InstructionForm .extend8S
    | i32TruncSatF32S : InstructionForm .i32TruncSatF32S
    | i64TruncSatF64U : InstructionForm .i64TruncSatF64U
    | memorySize : InstructionForm .memorySize
    | memoryGrow : InstructionForm .memoryGrow
    | br (index : Nat) (bound : index < 2 ^ 32) : InstructionForm (.br index)
    | br_if (index : Nat) (bound : index < 2 ^ 32) : InstructionForm (.br_if index)
    | call (index : Nat) (bound : index < 2 ^ 32) : InstructionForm (.call index)
    | localGet (index : Nat) (bound : index < 2 ^ 32) : InstructionForm (.localGet index)
    | localSet (index : Nat) (bound : index < 2 ^ 32) : InstructionForm (.localSet index)
    | localTee (index : Nat) (bound : index < 2 ^ 32) : InstructionForm (.localTee index)
    | globalGet (index : Nat) (bound : index < 2 ^ 32) : InstructionForm (.globalGet index)
    | globalSet (index : Nat) (bound : index < 2 ^ 32) : InstructionForm (.globalSet index)
    | load32 (offset : UInt32) : InstructionForm (.load32 offset)
    | load64 (offset : UInt32) : InstructionForm (.load64 offset)
    | load8U (offset : UInt32) : InstructionForm (.load8U offset)
    | store32 (offset : UInt32) : InstructionForm (.store32 offset)
    | store64 (offset : UInt32) : InstructionForm (.store64 offset)
    | store8 (offset : UInt32) : InstructionForm (.store8 offset)
    | const32 (value : UInt32) : InstructionForm (.const value)
    | const64 (value : UInt64) : InstructionForm (.constI64 value)
    | constF64 (value : UInt64) : InstructionForm (.f64Const value)
    | block (types : List Wasm.ValueType) (body : Wasm.Program)
        (typeForm : BlockForm types) (bodyForm : ProgramForm body) :
        InstructionForm (.block 0 types.length body [] types)
    | loop (types : List Wasm.ValueType) (body : Wasm.Program)
        (typeForm : BlockForm types) (bodyForm : ProgramForm body) :
        InstructionForm (.loop 0 types.length body [] types)
    | iff (types : List Wasm.ValueType) (thenBody elseBody : Wasm.Program)
        (typeForm : BlockForm types)
        (thenForm : ProgramForm thenBody) (elseForm : ProgramForm elseBody) :
        InstructionForm (.iff 0 types.length thenBody elseBody [] types)

  inductive ProgramForm : Wasm.Program → Prop
    | nil : ProgramForm []
    | cons (head : Wasm.Instruction) (tail : Wasm.Program)
        (headForm : InstructionForm head) (tailForm : ProgramForm tail) :
        ProgramForm (head :: tail)
end

namespace Size

def u32 (value : Nat) : Nat := (unsigned 32 value).length

def s32 (value : UInt32) : Nat := (signed 32 value.toBitVec.toInt).length

def s64 (value : UInt64) : Nat := (signed 64 value.toBitVec.toInt).length

def vector (sizes : List Nat) : Nat := u32 sizes.length + sizes.sum

def name (value : String) : Nat := u32 value.toUTF8.size + value.toUTF8.size

mutual
  def instruction : Wasm.Instruction → Nat
    | .i32TruncSatF32S => 2
    | .i64TruncSatF64U => 2
    | .memorySize => 2
    | .memoryGrow => 2
    | .const value => 1 + s32 value
    | .constI64 value => 1 + s64 value
    | .f64Const _ => 9
    | .br index => 1 + u32 index
    | .br_if index => 1 + u32 index
    | .call index => 1 + u32 index
    | .localGet index => 1 + u32 index
    | .localSet index => 1 + u32 index
    | .localTee index => 1 + u32 index
    | .globalGet index => 1 + u32 index
    | .globalSet index => 1 + u32 index
    | .load32 offset => 2 + u32 offset.toNat
    | .load64 offset => 2 + u32 offset.toNat
    | .load8U offset => 2 + u32 offset.toNat
    | .store32 offset => 2 + u32 offset.toNat
    | .store64 offset => 2 + u32 offset.toNat
    | .store8 offset => 2 + u32 offset.toNat
    | .block _ _ body _ _ | .loop _ _ body _ _ => 3 + program body
    | .iff _ _ thenBody elseBody _ _ => 4 + program thenBody + program elseBody
    | _ => 1

  def program : Wasm.Program → Nat
    | [] => 0
    | head :: tail => instruction head + program tail
end

def functionType (type : Wasm.FuncType) : Nat :=
  1 + u32 type.params.length + type.params.length + u32 type.results.length + type.results.length

def bodyPayload (func : Wasm.Function) : Nat :=
  u32 func.locals.length + 2 * func.locals.length + program func.body + 1

def functionBody (func : Wasm.Function) : Nat :=
  u32 (bodyPayload func) + bodyPayload func

def limits (minimum : UInt32) (maximum : Option UInt32) : Nat :=
  1 + u32 minimum.toNat + (maximum.map (fun m => u32 m.toNat)).getD 0

def memory (decl : Wasm.MemDecl) : Nat := limits decl.pagesMin decl.pagesMax

def global (decl : Wasm.GlobalDecl) : Nat :=
  match decl.init with
  | .i32 value => 4 + s32 value
  | .i64 value => 4 + s64 value
  | _ => 0

def typeIndex (signature : Wasm.FuncType) : List Wasm.FuncType → Nat
  | [] => 0
  | head :: tail => if head = signature then 0 else typeIndex signature tail + 1

def importFunction (types : List Wasm.FuncType) (decl : Wasm.ImportDecl) : Nat :=
  name decl.module + name decl.name + 1 +
    u32 (typeIndex { params := decl.params, results := decl.results } types)

def exportEntry (entry : UInt8 × String × Nat) : Nat :=
  name entry.2.1 + 1 + u32 entry.2.2

end Size

structure TypeReady (type : Wasm.FuncType) : Prop where
  params : ∀ t ∈ type.params, Numeric t
  results : ∀ t ∈ type.results, Numeric t
  paramCount : type.params.length < 2 ^ 32
  resultCount : type.results.length < 2 ^ 32

structure FunctionReady (types : List Wasm.FuncType) (func : Wasm.Function) : Prop where
  typeIndex : ∃ index, func.typeIdx = some index ∧ types[index]? = some (Spec.signature func) ∧
    index < 2 ^ 32
  locals : ∀ t ∈ func.locals, Numeric t
  localCount : func.locals.length < 2 ^ 32
  body : ProgramForm func.body
  bodySize : Size.bodyPayload func < 2 ^ 32

structure ImportReady (types : List Wasm.FuncType) (decl : Wasm.ImportDecl) : Prop where
  signature : ({ params := decl.params, results := decl.results } : Wasm.FuncType) ∈ types
  index : Size.typeIndex { params := decl.params, results := decl.results } types < 2 ^ 32
  moduleName : decl.module.toUTF8.size < 2 ^ 32
  fieldName : decl.name.toUTF8.size < 2 ^ 32

structure ExportReady (entry : UInt8 × String × Nat) : Prop where
  kind : entry.1 = 0 ∨ entry.1 = 2 ∨ entry.1 = 3
  name : entry.2.1.toUTF8.size < 2 ^ 32
  index : entry.2.2 < 2 ^ 32

structure Ready (m : Wasm.Module) : Prop where
  shape : Spec.Shape m
  types : ∀ type ∈ m.types, TypeReady type
  imports : ∀ decl ∈ m.imports, ImportReady m.types decl
  functions : ∀ func ∈ m.funcs, FunctionReady m.types func
  memories : ∀ decl ∈ m.memory.toList, decl.data = [] ∧ decl.is64 = false
  globals : ∀ decl ∈ m.globals, GlobalReady decl
  exports : ∀ entry ∈ Spec.exports m, ExportReady entry
  typeCount : m.types.length < 2 ^ 32
  importCount : m.imports.length < 2 ^ 32
  functionCount : m.funcs.length < 2 ^ 32
  globalCount : m.globals.length < 2 ^ 32
  exportCount : (Spec.exports m).length < 2 ^ 32
  typeSize : Size.vector (m.types.map Size.functionType) < 2 ^ 32
  importSize : Size.vector (m.imports.map (Size.importFunction m.types)) < 2 ^ 32
  functionSize : Size.vector (m.funcs.map (fun f => Size.u32 (f.typeIdx.getD 0))) < 2 ^ 32
  memorySize : Size.vector (m.memory.toList.map Size.memory) < 2 ^ 32
  globalSize : Size.vector (m.globals.map Size.global) < 2 ^ 32
  exportSize : Size.vector ((Spec.exports m).map Size.exportEntry) < 2 ^ 32
  codeSize : Size.vector (m.funcs.map Size.functionBody) < 2 ^ 32

end Wasm.Encoding
