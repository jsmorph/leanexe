import Project.Encoding.Spec.Modules

namespace Wasm.Encoding.Spec.Validity

def Types (types : List Wasm.ValueType) : Prop := ∀ type ∈ types, Numeric type

structure Context where
  functions : List Wasm.FuncType
  locals : List Wasm.ValueType
  globals : List (Wasm.ValueType × Bool)
  labels : List (List Wasm.ValueType)
  results : List Wasm.ValueType
  hasMemory : Bool

inductive Unary : Wasm.Instruction → Wasm.ValueType → Wasm.ValueType → Prop
  | eqz : Unary .eqz .i32 .i32
  | eqzI64 : Unary .eqzI64 .i64 .i32
  | wrapI64 : Unary .wrapI64 .i64 .i32
  | extendUI32 : Unary .extendUI32 .i32 .i64
  | f32Nearest : Unary .f32Nearest .f32 .f32
  | f32Sqrt : Unary .f32Sqrt .f32 .f32
  | f64Sqrt : Unary .f64Sqrt .f64 .f64
  | f64Abs : Unary .f64Abs .f64 .f64
  | f64ConvertI64U : Unary .f64ConvertI64U .i64 .f64
  | f32ConvertI32S : Unary .f32ConvertI32S .i32 .f32
  | i32TruncSatF32S : Unary .i32TruncSatF32S .f32 .i32
  | i64TruncSatF64U : Unary .i64TruncSatF64U .f64 .i64
  | extend8S : Unary .extend8S .i32 .i32
  | f32DemoteF64 : Unary .f32DemoteF64 .f64 .f32
  | f64PromoteF32 : Unary .f64PromoteF32 .f32 .f64
  | i32ReinterpretF32 : Unary .i32ReinterpretF32 .f32 .i32
  | i64ReinterpretF64 : Unary .i64ReinterpretF64 .f64 .i64
  | f32ReinterpretI32 : Unary .f32ReinterpretI32 .i32 .f32
  | f64ReinterpretI64 : Unary .f64ReinterpretI64 .i64 .f64

inductive Binary : Wasm.Instruction → Wasm.ValueType → Wasm.ValueType → Prop
  | eq : Binary .eq .i32 .i32
  | ltU : Binary .ltU .i32 .i32
  | gtU : Binary .gtU .i32 .i32
  | leU : Binary .leU .i32 .i32
  | geU : Binary .geU .i32 .i32
  | add : Binary .add .i32 .i32
  | and : Binary .and .i32 .i32
  | eqI64 : Binary .eqI64 .i64 .i32
  | f64Eq : Binary .f64Eq .f64 .i32
  | f64Lt : Binary .f64Lt .f64 .i32
  | f64Le : Binary .f64Le .f64 .i32
  | neI64 : Binary .neI64 .i64 .i32
  | ltUI64 : Binary .ltUI64 .i64 .i32
  | leUI64 : Binary .leUI64 .i64 .i32
  | geUI64 : Binary .geUI64 .i64 .i32
  | addI64 : Binary .addI64 .i64 .i64
  | subI64 : Binary .subI64 .i64 .i64
  | mulI64 : Binary .mulI64 .i64 .i64
  | divUI64 : Binary .divUI64 .i64 .i64
  | remUI64 : Binary .remUI64 .i64 .i64
  | andI64 : Binary .andI64 .i64 .i64
  | orI64 : Binary .orI64 .i64 .i64
  | xorI64 : Binary .xorI64 .i64 .i64
  | shlI64 : Binary .shlI64 .i64 .i64
  | shrUI64 : Binary .shrUI64 .i64 .i64
  | f32Add : Binary .f32Add .f32 .f32
  | f32Sub : Binary .f32Sub .f32 .f32
  | f32Mul : Binary .f32Mul .f32 .f32
  | f32Div : Binary .f32Div .f32 .f32
  | f64Add : Binary .f64Add .f64 .f64
  | f64Sub : Binary .f64Sub .f64 .f64
  | f64Mul : Binary .f64Mul .f64 .f64
  | f64Div : Binary .f64Div .f64 .f64

inductive Load : (UInt32 → Wasm.Instruction) → Wasm.ValueType → Prop
  | i32 : Load .load32 .i32
  | i64 : Load .load64 .i64
  | i32_8 : Load .load8U .i32

inductive Store : (UInt32 → Wasm.Instruction) → Wasm.ValueType → Prop
  | i32 : Store .store32 .i32
  | i64 : Store .store64 .i64
  | i32_8 : Store .store8 .i32

mutual
  inductive Instruction : Context → Wasm.Instruction →
      List Wasm.ValueType → List Wasm.ValueType → Prop
    | nop : Instruction context .nop [] []
    | unreachable (inputs outputs : List Wasm.ValueType)
        (inTypes : Types inputs) (outTypes : Types outputs) :
        Instruction context .unreachable inputs outputs
    | drop (numeric : Numeric type) : Instruction context .drop [type] []
    | unary (op : Unary instr input output) : Instruction context instr [input] [output]
    | binary (op : Binary instr input output) : Instruction context instr [input, input] [output]
    | const32 (value : UInt32) : Instruction context (.const value) [] [.i32]
    | const64 (value : UInt64) : Instruction context (.constI64 value) [] [.i64]
    | constF64 (value : UInt64) : Instruction context (.f64Const value) [] [.f64]
    | constF32 (value : UInt32) : Instruction context (.f32Const value) [] [.f32]
    | localGet (index : Nat) (found : context.locals[index]? = some type) :
        Instruction context (.localGet index) [] [type]
    | localSet (index : Nat) (found : context.locals[index]? = some type) :
        Instruction context (.localSet index) [type] []
    | localTee (index : Nat) (found : context.locals[index]? = some type) :
        Instruction context (.localTee index) [type] [type]
    | globalGet (index : Nat) (found : context.globals[index]? = some (type, mutable)) :
        Instruction context (.globalGet index) [] [type]
    | globalSet (index : Nat) (found : context.globals[index]? = some (type, true)) :
        Instruction context (.globalSet index) [type] []
    | call (index : Nat) (type : Wasm.FuncType) (found : context.functions[index]? = some type) :
        Instruction context (.call index) type.params type.results
    | load (op : Load make type) (offset : UInt32) (memory : context.hasMemory = true) :
        Instruction context (make offset) [.i32] [type]
    | store (op : Store make type) (offset : UInt32) (memory : context.hasMemory = true) :
        Instruction context (make offset) [.i32, type] []
    | memorySize (memory : context.hasMemory = true) :
        Instruction context .memorySize [] [.i32]
    | memoryGrow (memory : context.hasMemory = true) :
        Instruction context .memoryGrow [.i32] [.i32]
    | block (form : BlockForm results)
        (body : Program { context with labels := results :: context.labels } code [] results) :
        Instruction context (.block 0 results.length code [] results) [] results
    | loop (form : BlockForm results)
        (body : Program { context with labels := [] :: context.labels } code [] results) :
        Instruction context (.loop 0 results.length code [] results) [] results
    | iff (form : BlockForm results)
        (thenBody : Program { context with labels := results :: context.labels } yes [] results)
        (elseBody : Program { context with labels := results :: context.labels } no [] results) :
        Instruction context (.iff 0 results.length yes no [] results) [.i32] results
    | br (index : Nat) (found : context.labels[index]? = some results)
        (inTypes : Types inputs) (outTypes : Types outputs) :
        Instruction context (.br index) (inputs ++ results) outputs
    | brIf (index : Nat) (found : context.labels[index]? = some results) :
        Instruction context (.br_if index) (results ++ [.i32]) results
    | ret (inTypes : Types inputs) (outTypes : Types outputs) :
        Instruction context .ret (inputs ++ context.results) outputs
    | frame (typed : Instruction context instr inputs outputs) (stackTypes : Types stack) :
        Instruction context instr (stack ++ inputs) (stack ++ outputs)

  inductive Program : Context → Wasm.Program →
      List Wasm.ValueType → List Wasm.ValueType → Prop
    | nil (valid : Types types) : Program context [] types types
    | cons (head : Instruction context instr inputs middle)
        (tail : Program context code middle outputs) :
        Program context (instr :: code) inputs outputs
end

def functionTypes (m : Wasm.Module) : List Wasm.FuncType :=
  m.imports.map (fun d => { params := d.params, results := d.results }) ++ m.funcs.map signature

def globalTypes (m : Wasm.Module) : List (Wasm.ValueType × Bool) :=
  m.globals.map (fun g => (g.declaredType.getD .i32, g.isMut))

def functionContext (m : Wasm.Module) (func : Wasm.Function) : Context :=
  { functions := functionTypes m, locals := func.params ++ func.locals,
    globals := globalTypes m, labels := [func.results], results := func.results,
    hasMemory := m.memory.isSome }

def Function (m : Wasm.Module) (func : Wasm.Function) : Prop :=
  (∃ index, func.typeIdx = some index ∧ m.types[index]? = some (signature func)) ∧
  Types func.locals ∧ func.params.length + func.locals.length < 2 ^ 32 ∧
  Program (functionContext m func) func.body [] func.results

def Memory (decl : Wasm.MemDecl) : Prop :=
  decl.is64 = false ∧ decl.data = [] ∧ decl.pagesMin.toNat ≤ 65536 ∧
  ∀ maximum ∈ decl.pagesMax, decl.pagesMin ≤ maximum ∧ maximum.toNat ≤ 65536

structure Module (m : Wasm.Module) : Prop where
  shape : Shape m
  types : ∀ type ∈ m.types, Types type.params ∧ Types type.results
  imports : ∀ decl ∈ m.imports,
    ({ params := decl.params, results := decl.results } : Wasm.FuncType) ∈ m.types
  functions : ∀ func ∈ m.funcs, Function m func
  memories : ∀ decl ∈ m.memory, Memory decl
  globals : ∀ decl ∈ m.globals, GlobalReady decl
  functionCount : m.imports.length + m.funcs.length < 2 ^ 32
  functionExports : ∀ e ∈ m.exports, e.funcIdx < m.imports.length + m.funcs.length
  globalExports : ∀ e ∈ m.globalExports, e.2 < m.globals.length
  memoryExports : ∀ e ∈ m.memoryExports, e.2 = 0 ∧ m.memory.isSome = true
  distinctExports : ((exports m).map (fun e => e.2.1)).Nodup

end Wasm.Encoding.Spec.Validity
