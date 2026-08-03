import Project.Artifact.Binary.Grammar

namespace Wasm.Binary.Validity

structure Stack where
  values : List ValType
  polymorphic : Bool
  deriving DecidableEq

def Stack.push (state : Stack) (type : ValType) : Stack :=
  { state with values := type :: state.values }

def Stack.pushMany (state : Stack) (types : List ValType) : Stack :=
  { state with values := types.reverse ++ state.values }

def bottom (count : Nat) (values : List ValType) : List ValType :=
  values.drop (values.length - count)

def markUnreachable (base : Nat) (state : Stack) : Stack :=
  { values := bottom base state.values, polymorphic := true }

def blockResults : BlockType → List ValType
  | .empty => []
  | .value type => [type]

def PopExpected (base : Nat) (expected : ValType) (start finish : Stack) : Prop :=
  (start.values.length = base ∧ start.polymorphic = true ∧ finish = start) ∨
  ∃ found rest,
    start.values = found :: rest ∧
    start.values.length ≠ base ∧
    found = expected ∧
    finish = { start with values := rest }

def PopAny (base : Nat) (start finish : Stack) : Prop :=
  (start.values.length = base ∧ start.polymorphic = true ∧ finish = start) ∨
  ∃ found rest,
    start.values = found :: rest ∧
    start.values.length ≠ base ∧
    finish = { start with values := rest }

inductive PopSequence (base : Nat) : List ValType → Stack → Stack → Prop
  | nil (state : Stack) : PopSequence base [] state state
  | cons (type : ValType) (types : List ValType) (start middle finish : Stack)
      (head : PopExpected base type start middle)
      (tail : PopSequence base types middle finish) :
      PopSequence base (type :: types) start finish

def PopMany (base : Nat) (types : List ValType) (start finish : Stack) : Prop :=
  PopSequence base types.reverse start finish

def FinishFrame (base : Nat) (outer body finish : Stack)
    (results : List ValType) : Prop :=
  ∃ consumed,
    PopMany base results body consumed ∧
    consumed.values.length = base ∧
    finish = outer.pushMany results

structure Context where
  functions : List FuncType
  locals : UInt32 → Option ValType
  globals : List GlobalType
  labels : List (List ValType)
  results : List ValType
  hasMemory : Bool

inductive UnaryOp : Instr → ValType → ValType → Prop
  | i32Eqz : UnaryOp .i32Eqz .i32 .i32
  | i64Eqz : UnaryOp .i64Eqz .i64 .i32
  | i32WrapI64 : UnaryOp .i32WrapI64 .i64 .i32
  | i64ExtendI32U : UnaryOp .i64ExtendI32U .i32 .i64

inductive BinaryOp : Instr → ValType → ValType → Prop
  | i32Eq : BinaryOp .i32Eq .i32 .i32
  | i32And : BinaryOp .i32And .i32 .i32
  | i64Eq : BinaryOp .i64Eq .i64 .i32
  | i64Ne : BinaryOp .i64Ne .i64 .i32
  | i64LtU : BinaryOp .i64LtU .i64 .i32
  | i64LeU : BinaryOp .i64LeU .i64 .i32
  | i64GeU : BinaryOp .i64GeU .i64 .i32
  | i64Add : BinaryOp .i64Add .i64 .i64
  | i64Sub : BinaryOp .i64Sub .i64 .i64
  | i64Mul : BinaryOp .i64Mul .i64 .i64
  | i64DivU : BinaryOp .i64DivU .i64 .i64
  | i64RemU : BinaryOp .i64RemU .i64 .i64
  | i64And : BinaryOp .i64And .i64 .i64
  | i64Or : BinaryOp .i64Or .i64 .i64
  | i64Xor : BinaryOp .i64Xor .i64 .i64
  | i64Shl : BinaryOp .i64Shl .i64 .i64
  | i64ShrU : BinaryOp .i64ShrU .i64 .i64

mutual
  inductive InstrValid : Context → Nat → Stack → Instr → Stack → Prop
    | unreachable (state : Stack) :
        InstrValid context base state .unreachable (markUnreachable base state)
    | drop (start finish : Stack) (effect : PopAny base start finish) :
        InstrValid context base start .drop finish
    | block (type : BlockType) (body : List Instr) (start bodyFinish finish : Stack)
        (bodyValid : InstrsValid
          { context with labels := blockResults type :: context.labels }
          start.values.length start body bodyFinish)
        (frameValid : FinishFrame start.values.length start bodyFinish finish
          (blockResults type)) :
        InstrValid context base start (.block type body) finish
    | loop (type : BlockType) (body : List Instr) (start bodyFinish finish : Stack)
        (bodyValid : InstrsValid { context with labels := [] :: context.labels }
          start.values.length start body bodyFinish)
        (frameValid : FinishFrame start.values.length start bodyFinish finish
          (blockResults type)) :
        InstrValid context base start (.loop type body) finish
    | iffNone (type : BlockType) (thenBody : List Instr)
        (start outer thenFinish finish : Stack)
        (condition : PopExpected base .i32 start outer)
        (thenValid : InstrsValid
          { context with labels := blockResults type :: context.labels }
          outer.values.length outer thenBody thenFinish)
        (thenFrame : FinishFrame outer.values.length outer thenFinish finish
          (blockResults type))
        (elseFrame : FinishFrame outer.values.length outer outer finish
          (blockResults type)) :
        InstrValid context base start (.iff type thenBody none) finish
    | iffSome (type : BlockType) (thenBody elseBody : List Instr)
        (start outer thenFinish elseFinish finish : Stack)
        (condition : PopExpected base .i32 start outer)
        (thenValid : InstrsValid
          { context with labels := blockResults type :: context.labels }
          outer.values.length outer thenBody thenFinish)
        (elseValid : InstrsValid
          { context with labels := blockResults type :: context.labels }
          outer.values.length outer elseBody elseFinish)
        (thenFrame : FinishFrame outer.values.length outer thenFinish finish
          (blockResults type))
        (elseFrame : FinishFrame outer.values.length outer elseFinish finish
          (blockResults type)) :
        InstrValid context base start (.iff type thenBody (some elseBody)) finish
    | br (depth : UInt32) (types : List ValType) (start popped : Stack)
        (label : context.labels[depth.toNat]? = some types)
        (operands : PopMany base types start popped) :
        InstrValid context base start (.br depth) (markUnreachable base popped)
    | brIf (depth : UInt32) (types : List ValType) (start afterCondition popped : Stack)
        (condition : PopExpected base .i32 start afterCondition)
        (label : context.labels[depth.toNat]? = some types)
        (operands : PopMany base types afterCondition popped) :
        InstrValid context base start (.brIf depth) (popped.pushMany types)
    | ret (start popped : Stack)
        (operands : PopMany base context.results start popped) :
        InstrValid context base start .ret (markUnreachable base popped)
    | call (index : UInt32) (type : FuncType) (start popped : Stack)
        (functionType : context.functions[index.toNat]? = some type)
        (operands : PopMany base type.params start popped) :
        InstrValid context base start (.call index) (popped.pushMany type.results)
    | localGet (index : UInt32) (type : ValType) (state : Stack)
        (localType : context.locals index = some type) :
        InstrValid context base state (.localGet index) (state.push type)
    | localSet (index : UInt32) (type : ValType) (start finish : Stack)
        (localType : context.locals index = some type)
        (effect : PopExpected base type start finish) :
        InstrValid context base start (.localSet index) finish
    | localTee (index : UInt32) (type : ValType) (start popped : Stack)
        (localType : context.locals index = some type)
        (effect : PopExpected base type start popped) :
        InstrValid context base start (.localTee index) (popped.push type)
    | globalGet (index : UInt32) (type : GlobalType) (state : Stack)
        (global : context.globals[index.toNat]? = some type) :
        InstrValid context base state (.globalGet index) (state.push type.type)
    | globalSet (index : UInt32) (type : GlobalType) (start finish : Stack)
        (global : context.globals[index.toNat]? = some type)
        (mutable : type.mutability = .mutable)
        (effect : PopExpected base type.type start finish) :
        InstrValid context base start (.globalSet index) finish
    | i32Const (value : Int) (state : Stack)
        (range : -(2 : Int) ^ 31 ≤ value ∧ value < (2 : Int) ^ 31) :
        InstrValid context base state (.i32Const value) (state.push .i32)
    | i64Const (value : Int) (state : Stack)
        (range : -(2 : Int) ^ 63 ≤ value ∧ value < (2 : Int) ^ 63) :
        InstrValid context base state (.i64Const value) (state.push .i64)
    | unary (instr : Instr) (input output : ValType) (start popped : Stack)
        (operation : UnaryOp instr input output)
        (effect : PopExpected base input start popped) :
        InstrValid context base start instr (popped.push output)
    | binary (instr : Instr) (input output : ValType)
        (start firstPop secondPop : Stack)
        (operation : BinaryOp instr input output)
        (first : PopExpected base input start firstPop)
        (second : PopExpected base input firstPop secondPop) :
        InstrValid context base start instr (secondPop.push output)
    | load (instr : Instr) (arg : MemArg) (input output : ValType)
        (maximum : UInt32) (start popped : Stack)
        (shape : (instr, input, output, maximum) =
          (.i64Load arg, .i32, .i64, 3) ∨
          (instr, input, output, maximum) = (.i32Load arg, .i32, .i32, 2) ∨
          (instr, input, output, maximum) = (.i32Load8U arg, .i32, .i32, 0))
        (memory : context.hasMemory = true)
        (alignment : arg.align ≤ maximum)
        (address : PopExpected base input start popped) :
        InstrValid context base start instr (popped.push output)
    | store (instr : Instr) (arg : MemArg) (valueType : ValType)
        (maximum : UInt32) (start valuePopped addressPopped : Stack)
        (shape : (instr, valueType, maximum) = (.i64Store arg, .i64, 3) ∨
          (instr, valueType, maximum) = (.i32Store arg, .i32, 2) ∨
          (instr, valueType, maximum) = (.i32Store8 arg, .i32, 0))
        (memory : context.hasMemory = true)
        (alignment : arg.align ≤ maximum)
        (value : PopExpected base valueType start valuePopped)
        (address : PopExpected base .i32 valuePopped addressPopped) :
        InstrValid context base start instr addressPopped
    | memorySize (memory : UInt32) (state : Stack)
        (present : context.hasMemory = true) (zero : memory = 0) :
        InstrValid context base state (.memorySize memory) (state.push .i32)
    | memoryGrow (memory : UInt32) (start popped : Stack)
        (present : context.hasMemory = true) (zero : memory = 0)
        (pages : PopExpected base .i32 start popped) :
        InstrValid context base start (.memoryGrow memory) (popped.push .i32)

  inductive InstrsValid : Context → Nat → Stack → List Instr → Stack → Prop
    | nil (state : Stack) : InstrsValid context base state [] state
    | cons (start middle finish : Stack) (head : Instr) (tail : List Instr)
        (headValid : InstrValid context base start head middle)
        (tailValid : InstrsValid context base middle tail finish) :
        InstrsValid context base start (head :: tail) finish
end

def localDeclType : List LocalDecl → Nat → Option ValType
  | [], _ => none
  | decl :: rest, index =>
      if index < decl.count.toNat then some decl.type
      else localDeclType rest (index - decl.count.toNat)

def localType (params : List ValType) (locals : List LocalDecl)
    (index : UInt32) : Option ValType :=
  if index.toNat < params.length then params[index.toNat]?
  else localDeclType locals (index.toNat - params.length)

def RequiredSections (module_ : RawModule) : Prop :=
  (module_.types ≠ [] → .type ∈ module_.sections) ∧
  (module_.functionTypeIndices ≠ [] → .function ∈ module_.sections) ∧
  (module_.memories ≠ [] → .memory ∈ module_.sections) ∧
  (module_.globals ≠ [] → .global ∈ module_.sections) ∧
  (module_.exports ≠ [] → .export ∈ module_.sections) ∧
  (module_.codes ≠ [] → .code ∈ module_.sections)

def SectionsValid (module_ : RawModule) : Prop :=
  Grammar.OrderedAfter 0 module_.sections ∧ RequiredSections module_

def LimitsValid (limits : Limits) : Prop :=
  limits.min.toNat ≤ 65536 ∧
  ∀ maximum ∈ limits.max, limits.min ≤ maximum ∧ maximum.toNat ≤ 65536

def ConstType : ConstExpr → ValType
  | .i32Const _ => .i32
  | .i64Const _ => .i64

def ConstInRange : ConstExpr → Prop
  | .i32Const value => -(2 : Int) ^ 31 ≤ value ∧ value < (2 : Int) ^ 31
  | .i64Const value => -(2 : Int) ^ 63 ≤ value ∧ value < (2 : Int) ^ 63

def GlobalValid (global : Global) : Prop :=
  ConstType global.init = global.type.type ∧ ConstInRange global.init

def GlobalsValid (globals : List Global) : Prop :=
  ∀ global, global ∈ globals → GlobalValid global

def ExportValid (module_ : RawModule) (entry : Export) : Prop :=
  entry.name.text.toByteArray.data.toList = entry.name.bytes ∧
  match entry.desc with
  | .func index => index.toNat < module_.functionTypeIndices.length
  | .memory index => index.toNat < module_.memories.length
  | .global index => index.toNat < module_.globals.length

def ExportNamesUnique (exports : List Export) : Prop :=
  exports.Pairwise fun first second => first.name.bytes ≠ second.name.bytes

def ExportsValid (module_ : RawModule) : Prop :=
  ExportNamesUnique module_.exports ∧
  ∀ entry, entry ∈ module_.exports → ExportValid module_ entry

inductive ResolvedTypes (types : List FuncType) :
    List UInt32 → List FuncType → Prop
  | nil : ResolvedTypes types [] []
  | cons (index : UInt32) (type : FuncType) (indices : List UInt32)
      (resolved : List FuncType) (lookup : types[index.toNat]? = some type)
      (tail : ResolvedTypes types indices resolved) :
      ResolvedTypes types (index :: indices) (type :: resolved)

def FunctionValid (module_ : RawModule) (functions : List FuncType)
    (type : FuncType) (code : Code) : Prop :=
  let context : Context :=
    { functions
      locals := localType type.params code.locals
      globals := module_.globals.map (·.type)
      labels := [type.results]
      results := type.results
      hasMemory := module_.memories.length = 1 }
  let initial : Stack := { values := [], polymorphic := false }
  ∃ state finish,
    InstrsValid context 0 initial code.body state ∧
    FinishFrame 0 initial state finish type.results

inductive FunctionPairsValid (module_ : RawModule) (functions : List FuncType) :
    List FuncType → List Code → Prop
  | nil : FunctionPairsValid module_ functions [] []
  | cons (type : FuncType) (code : Code) (types : List FuncType) (codes : List Code)
      (head : FunctionValid module_ functions type code)
      (tail : FunctionPairsValid module_ functions types codes) :
      FunctionPairsValid module_ functions (type :: types) (code :: codes)

def FunctionsValid (module_ : RawModule) : Prop :=
  ∃ functions,
    ResolvedTypes module_.types module_.functionTypeIndices functions ∧
    FunctionPairsValid module_ functions functions module_.codes

def ModuleValid (module_ : RawModule) : Prop :=
  SectionsValid module_ ∧
  (∃ memory, module_.memories = [memory] ∧ LimitsValid memory.limits) ∧
  GlobalsValid module_.globals ∧
  ExportsValid module_ ∧
  FunctionsValid module_

end Wasm.Binary.Validity

namespace Wasm.Binary

def CoreValid : RawModule → Prop :=
  Validity.ModuleValid

end Wasm.Binary
