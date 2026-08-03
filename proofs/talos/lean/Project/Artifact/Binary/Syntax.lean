namespace Wasm.Binary

inductive SectionId where
  | type
  | function
  | memory
  | global
  | export
  | code
  deriving Repr, Inhabited, DecidableEq

def SectionId.byte : SectionId → UInt8
  | .type => 1
  | .function => 3
  | .memory => 5
  | .global => 6
  | .export => 7
  | .code => 10

def SectionId.rank : SectionId → Nat
  | .type => 1
  | .function => 2
  | .memory => 3
  | .global => 4
  | .export => 5
  | .code => 6

inductive ValType where
  | i32
  | i64
  deriving Repr, Inhabited, DecidableEq

structure FuncType where
  params : List ValType
  results : List ValType
  deriving Repr, Inhabited, DecidableEq

inductive Mutability where
  | immutable
  | mutable
  deriving Repr, Inhabited, DecidableEq

structure Limits where
  min : UInt32
  max : Option UInt32
  deriving Repr, Inhabited, DecidableEq

structure MemoryType where
  limits : Limits
  deriving Repr, Inhabited, DecidableEq

structure GlobalType where
  type : ValType
  mutability : Mutability
  deriving Repr, Inhabited, DecidableEq

inductive ConstExpr where
  | i32Const (value : Int)
  | i64Const (value : Int)
  deriving Repr, Inhabited, DecidableEq

structure Global where
  type : GlobalType
  init : ConstExpr
  deriving Repr, Inhabited, DecidableEq

inductive BlockType where
  | empty
  | value (type : ValType)
  deriving Repr, Inhabited, DecidableEq

structure MemArg where
  align : UInt32
  offset : UInt32
  deriving Repr, Inhabited, DecidableEq

inductive Instr where
  | unreachable
  | drop
  | block (type : BlockType) (body : List Instr)
  | loop (type : BlockType) (body : List Instr)
  | iff (type : BlockType) (thenBody : List Instr) (elseBody : Option (List Instr))
  | br (depth : UInt32)
  | brIf (depth : UInt32)
  | ret
  | call (index : UInt32)
  | localGet (index : UInt32)
  | localSet (index : UInt32)
  | localTee (index : UInt32)
  | globalGet (index : UInt32)
  | globalSet (index : UInt32)
  | i32Const (value : Int)
  | i64Const (value : Int)
  | i32Eqz
  | i32Eq
  | i32And
  | i64Eqz
  | i64Eq
  | i64Ne
  | i64LtU
  | i64LeU
  | i64GeU
  | i64Add
  | i64Sub
  | i64Mul
  | i64DivU
  | i64RemU
  | i64And
  | i64Or
  | i64Xor
  | i64Shl
  | i64ShrU
  | i32WrapI64
  | i64ExtendI32U
  | i64Load (arg : MemArg)
  | i32Load (arg : MemArg)
  | i32Load8U (arg : MemArg)
  | i64Store (arg : MemArg)
  | i32Store (arg : MemArg)
  | i32Store8 (arg : MemArg)
  | memorySize (memory : UInt32)
  | memoryGrow (memory : UInt32)
  deriving Repr, Inhabited, BEq

structure LocalDecl where
  count : UInt32
  type : ValType
  deriving Repr, Inhabited, DecidableEq

structure Code where
  locals : List LocalDecl
  body : List Instr
  deriving Repr, Inhabited, BEq

structure Name where
  bytes : List UInt8
  text : String
  deriving Repr, Inhabited, DecidableEq

inductive ExportDesc where
  | func (index : UInt32)
  | memory (index : UInt32)
  | global (index : UInt32)
  deriving Repr, Inhabited, DecidableEq

structure Export where
  name : Name
  desc : ExportDesc
  deriving Repr, Inhabited, DecidableEq

structure RawModule where
  sections : List SectionId
  types : List FuncType
  functionTypeIndices : List UInt32
  memories : List MemoryType
  globals : List Global
  exports : List Export
  codes : List Code
  deriving Repr, Inhabited, BEq

end Wasm.Binary
