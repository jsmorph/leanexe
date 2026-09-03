import Init.Data.String.Basic
import Project.Artifact.Binary.Syntax

namespace Wasm.Binary.Grammar

def byte (value : Nat) : UInt8 :=
  UInt8.ofNat value

def unsignedValue : List UInt8 → Nat
  | [] => 0
  | head :: tail => head.toNat % 128 + 128 * unsignedValue tail

def signedValue (bytes : List UInt8) : Int :=
  let value := Int.ofNat (unsignedValue bytes)
  match bytes.getLast? with
  | some last =>
      if last.toNat % 128 < 64 then value
      else value - Int.ofNat (2 ^ (7 * bytes.length))
  | none => 0

def continuationForm : List UInt8 → Prop
  | [] => False
  | [last] => last.toNat < 128
  | head :: tail => 128 ≤ head.toNat ∧ continuationForm tail

def unsignedTerminalFits (width : Nat) (bytes : List UInt8) : Prop :=
  match bytes.getLast? with
  | none => False
  | some last =>
      let shift := 7 * (bytes.length - 1)
      shift < width ∧ last.toNat % 128 < 2 ^ (width - shift)

def signedTerminalFits (width : Nat) (bytes : List UInt8) : Prop :=
  match bytes.getLast? with
  | none => False
  | some last =>
      let shift := 7 * (bytes.length - 1)
      let used := width - shift
      shift < width ∧
        (shift + 7 ≤ width ∨
          last.toNat % 128 < 2 ^ (used - 1) ∨
          128 - 2 ^ (used - 1) ≤ last.toNat % 128)

def U32 (bytes : List UInt8) (value : Nat) : Prop :=
  bytes.length ≤ 5 ∧ continuationForm bytes ∧
    unsignedTerminalFits 32 bytes ∧ unsignedValue bytes = value

def U64 (bytes : List UInt8) (value : Nat) : Prop :=
  bytes.length ≤ 10 ∧ continuationForm bytes ∧
    unsignedTerminalFits 64 bytes ∧ unsignedValue bytes = value

def S32 (bytes : List UInt8) (value : Int) : Prop :=
  bytes.length ≤ 5 ∧ continuationForm bytes ∧
    signedTerminalFits 32 bytes ∧ signedValue bytes = value

def S64 (bytes : List UInt8) (value : Int) : Prop :=
  bytes.length ≤ 10 ∧ continuationForm bytes ∧
    signedTerminalFits 64 bytes ∧ signedValue bytes = value

inductive Items (relation : List UInt8 → α → Prop) : List UInt8 → List α → Prop
  | nil : Items relation [] []
  | cons (headBytes tailBytes : List UInt8) (head : α) (tail : List α)
      (headEncoding : relation headBytes head)
      (tailEncoding : Items relation tailBytes tail) :
      Items relation (headBytes ++ tailBytes) (head :: tail)

inductive Vector (relation : List UInt8 → α → Prop) : List UInt8 → List α → Prop
  | intro (lengthBytes body : List UInt8) (values : List α)
      (lengthEncoding : U32 lengthBytes values.length)
      (bodyEncoding : Items relation body values) :
      Vector relation (lengthBytes ++ body) values

inductive Sized (relation : List UInt8 → α → Prop) : List UInt8 → α → Prop
  | intro (lengthBytes body : List UInt8) (value : α)
      (lengthEncoding : U32 lengthBytes body.length)
      (bodyEncoding : relation body value) :
      Sized relation (lengthBytes ++ body) value

inductive ValType : List UInt8 → Binary.ValType → Prop
  | i32 : ValType [byte 127] .i32
  | i64 : ValType [byte 126] .i64

inductive BlockType : List UInt8 → Binary.BlockType → Prop
  | empty : BlockType [byte 64] .empty
  | i32 : BlockType [byte 127] (.value .i32)
  | i64 : BlockType [byte 126] (.value .i64)

inductive FuncType : List UInt8 → Binary.FuncType → Prop
  | intro (paramBytes resultBytes : List UInt8) (params results : List Binary.ValType)
      (paramsEncoding : Vector ValType paramBytes params)
      (resultsEncoding : Vector ValType resultBytes results) :
      FuncType (byte 96 :: (paramBytes ++ resultBytes)) { params, results }

inductive Limits : List UInt8 → Binary.Limits → Prop
  | min (bytes : List UInt8) (value : UInt32)
      (encoding : U32 bytes value.toNat) :
      Limits (byte 0 :: bytes) { min := value, max := none }
  | minMax (minBytes maxBytes : List UInt8) (min max : UInt32)
      (minEncoding : U32 minBytes min.toNat)
      (maxEncoding : U32 maxBytes max.toNat) :
      Limits (byte 1 :: (minBytes ++ maxBytes)) { min, max := some max }

inductive MemoryType : List UInt8 → Binary.MemoryType → Prop
  | intro (bytes : List UInt8) (limits : Binary.Limits)
      (encoding : Limits bytes limits) :
      MemoryType bytes { limits }

inductive Mutability : List UInt8 → Binary.Mutability → Prop
  | immutable : Mutability [byte 0] .immutable
  | mutable : Mutability [byte 1] .mutable

inductive GlobalType : List UInt8 → Binary.GlobalType → Prop
  | intro (typeBytes mutabilityBytes : List UInt8) (type : Binary.ValType)
      (mutability : Binary.Mutability)
      (typeEncoding : ValType typeBytes type)
      (mutabilityEncoding : Mutability mutabilityBytes mutability) :
      GlobalType (typeBytes ++ mutabilityBytes) { type, mutability }

inductive ConstExpr : List UInt8 → Binary.ConstExpr → Prop
  | i32 (bytes : List UInt8) (value : Int) (encoding : S32 bytes value) :
      ConstExpr (byte 65 :: (bytes ++ [byte 11])) (.i32Const value)
  | i64 (bytes : List UInt8) (value : Int) (encoding : S64 bytes value) :
      ConstExpr (byte 66 :: (bytes ++ [byte 11])) (.i64Const value)

inductive Global : List UInt8 → Binary.Global → Prop
  | intro (typeBytes initBytes : List UInt8) (type : Binary.GlobalType)
      (init : Binary.ConstExpr)
      (typeEncoding : GlobalType typeBytes type)
      (initEncoding : ConstExpr initBytes init) :
      Global (typeBytes ++ initBytes) { type, init }

inductive MemArg : List UInt8 → Binary.MemArg → Prop
  | intro (alignBytes offsetBytes : List UInt8) (align offset : UInt32)
      (alignEncoding : U32 alignBytes align.toNat)
      (offsetEncoding : U32 offsetBytes offset.toNat) :
      MemArg (alignBytes ++ offsetBytes) { align, offset }

mutual
  inductive Instr : List UInt8 → Binary.Instr → Prop
    | unreachable : Instr [byte 0] .unreachable
    | block (typeBytes bodyBytes : List UInt8) (type : Binary.BlockType)
        (body : List Binary.Instr) (typeEncoding : BlockType typeBytes type)
        (bodyEncoding : Instrs bodyBytes body) :
        Instr (byte 2 :: (typeBytes ++ bodyBytes ++ [byte 11])) (.block type body)
    | loop (typeBytes bodyBytes : List UInt8) (type : Binary.BlockType)
        (body : List Binary.Instr) (typeEncoding : BlockType typeBytes type)
        (bodyEncoding : Instrs bodyBytes body) :
        Instr (byte 3 :: (typeBytes ++ bodyBytes ++ [byte 11])) (.loop type body)
    | iffNoElse (typeBytes thenBytes : List UInt8) (type : Binary.BlockType)
        (thenBody : List Binary.Instr) (typeEncoding : BlockType typeBytes type)
        (thenEncoding : Instrs thenBytes thenBody) :
        Instr (byte 4 :: (typeBytes ++ thenBytes ++ [byte 11]))
          (.iff type thenBody none)
    | iffElse (typeBytes thenBytes elseBytes : List UInt8) (type : Binary.BlockType)
        (thenBody elseBody : List Binary.Instr) (typeEncoding : BlockType typeBytes type)
        (thenEncoding : Instrs thenBytes thenBody)
        (elseEncoding : Instrs elseBytes elseBody) :
        Instr (byte 4 :: (typeBytes ++ thenBytes ++ byte 5 :: elseBytes ++ [byte 11]))
          (.iff type thenBody (some elseBody))
    | br (bytes : List UInt8) (depth : UInt32) (encoding : U32 bytes depth.toNat) :
        Instr (byte 12 :: bytes) (.br depth)
    | brIf (bytes : List UInt8) (depth : UInt32) (encoding : U32 bytes depth.toNat) :
        Instr (byte 13 :: bytes) (.brIf depth)
    | ret : Instr [byte 15] .ret
    | call (bytes : List UInt8) (index : UInt32) (encoding : U32 bytes index.toNat) :
        Instr (byte 16 :: bytes) (.call index)
    | drop : Instr [byte 26] .drop
    | localGet (bytes : List UInt8) (index : UInt32) (encoding : U32 bytes index.toNat) :
        Instr (byte 32 :: bytes) (.localGet index)
    | localSet (bytes : List UInt8) (index : UInt32) (encoding : U32 bytes index.toNat) :
        Instr (byte 33 :: bytes) (.localSet index)
    | localTee (bytes : List UInt8) (index : UInt32) (encoding : U32 bytes index.toNat) :
        Instr (byte 34 :: bytes) (.localTee index)
    | globalGet (bytes : List UInt8) (index : UInt32) (encoding : U32 bytes index.toNat) :
        Instr (byte 35 :: bytes) (.globalGet index)
    | globalSet (bytes : List UInt8) (index : UInt32) (encoding : U32 bytes index.toNat) :
        Instr (byte 36 :: bytes) (.globalSet index)
    | i32Load (bytes : List UInt8) (arg : Binary.MemArg) (encoding : MemArg bytes arg) :
        Instr (byte 40 :: bytes) (.i32Load arg)
    | i64Load (bytes : List UInt8) (arg : Binary.MemArg) (encoding : MemArg bytes arg) :
        Instr (byte 41 :: bytes) (.i64Load arg)
    | i32Load8U (bytes : List UInt8) (arg : Binary.MemArg) (encoding : MemArg bytes arg) :
        Instr (byte 45 :: bytes) (.i32Load8U arg)
    | i32Store (bytes : List UInt8) (arg : Binary.MemArg) (encoding : MemArg bytes arg) :
        Instr (byte 54 :: bytes) (.i32Store arg)
    | i64Store (bytes : List UInt8) (arg : Binary.MemArg) (encoding : MemArg bytes arg) :
        Instr (byte 55 :: bytes) (.i64Store arg)
    | i32Store8 (bytes : List UInt8) (arg : Binary.MemArg) (encoding : MemArg bytes arg) :
        Instr (byte 58 :: bytes) (.i32Store8 arg)
    | memorySize (bytes : List UInt8) (memory : UInt32) (encoding : U32 bytes memory.toNat) :
        Instr (byte 63 :: bytes) (.memorySize memory)
    | memoryGrow (bytes : List UInt8) (memory : UInt32) (encoding : U32 bytes memory.toNat) :
        Instr (byte 64 :: bytes) (.memoryGrow memory)
    | i32Const (bytes : List UInt8) (value : Int) (encoding : S32 bytes value) :
        Instr (byte 65 :: bytes) (.i32Const value)
    | i64Const (bytes : List UInt8) (value : Int) (encoding : S64 bytes value) :
        Instr (byte 66 :: bytes) (.i64Const value)
    | i32Eqz : Instr [byte 69] .i32Eqz
    | i32Eq : Instr [byte 70] .i32Eq
    | i64Eqz : Instr [byte 80] .i64Eqz
    | i64Eq : Instr [byte 81] .i64Eq
    | i64Ne : Instr [byte 82] .i64Ne
    | i64LtU : Instr [byte 84] .i64LtU
    | i64LeU : Instr [byte 88] .i64LeU
    | i64GeU : Instr [byte 90] .i64GeU
    | i32And : Instr [byte 113] .i32And
    | i64Add : Instr [byte 124] .i64Add
    | i64Sub : Instr [byte 125] .i64Sub
    | i64Mul : Instr [byte 126] .i64Mul
    | i64DivU : Instr [byte 128] .i64DivU
    | i64RemU : Instr [byte 130] .i64RemU
    | i64And : Instr [byte 131] .i64And
    | i64Or : Instr [byte 132] .i64Or
    | i64Xor : Instr [byte 133] .i64Xor
    | i64Shl : Instr [byte 134] .i64Shl
    | i64ShrU : Instr [byte 136] .i64ShrU
    | f64Add : Instr [byte 160] .f64Add
    | f64Mul : Instr [byte 162] .f64Mul
    | i32WrapI64 : Instr [byte 167] .i32WrapI64
    | i64ExtendI32U : Instr [byte 173] .i64ExtendI32U
    | i64ReinterpretF64 : Instr [byte 189] .i64ReinterpretF64
    | f64ReinterpretI64 : Instr [byte 191] .f64ReinterpretI64

  inductive Instrs : List UInt8 → List Binary.Instr → Prop
    | nil : Instrs [] []
    | cons (headBytes tailBytes : List UInt8) (head : Binary.Instr)
        (tail : List Binary.Instr) (headEncoding : Instr headBytes head)
        (tailEncoding : Instrs tailBytes tail) :
        Instrs (headBytes ++ tailBytes) (head :: tail)
end

inductive LocalDecl : List UInt8 → Binary.LocalDecl → Prop
  | intro (countBytes typeBytes : List UInt8) (count : UInt32) (type : Binary.ValType)
      (countEncoding : U32 countBytes count.toNat)
      (typeEncoding : ValType typeBytes type) :
      LocalDecl (countBytes ++ typeBytes) { count, type }

inductive CodeBody : List UInt8 → Binary.Code → Prop
  | intro (localBytes instructionBytes : List UInt8) (locals : List Binary.LocalDecl)
      (body : List Binary.Instr) (localEncoding : Vector LocalDecl localBytes locals)
      (bodyEncoding : Instrs instructionBytes body) :
      CodeBody (localBytes ++ instructionBytes ++ [byte 11]) { locals, body }

def Code : List UInt8 → Binary.Code → Prop :=
  Sized CodeBody

inductive Name : List UInt8 → Binary.Name → Prop
  | intro (lengthBytes bytes : List UInt8) (text : String)
      (lengthEncoding : U32 lengthBytes bytes.length)
      (textEncoding : String.fromUTF8? bytes.toByteArray = some text) :
      Name (lengthBytes ++ bytes) { bytes, text }

inductive ExportDesc : List UInt8 → Binary.ExportDesc → Prop
  | func (bytes : List UInt8) (index : UInt32) (encoding : U32 bytes index.toNat) :
      ExportDesc (byte 0 :: bytes) (.func index)
  | memory (bytes : List UInt8) (index : UInt32) (encoding : U32 bytes index.toNat) :
      ExportDesc (byte 2 :: bytes) (.memory index)
  | global (bytes : List UInt8) (index : UInt32) (encoding : U32 bytes index.toNat) :
      ExportDesc (byte 3 :: bytes) (.global index)

inductive Export : List UInt8 → Binary.Export → Prop
  | intro (nameBytes descBytes : List UInt8) (name : Binary.Name)
      (desc : Binary.ExportDesc) (nameEncoding : Name nameBytes name)
      (descEncoding : ExportDesc descBytes desc) :
      Export (nameBytes ++ descBytes) { name, desc }

inductive Section (module_ : Binary.RawModule) : List UInt8 → Binary.SectionId → Prop
  | type (bytes : List UInt8)
      (encoding : Sized (Vector FuncType) bytes module_.types) :
      Section module_ (byte 1 :: bytes) .type
  | function (bytes : List UInt8)
      (encoding : Sized (Vector fun bs index => U32 bs index.toNat)
        bytes module_.functionTypeIndices) :
      Section module_ (byte 3 :: bytes) .function
  | memory (bytes : List UInt8)
      (encoding : Sized (Vector MemoryType) bytes module_.memories) :
      Section module_ (byte 5 :: bytes) .memory
  | global (bytes : List UInt8)
      (encoding : Sized (Vector Global) bytes module_.globals) :
      Section module_ (byte 6 :: bytes) .global
  | export (bytes : List UInt8)
      (encoding : Sized (Vector Export) bytes module_.exports) :
      Section module_ (byte 7 :: bytes) .export
  | code (bytes : List UInt8)
      (encoding : Sized (Vector Code) bytes module_.codes) :
      Section module_ (byte 10 :: bytes) .code

inductive Sections (module_ : Binary.RawModule) : List UInt8 → List Binary.SectionId → Prop
  | nil : Sections module_ [] []
  | cons (headBytes tailBytes : List UInt8) (head : Binary.SectionId)
      (tail : List Binary.SectionId) (headEncoding : Section module_ headBytes head)
      (tailEncoding : Sections module_ tailBytes tail) :
      Sections module_ (headBytes ++ tailBytes) (head :: tail)

inductive OrderedAfter : Nat → List Binary.SectionId → Prop
  | nil (lastRank : Nat) : OrderedAfter lastRank []
  | cons (lastRank : Nat) (head : Binary.SectionId) (tail : List Binary.SectionId)
      (rankIncreases : lastRank < head.rank)
      (tailOrdered : OrderedAfter head.rank tail) :
      OrderedAfter lastRank (head :: tail)

def AbsentFieldsEmpty (module_ : Binary.RawModule) : Prop :=
  (.type ∈ module_.sections ∨ module_.types = []) ∧
  (.function ∈ module_.sections ∨ module_.functionTypeIndices = []) ∧
  (.memory ∈ module_.sections ∨ module_.memories = []) ∧
  (.global ∈ module_.sections ∨ module_.globals = []) ∧
  (.export ∈ module_.sections ∨ module_.exports = []) ∧
  (.code ∈ module_.sections ∨ module_.codes = [])

def ModuleBytes (bytes : List UInt8) (module_ : Binary.RawModule) : Prop :=
  ∃ sectionBytes,
    bytes = [byte 0, byte 97, byte 115, byte 109, byte 1, byte 0, byte 0, byte 0] ++
      sectionBytes ∧
    Sections module_ sectionBytes module_.sections ∧
    OrderedAfter 0 module_.sections ∧
    AbsentFieldsEmpty module_

def Encodes (bytes : ByteArray) (module_ : Binary.RawModule) : Prop :=
  ModuleBytes bytes.data.toList module_

end Wasm.Binary.Grammar
