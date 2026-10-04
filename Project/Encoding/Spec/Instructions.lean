import Project.Encoding.Spec.Types

namespace Wasm.Encoding.Spec

inductive Plain : Bytes → Wasm.Instruction → Prop
  | unreachable : Plain [0x00] .unreachable
  | nop : Plain [0x01] .nop
  | ret : Plain [0x0f] .ret
  | drop : Plain [0x1a] .drop
  | eqz : Plain [0x45] .eqz
  | eq : Plain [0x46] .eq
  | ltU : Plain [0x49] .ltU
  | gtU : Plain [0x4b] .gtU
  | leU : Plain [0x4d] .leU
  | geU : Plain [0x4f] .geU
  | eqzI64 : Plain [0x50] .eqzI64
  | eqI64 : Plain [0x51] .eqI64
  | neI64 : Plain [0x52] .neI64
  | ltUI64 : Plain [0x54] .ltUI64
  | leUI64 : Plain [0x58] .leUI64
  | f64Eq : Plain [0x61] .f64Eq
  | f64Lt : Plain [0x63] .f64Lt
  | f64Le : Plain [0x65] .f64Le
  | f64Abs : Plain [0x99] .f64Abs
  | f64ConvertI64U : Plain [0xba] .f64ConvertI64U
  | geUI64 : Plain [0x5a] .geUI64
  | add : Plain [0x6a] .add
  | and : Plain [0x71] .and
  | addI64 : Plain [0x7c] .addI64
  | subI64 : Plain [0x7d] .subI64
  | mulI64 : Plain [0x7e] .mulI64
  | divUI64 : Plain [0x80] .divUI64
  | remUI64 : Plain [0x82] .remUI64
  | andI64 : Plain [0x83] .andI64
  | orI64 : Plain [0x84] .orI64
  | xorI64 : Plain [0x85] .xorI64
  | shlI64 : Plain [0x86] .shlI64
  | shrUI64 : Plain [0x88] .shrUI64
  | f32Nearest : Plain [0x90] .f32Nearest
  | f32Sqrt : Plain [0x91] .f32Sqrt
  | f32Add : Plain [0x92] .f32Add
  | f32Sub : Plain [0x93] .f32Sub
  | f32Mul : Plain [0x94] .f32Mul
  | f32Div : Plain [0x95] .f32Div
  | f64Sqrt : Plain [0x9f] .f64Sqrt
  | f64Add : Plain [0xa0] .f64Add
  | f64Sub : Plain [0xa1] .f64Sub
  | f64Mul : Plain [0xa2] .f64Mul
  | f64Div : Plain [0xa3] .f64Div
  | wrapI64 : Plain [0xa7] .wrapI64
  | extendUI32 : Plain [0xad] .extendUI32
  | f32ConvertI32S : Plain [0xb2] .f32ConvertI32S
  | f32DemoteF64 : Plain [0xb6] .f32DemoteF64
  | f64PromoteF32 : Plain [0xbb] .f64PromoteF32
  | i32ReinterpretF32 : Plain [0xbc] .i32ReinterpretF32
  | i64ReinterpretF64 : Plain [0xbd] .i64ReinterpretF64
  | f32ReinterpretI32 : Plain [0xbe] .f32ReinterpretI32
  | f64ReinterpretI64 : Plain [0xbf] .f64ReinterpretI64
  | extend8S : Plain [0xc0] .extend8S
  | i32TruncSatF32S : Plain [0xfc, 0x00] .i32TruncSatF32S
  | i64TruncSatF64U : Plain [0xfc, 0x07] .i64TruncSatF64U
  | memorySize : Plain [0x3f, 0x00] .memorySize
  | memoryGrow : Plain [0x40, 0x00] .memoryGrow

inductive IndexOp : UInt8 → (Nat → Wasm.Instruction) → Prop
  | br : IndexOp 0x0c .br
  | br_if : IndexOp 0x0d .br_if
  | call : IndexOp 0x10 .call
  | localGet : IndexOp 0x20 .localGet
  | localSet : IndexOp 0x21 .localSet
  | localTee : IndexOp 0x22 .localTee
  | globalGet : IndexOp 0x23 .globalGet
  | globalSet : IndexOp 0x24 .globalSet

inductive MemoryOp : UInt8 → Nat → (UInt32 → Wasm.Instruction) → Prop
  | load32 : MemoryOp 0x28 2 .load32
  | load64 : MemoryOp 0x29 3 .load64
  | load8U : MemoryOp 0x2d 0 .load8U
  | store32 : MemoryOp 0x36 2 .store32
  | store64 : MemoryOp 0x37 3 .store64
  | store8 : MemoryOp 0x3a 0 .store8

inductive MemArg (maxAlignment : Nat) : Bytes → UInt32 → Prop
  | intro (alignBytes offsetBytes : Bytes) (alignment : Nat) (offset : UInt32)
      (alignEncoding : Unsigned 32 alignBytes alignment)
      (alignBound : alignment ≤ maxAlignment)
      (offsetEncoding : Unsigned 32 offsetBytes offset.toNat) :
      MemArg maxAlignment (alignBytes ++ offsetBytes) offset

/-- A 64-bit word as eight bytes, least significant first. -/
def littleEndian64 (value : UInt64) : Bytes :=
  (List.range 8).map fun i => UInt8.ofNat (value.toNat / 256 ^ i)

/-- A 32-bit word as four bytes, least significant first. -/
def littleEndian32 (value : UInt32) : Bytes :=
  (List.range 4).map fun i => UInt8.ofNat (value.toNat / 256 ^ i)

mutual
  inductive Instr : Bytes → Wasm.Instruction → Prop
    | plain (bytes : Bytes) (instr : Wasm.Instruction) (rule : Plain bytes instr) :
        Instr bytes instr
    | index (opcode : UInt8) (make : Nat → Wasm.Instruction) (index : Nat)
        (bytes : Bytes) (rule : IndexOp opcode make)
        (immediate : Unsigned 32 bytes index) :
        Instr (opcode :: bytes) (make index)
    | memory (opcode : UInt8) (maxAlignment : Nat) (make : UInt32 → Wasm.Instruction)
        (offset : UInt32) (bytes : Bytes) (rule : MemoryOp opcode maxAlignment make)
        (immediate : MemArg maxAlignment bytes offset) :
        Instr (opcode :: bytes) (make offset)
    | const32 (bytes : Bytes) (value : UInt32)
        (immediate : Signed 32 bytes value.toBitVec.toInt) :
        Instr (0x41 :: bytes) (.const value)
    | const64 (bytes : Bytes) (value : UInt64)
        (immediate : Signed 64 bytes value.toBitVec.toInt) :
        Instr (0x42 :: bytes) (.constI64 value)
    | constF64 (value : UInt64) : Instr (0x44 :: littleEndian64 value) (.f64Const value)
    | constF32 (value : UInt32) : Instr (0x43 :: littleEndian32 value) (.f32Const value)
    | block (typeBytes bodyBytes : Bytes) (types : List Wasm.ValueType)
        (body : Wasm.Program) (typeEncoding : BlockType typeBytes types)
        (bodyEncoding : Instrs bodyBytes body) :
        Instr (0x02 :: (typeBytes ++ bodyBytes ++ [0x0b]))
          (.block 0 types.length body [] types)
    | loop (typeBytes bodyBytes : Bytes) (types : List Wasm.ValueType)
        (body : Wasm.Program) (typeEncoding : BlockType typeBytes types)
        (bodyEncoding : Instrs bodyBytes body) :
        Instr (0x03 :: (typeBytes ++ bodyBytes ++ [0x0b]))
          (.loop 0 types.length body [] types)
    | iff (typeBytes thenBytes elseBytes : Bytes) (types : List Wasm.ValueType)
        (thenBody elseBody : Wasm.Program) (typeEncoding : BlockType typeBytes types)
        (thenEncoding : Instrs thenBytes thenBody) (elseEncoding : Instrs elseBytes elseBody) :
        Instr (0x04 :: (typeBytes ++ thenBytes ++ 0x05 :: elseBytes ++ [0x0b]))
          (.iff 0 types.length thenBody elseBody [] types)

  inductive Instrs : Bytes → Wasm.Program → Prop
    | nil : Instrs [] []
    | cons (headBytes tailBytes : Bytes) (head : Wasm.Instruction) (tail : Wasm.Program)
        (headEncoding : Instr headBytes head) (tailEncoding : Instrs tailBytes tail) :
        Instrs (headBytes ++ tailBytes) (head :: tail)
end

end Wasm.Encoding.Spec
