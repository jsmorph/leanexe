import Project.Encoding.Spec.Values
import Interpreter.Wasm.Syntax

namespace Wasm.Encoding.Spec

inductive ValType : Bytes → Wasm.ValueType → Prop
  | i32 : ValType [0x7f] .i32
  | i64 : ValType [0x7e] .i64
  | f32 : ValType [0x7d] .f32
  | f64 : ValType [0x7c] .f64

inductive BlockType : Bytes → List Wasm.ValueType → Prop
  | empty : BlockType [0x40] []
  | value (bytes : Bytes) (type : Wasm.ValueType) (encoding : ValType bytes type) :
      BlockType bytes [type]

inductive FuncType : Bytes → Wasm.FuncType → Prop
  | intro (paramBytes resultBytes : Bytes) (params results : List Wasm.ValueType)
      (parameters : Vector ValType paramBytes params)
      (returns : Vector ValType resultBytes results) :
      FuncType (0x60 :: (paramBytes ++ resultBytes)) { params, results }

inductive Limits : Bytes → UInt32 → Option UInt32 → Prop
  | min (bytes : Bytes) (minimum : UInt32)
      (encoding : Unsigned 32 bytes minimum.toNat) :
      Limits (0 :: bytes) minimum none
  | minMax (minBytes maxBytes : Bytes) (minimum maximum : UInt32)
      (minEncoding : Unsigned 32 minBytes minimum.toNat)
      (maxEncoding : Unsigned 32 maxBytes maximum.toNat) :
      Limits (1 :: (minBytes ++ maxBytes)) minimum (some maximum)

inductive Memory : Bytes → Wasm.MemDecl → Prop
  | intro (bytes : Bytes) (minimum : UInt32) (maximum : Option UInt32)
      (encoding : Limits bytes minimum maximum) :
      Memory bytes { pagesMin := minimum, pagesMax := maximum }

inductive Mutability : Bytes → Bool → Prop
  | immutable : Mutability [0] false
  | mutable : Mutability [1] true

inductive Global : Bytes → Wasm.GlobalDecl → Prop
  | i32 (mutBytes valueBytes : Bytes) (mutable : Bool) (value : UInt32)
      (mutability : Mutability mutBytes mutable)
      (constant : Signed 32 valueBytes value.toBitVec.toInt) :
      Global (0x7f :: (mutBytes ++ 0x41 :: valueBytes ++ [0x0b]))
        { init := .i32 value, declaredType := some .i32, isMut := mutable,
          sourceInit := some [.const value] }
  | i64 (mutBytes valueBytes : Bytes) (mutable : Bool) (value : UInt64)
      (mutability : Mutability mutBytes mutable)
      (constant : Signed 64 valueBytes value.toBitVec.toInt) :
      Global (0x7e :: (mutBytes ++ 0x42 :: valueBytes ++ [0x0b]))
        { init := .i64 value, declaredType := some .i64, isMut := mutable,
          sourceInit := some [.constI64 value] }

end Wasm.Encoding.Spec

namespace Wasm.Encoding

def Numeric (type : Wasm.ValueType) : Prop :=
  type = .i32 ∨ type = .i64 ∨ type = .f32 ∨ type = .f64

inductive BlockForm : List Wasm.ValueType → Prop
  | empty : BlockForm []
  | value (type : Wasm.ValueType) (numeric : Numeric type) : BlockForm [type]

inductive GlobalReady : Wasm.GlobalDecl → Prop
  | i32 (value : UInt32) (mutable : Bool) :
      GlobalReady { init := .i32 value, declaredType := some .i32, isMut := mutable,
                    sourceInit := some [.const value] }
  | i64 (value : UInt64) (mutable : Bool) :
      GlobalReady { init := .i64 value, declaredType := some .i64, isMut := mutable,
                    sourceInit := some [.constI64 value] }

end Wasm.Encoding
