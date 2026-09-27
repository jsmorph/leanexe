import Project.Encoding.Containers
import Project.Encoding.Spec.Types
import Init.Data.BitVec.Lemmas

namespace Wasm.Encoding

def valueType : (type : Wasm.ValueType) → Result Spec.ValType type
  | .i32 => .ok ⟨[0x7f], .i32⟩
  | .i64 => .ok ⟨[0x7e], .i64⟩
  | .f32 => .ok ⟨[0x7d], .f32⟩
  | .f64 => .ok ⟨[0x7c], .f64⟩
  | _ => .error "value type is outside LeanExe's emitted WASM"

def blockType : (types : List Wasm.ValueType) → Result Spec.BlockType types
  | [] => .ok ⟨[0x40], .empty⟩
  | [type] => do
      let encoded ← valueType type
      pure ⟨encoded.val, .value _ _ encoded.property⟩
  | _ => .error "block result types are outside LeanExe's emitted WASM"

def functionType (type : Wasm.FuncType) : Result Spec.FuncType type := do
  let parameters ← vector valueType type.params
  let results ← vector valueType type.results
  pure ⟨0x60 :: (parameters.val ++ results.val),
    .intro _ _ _ _ parameters.property results.property⟩

def limits (minimum : UInt32) : (maximum : Option UInt32) →
    Except String { bytes : Spec.Bytes // Spec.Limits bytes minimum maximum }
  | none => do
      let lower ← u32 minimum.toNat
      pure ⟨0 :: lower.val, .min _ _ lower.property⟩
  | some maximum => do
      let lower ← u32 minimum.toNat
      let upper ← u32 maximum.toNat
      pure ⟨1 :: (lower.val ++ upper.val), .minMax _ _ _ _ lower.property upper.property⟩

def memory : (decl : Wasm.MemDecl) → Result Spec.Memory decl
  | { pagesMin := minimum, pagesMax := maximum, data := [], is64 := false } => do
      let encoded ← limits minimum maximum
      pure ⟨encoded.val, .intro _ _ _ encoded.property⟩
  | _ => .error "memory declaration is outside LeanExe's emitted WASM"

def mutability : (mutable : Bool) → Encoded Spec.Mutability mutable
  | false => ⟨[0], .immutable⟩
  | true => ⟨[1], .mutable⟩

def signed32 (value : UInt32) : Encoded (Spec.Signed 32) value.toBitVec.toInt :=
  ⟨signed 32 value.toBitVec.toInt,
    signed_correct 32 _ (by decide) (BitVec.le_toInt _) BitVec.toInt_lt⟩

def signed64 (value : UInt64) : Encoded (Spec.Signed 64) value.toBitVec.toInt :=
  ⟨signed 64 value.toBitVec.toInt,
    signed_correct 64 _ (by decide) (BitVec.le_toInt _) BitVec.toInt_lt⟩

def global : (decl : Wasm.GlobalDecl) → Result Spec.Global decl
  | { init := .i32 value, declaredType := some .i32, isMut := mutable,
      sourceInit := some [.const initial], initExpr := [] } =>
      if same : initial = value then
        let encoded := signed32 value
        let mutBytes := mutability mutable
        .ok ⟨0x7f :: (mutBytes.val ++ 0x41 :: encoded.val ++ [0x0b]), by
          subst initial
          exact .i32 _ _ _ _ mutBytes.property encoded.property⟩
      else .error "global initializer disagrees with its represented value"
  | { init := .i64 value, declaredType := some .i64, isMut := mutable,
      sourceInit := some [.constI64 initial], initExpr := [] } =>
      if same : initial = value then
        let encoded := signed64 value
        let mutBytes := mutability mutable
        .ok ⟨0x7e :: (mutBytes.val ++ 0x42 :: encoded.val ++ [0x0b]), by
          subst initial
          exact .i64 _ _ _ _ mutBytes.property encoded.property⟩
      else .error "global initializer disagrees with its represented value"
  | _ => .error "global declaration is outside LeanExe's emitted WASM"

end Wasm.Encoding
