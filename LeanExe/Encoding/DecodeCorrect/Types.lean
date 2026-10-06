import LeanExe.Encoding.DecodeCorrect.Basic
import LeanExe.Encoding.Spec.Modules

namespace Wasm.Encoding.Decoder

open Wasm.Encoding.Spec

theorem parses_many_map {item : Parser β} {relation : List UInt8 → α → Prop} {g : α → β}
    (hItem : ∀ bytes value, relation bytes value → Parses item bytes (g value))
    {bytes : List UInt8} {values : List α} (h : Items relation bytes values) :
    Parses (many item values.length) bytes (values.map g) := by
  induction h with
  | nil => exact Parses.pure' _
  | cons headBytes tailBytes head tail headEncoding tailEncoding ih =>
      rw [List.length_cons, many, List.map_cons]
      exact Parses.bind (hItem _ _ headEncoding) (Parses.bind_nil ih (Parses.pure' _))

/-- `vec item` reads a vector whose items the relation describes, returning the
items' images under `g`. -/
theorem parses_vec_map {item : Parser β} {relation : List UInt8 → α → Prop} {g : α → β}
    (hItem : ∀ bytes value, relation bytes value → Parses item bytes (g value))
    (hNonempty : ∀ bytes value, relation bytes value → bytes ≠ [])
    {bytes : List UInt8} {values : List α} (h : Vector relation bytes values) :
    Parses (vec item) bytes (values.map g) := by
  cases h with
  | intro countBytes body values count items =>
      intro rest
      have hLength := items_length_le hNonempty items
      have hNot : ¬ (body ++ rest).length < values.length := by
        simp only [List.length_append]
        omega
      show StateT.run (vec item) (countBytes ++ body ++ rest) = _
      unfold vec
      rw [StateT.run_bind, List.append_assoc,
        parses_unsigned count 32 (Nat.le_refl _) (body ++ rest)]
      show StateT.run (remaining >>= fun available =>
        if available < values.length then malformed "unexpected end"
        else many item values.length) (body ++ rest) = _
      rw [StateT.run_bind]
      show StateT.run (if (body ++ rest).length < values.length then malformed "unexpected end"
        else many item values.length) (body ++ rest) = _
      rw [ite_eq_right hNot]
      exact parses_many_map hItem items rest

theorem vector_length_lt {relation : List UInt8 → α → Prop} {bytes : List UInt8}
    {values : List α} (h : Vector relation bytes values) : values.length < 2 ^ 32 := by
  cases h with
  | intro countBytes body values count items => exact unsigned_lt count

theorem vector_nonempty {relation : List UInt8 → α → Prop} {bytes : List UInt8}
    {values : List α} (h : Vector relation bytes values) : bytes ≠ [] := by
  cases h with
  | intro countBytes body values count items =>
      have := unsigned_nonempty count
      cases countBytes with
      | nil => exact absurd rfl this
      | cons _ _ => simp

theorem name_nonempty {bytes : List UInt8} {value : String} (h : Name bytes value) :
    bytes ≠ [] := by
  cases h with
  | intro countBytes value count =>
      have := unsigned_nonempty count
      cases countBytes with
      | nil => exact absurd rfl this
      | cons _ _ => simp

theorem parses_valueType {bytes : List UInt8} {type : ValueType} (h : ValType bytes type) :
    Parses valueType bytes type := by
  cases h <;> exact Parses.bind_nil (parses_byte _) (Parses.pure' _)

theorem valType_nonempty {bytes : List UInt8} {type : ValueType} (h : ValType bytes type) :
    bytes ≠ [] := by
  cases h <;> simp

theorem parses_blockType {bytes : List UInt8} {types : List ValueType}
    (h : BlockType bytes types) : Parses blockType bytes types := by
  cases h with
  | empty => exact Parses.bind_nil (parses_byte _) (Parses.pure' _)
  | value bytes type encoding =>
      cases encoding <;> exact Parses.bind_nil (parses_byte _) (Parses.pure' _)

theorem parses_funcType {bytes : List UInt8} {type : Wasm.FuncType}
    (h : Spec.FuncType bytes type) : Parses funcType bytes type := by
  match h with
  | .intro paramBytes resultBytes params results parameters returns =>
      have hParams := parses_vec_map (g := id) (fun _ _ h => parses_valueType h)
        (fun _ _ h => valType_nonempty h) parameters
      have hResults := parses_vec_map (g := id) (fun _ _ h => parses_valueType h)
        (fun _ _ h => valType_nonempty h) returns
      simp only [List.map_id] at hParams hResults
      unfold funcType
      refine Parses.bind (parses_byte 0x60) ?_
      show Parses (do
          let params ← vec valueType
          let results ← vec valueType
          pure ({ params := params, results := results } : Wasm.FuncType))
        (paramBytes ++ resultBytes) { params := params, results := results }
      exact Parses.bind hParams (Parses.bind_nil hResults (Parses.pure' _))

theorem funcType_nonempty {bytes : List UInt8} {type : Wasm.FuncType}
    (h : Spec.FuncType bytes type) : bytes ≠ [] := by
  match h with
  | .intro _ _ _ _ _ _ => simp

theorem parses_memType {bytes : List UInt8} {decl : MemDecl} (h : Memory bytes decl) :
    Parses memType bytes decl := by
  match h with
  | .intro _ minimum maximum encoding =>
      unfold memType
      match encoding with
      | .min minBytes minimum minEncoding =>
          refine Parses.bind (parses_byte 0x00) ?_
          show Parses (do
              let minimum ← unsigned 32
              pure ({ pagesMin := UInt32.ofNat minimum } : MemDecl))
            minBytes { pagesMin := minimum, pagesMax := none }
          refine Parses.bind_nil (parses_unsigned minEncoding 32 (Nat.le_refl _)) ?_
          rw [UInt32.ofNat_toNat]
          exact Parses.pure' _
      | .minMax minBytes maxBytes minimum maximum minEncoding maxEncoding =>
          refine Parses.bind (parses_byte 0x01) ?_
          show Parses (do
              let minimum ← unsigned 32
              let maximum ← unsigned 32
              pure ({ pagesMin := UInt32.ofNat minimum,
                      pagesMax := some (UInt32.ofNat maximum) } : MemDecl))
            (minBytes ++ maxBytes) { pagesMin := minimum, pagesMax := some maximum }
          refine Parses.bind (parses_unsigned minEncoding 32 (Nat.le_refl _)) ?_
          refine Parses.bind_nil (parses_unsigned maxEncoding 32 (Nat.le_refl _)) ?_
          rw [UInt32.ofNat_toNat, UInt32.ofNat_toNat]
          exact Parses.pure' _

theorem memory_nonempty {bytes : List UInt8} {decl : MemDecl} (h : Memory bytes decl) :
    bytes ≠ [] := by
  match h with
  | .intro _ _ _ encoding =>
      match encoding with
      | .min _ _ _ => simp
      | .minMax _ _ _ _ _ _ => simp

theorem parses_memories {bytes : List UInt8} {memory : Option MemDecl}
    (h : Vector Memory bytes memory.toList) : Parses memories bytes memory := by
  have hVec := parses_vec_map (g := id) (fun _ _ h => parses_memType h)
    (fun _ _ h => memory_nonempty h) h
  simp only [List.map_id] at hVec
  unfold memories
  refine Parses.bind_nil hVec ?_
  cases memory <;> exact Parses.pure' _

theorem parses_mutability {bytes : List UInt8} {mutable : Bool}
    (h : Mutability bytes mutable) : Parses mutability bytes mutable := by
  cases h <;> exact Parses.bind_nil (parses_byte _) (Parses.pure' _)

theorem parses_constEnd : Parses constEnd [0x0b] () :=
  Parses.bind_nil (parses_byte 0x0b) (Parses.pure' ())

theorem parses_global {bytes : List UInt8} {decl : GlobalDecl} (h : Global bytes decl) :
    Parses global bytes decl := by
  match h with
  | .i32 mutBytes valueBytes mutable value mutabilityEncoding constant =>
      unfold global
      rw [List.append_assoc]
      refine Parses.bind (parses_valueType .i32) ?_
      refine Parses.bind (parses_mutability mutabilityEncoding) ?_
      rw [List.cons_append]
      refine Parses.bind_cons (parses_byte 0x41) ?_
      show Parses (do
          let value := wrap32 (← signed 32)
          constEnd
          pure ({ init := .i32 value, declaredType := some .i32, isMut := mutable,
                  sourceInit := some [.const value] } : GlobalDecl)) (valueBytes ++ [0x0b]) _
      refine Parses.bind (parses_signed constant) ?_
      show Parses (do
          constEnd
          pure ({ init := .i32 (wrap32 value.toBitVec.toInt), declaredType := some .i32,
                  isMut := mutable,
                  sourceInit := some [.const (wrap32 value.toBitVec.toInt)] } : GlobalDecl))
        [0x0b] _
      rw [wrap32_toInt]
      exact Parses.bind_nil parses_constEnd (Parses.pure' _)
  | .i64 mutBytes valueBytes mutable value mutabilityEncoding constant =>
      unfold global
      rw [List.append_assoc]
      refine Parses.bind (parses_valueType .i64) ?_
      refine Parses.bind (parses_mutability mutabilityEncoding) ?_
      rw [List.cons_append]
      refine Parses.bind_cons (parses_byte 0x42) ?_
      show Parses (do
          let value := wrap64 (← signed 64)
          constEnd
          pure ({ init := .i64 value, declaredType := some .i64, isMut := mutable,
                  sourceInit := some [.constI64 value] } : GlobalDecl)) (valueBytes ++ [0x0b]) _
      refine Parses.bind (parses_signed constant) ?_
      show Parses (do
          constEnd
          pure ({ init := .i64 (wrap64 value.toBitVec.toInt), declaredType := some .i64,
                  isMut := mutable,
                  sourceInit := some [.constI64 (wrap64 value.toBitVec.toInt)] } : GlobalDecl))
        [0x0b] _
      rw [wrap64_toInt]
      exact Parses.bind_nil parses_constEnd (Parses.pure' _)

theorem global_nonempty {bytes : List UInt8} {decl : GlobalDecl} (h : Global bytes decl) :
    bytes ≠ [] := by
  cases h <;> simp

theorem parses_importDecl {types : List Wasm.FuncType} {bytes : List UInt8}
    {decl : ImportDecl} (h : Import types bytes decl) : Parses (importDecl types) bytes decl := by
  match h with
  | .intro moduleBytes nameBytes indexBytes decl index moduleName fieldName encoding declaredType =>
      unfold importDecl
      rw [List.append_assoc]
      refine Parses.bind (parses_name moduleName) ?_
      refine Parses.bind (parses_name fieldName) ?_
      refine Parses.bind (parses_byte 0x00) ?_
      show Parses (do
          let index ← unsigned 32
          match types[index]? with
          | some type =>
              pure ({ «module» := decl.module, name := decl.name,
                      params := type.params, results := type.results } : ImportDecl)
          | none => invalid "unknown type") indexBytes decl
      refine Parses.bind_nil (parses_unsigned encoding 32 (Nat.le_refl _)) ?_
      rw [declaredType]
      exact Parses.pure' _

theorem import_nonempty {types : List Wasm.FuncType} {bytes : List UInt8} {decl : ImportDecl}
    (h : Import types bytes decl) : bytes ≠ [] := by
  match h with
  | .intro moduleBytes _ _ _ _ moduleName _ _ _ =>
      have := name_nonempty moduleName
      cases moduleBytes with
      | nil => exact absurd rfl this
      | cons _ _ => simp

theorem parses_exportEntry {bytes : List UInt8} {entry : UInt8 × String × Nat}
    (h : Spec.Export bytes entry) : Parses exportEntry bytes entry := by
  match h with
  | .intro nameBytes indexBytes kind exportName index kindValid nameEncoding indexEncoding =>
      unfold exportEntry
      refine Parses.bind (parses_name nameEncoding) ?_
      refine Parses.bind (parses_byte kind) ?_
      refine Parses.bind_nil (parses_unsigned indexEncoding 32 (Nat.le_refl _)) ?_
      rcases kindValid with rfl | rfl | rfl <;> exact Parses.pure' _

theorem export_nonempty {bytes : List UInt8} {entry : UInt8 × String × Nat}
    (h : Spec.Export bytes entry) : bytes ≠ [] := by
  match h with
  | .intro nameBytes _ _ _ _ _ nameEncoding _ =>
      have := name_nonempty nameEncoding
      cases nameBytes with
      | nil => exact absurd rfl this
      | cons _ _ => simp

theorem parses_functionIndex {types : List Wasm.FuncType} {bytes : List UInt8}
    {func : Wasm.Function} (h : FunctionIndex types bytes func) :
    Parses (unsigned 32) bytes (func.typeIdx.getD 0) := by
  match h with
  | .intro _ _ _ encoding declaredIndex _ =>
      rw [declaredIndex]
      exact parses_unsigned encoding 32 (Nat.le_refl _)

theorem functionIndex_nonempty {types : List Wasm.FuncType} {bytes : List UInt8}
    {func : Wasm.Function} (h : FunctionIndex types bytes func) : bytes ≠ [] := by
  match h with
  | .intro _ _ _ encoding _ _ => exact unsigned_nonempty encoding

theorem parses_local {bytes : List UInt8} {type : ValueType} (h : Local bytes type) :
    Parses localGroup bytes (1, type) := by
  match h with
  | .intro bytes type encoding =>
      unfold localGroup
      have hOne : Unsigned 32 [1] 1 := Unsigned.terminal 32 1 (by decide) (by decide) (by decide)
      exact Parses.bind (parses_unsigned hOne 32 (Nat.le_refl _))
        (Parses.bind_nil (parses_valueType encoding) (Parses.pure' _))

theorem local_nonempty {bytes : List UInt8} {type : ValueType} (h : Local bytes type) :
    bytes ≠ [] := by
  match h with
  | .intro _ _ _ => simp

end Wasm.Encoding.Decoder
