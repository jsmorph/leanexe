import Verified.Wasi.Code

namespace Verified.Wasi

open Wasm

def EffectSig.type (signature : EffectSig) : FuncType :=
  { params := codeParams signature.params true
    results := signature.result.types }

def EffectSig.entryType (signature : EffectSig) : FuncType :=
  { params := signature.params.flatMap Ty.types
    results := signature.result.types }

def effectTypeIndex (source : Wasm.Module) (index : Nat) : Nat :=
  Module.extraTypeIndex source (2 + index)

def EffectProg.types : {effectSigs : List EffectSig} →
    EffectProg pureSigs effectSigs → List FuncType
  | _, .nil => []
  | _, .cons function rest => rest.types ++ [function.type]

/-- Bodies follow their earlier callees.  The three I/O functions precede them, while two
function types cover those wrappers. -/
def EffectProg.functions (source : Wasm.Module)
    (pool : Bytes.LiteralPool) :
    {effectSigs : List EffectSig} → EffectProg pureSigs effectSigs → List Function
  | _, .nil => []
  | _, .cons (effectSigs := effectSigs) function rest =>
    rest.functions source pool ++ [function.function source (effectTypeIndex source effectSigs.length) pool]

inductive HiddenTables : List Ty → List Mode → Type where
  | nil : HiddenTables params modes
  | cons (address : UInt64) (rest : HiddenTables params modes) :
      HiddenTables (.array .word :: params) (.borrowed :: modes)

def HiddenTables.addresses : HiddenTables params modes → List UInt64
  | .nil => []
  | .cons address rest => address :: rest.addresses

def HiddenTables.visibleParams : {params : List Ty} → {modes : List Mode} →
    HiddenTables params modes → List Ty
  | params, _, .nil => params
  | _, _, .cons _ rest => rest.visibleParams

def HiddenTables.visibleModes : {params : List Ty} → {modes : List Mode} →
    HiddenTables params modes → List Mode
  | _, modes, .nil => modes
  | _, _, .cons _ rest => rest.visibleModes

theorem HiddenTables.params_eq (tables : HiddenTables params modes) :
    params = List.replicate tables.addresses.length (.array .word) ++ tables.visibleParams := by
  induction tables with
  | nil => rfl
  | cons address rest ih =>
    simp only [HiddenTables.addresses, List.length_cons, List.replicate_succ,
      List.cons_append, HiddenTables.visibleParams, ← ih]

theorem HiddenTables.modes_eq (tables : HiddenTables params modes) :
    modes = List.replicate tables.addresses.length .borrowed ++ tables.visibleModes := by
  induction tables with
  | nil => rfl
  | cons address rest ih =>
    simp only [HiddenTables.addresses, List.length_cons, List.replicate_succ,
      List.cons_append, HiddenTables.visibleModes, ← ih]

structure EffectEntry (effectSigs : List EffectSig) where
  signature : EffectSig
  callee : EffectVar effectSigs signature
  tables : HiddenTables signature.params signature.modes

def EffectEntry.type (entry : EffectEntry effectSigs) : FuncType :=
  { params := entry.tables.visibleParams.flatMap Ty.types
    results := entry.signature.result.types }

def EffectEntry.function (source : Wasm.Module) (entry : EffectEntry effectSigs)
    (typeIdx : Nat) : Function :=
  let params := entry.tables.visibleParams.flatMap Ty.types
  { params
    locals := []
    body := [.constI64 0] ++ entry.tables.addresses.map Instruction.constI64 ++
      (List.range params.length).map Instruction.localGet ++
      [.call (Wrappers.effectIndex source entry.callee.index)]
    results := entry.signature.result.types
    typeIdx := some typeIdx }

structure EffectMain (effectSigs : List EffectSig) where
  name : String
  tables : List UInt64 := []
  callee : EffectVar effectSigs
    ⟨name, List.replicate tables.length (.array .word),
      List.replicate tables.length .borrowed, .value .word⟩

def startType : FuncType := { params := [], results := [] }

def EffectMain.function (source : Wasm.Module) (main : EffectMain effectSigs)
    (typeIdx : Nat) : Function :=
  { params := []
    locals := []
    body := [.constI64 0] ++ main.tables.map Instruction.constI64 ++
      [.call (Wrappers.effectIndex source main.callee.index), .wrapI64, .call 2, .unreachable]
    results := []
    typeIdx := some typeIdx }

theorem EffectVar.index_lt (callee : EffectVar effectSigs signature) :
    callee.index < effectSigs.length := by
  induction callee with
  | here => simp only [EffectVar.index, List.length_cons]; omega
  | there callee ih => simp only [EffectVar.index, List.length_cons]; omega

@[simp] theorem EffectProg.types_length (program : EffectProg pureSigs effectSigs) :
    program.types.length = effectSigs.length := by
  induction program with
  | nil => rfl
  | cons function rest ih => simp only [EffectProg.types, List.length_append,
      ih, List.length_cons, List.length_nil]

@[simp] theorem EffectProg.functions_length (program : EffectProg pureSigs effectSigs)
    (source : Wasm.Module) (pool : Bytes.LiteralPool) :
    (program.functions source pool).length = effectSigs.length := by
  induction program with
  | nil => rfl
  | cons function rest ih => simp only [EffectProg.functions, List.length_append,
      ih, List.length_cons, List.length_nil]

theorem EffectProg.types_get : {effectSigs : List EffectSig} →
    (program : EffectProg pureSigs effectSigs) → {signature : EffectSig} →
    (callee : EffectVar effectSigs signature) →
    program.types[callee.index]? = some signature.type
  | _, .nil, _, callee => nomatch callee
  | _, .cons function rest, _, .here => by
    rw [EffectProg.types, EffectVar.index,
      List.getElem?_append_right (by rw [EffectProg.types_length]), EffectProg.types_length,
      Nat.sub_self]
    rfl
  | _, .cons function rest, _, .there callee => by
    rw [EffectProg.types, EffectVar.index,
      List.getElem?_append_left (by rw [EffectProg.types_length]; exact callee.index_lt)]
    exact rest.types_get callee

@[simp] theorem EffectFunc.function_signature (source : Wasm.Module)
    (function : EffectFunc pureSigs effectSigs) (typeIdx : Nat)
    (pool : Bytes.LiteralPool) :
    Encoding.Spec.signature (function.function source typeIdx pool) = function.type := rfl

theorem EffectProg.functions_signatures (program : EffectProg pureSigs effectSigs)
    (source : Wasm.Module) (pool : Bytes.LiteralPool) :
    (program.functions source pool).map Encoding.Spec.signature = program.types := by
  induction program with
  | nil => rfl
  | cons function rest ih =>
    simp only [EffectProg.functions, List.map_append, List.map_cons, List.map_nil,
      EffectFunc.function_signature, ih, EffectProg.types]

theorem EffectProg.function_typeIdx (source : Wasm.Module)
    (pool : Bytes.LiteralPool) :
    {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    {signature : EffectSig} → (callee : EffectVar effectSigs signature) →
    ((program.functions source pool)[callee.index]?).map Function.typeIdx =
      some (some (effectTypeIndex source callee.index))
  | _, .nil, _, callee => nomatch callee
  | _, .cons function rest, _, .here => by
    rw [EffectProg.functions, EffectVar.index,
      List.getElem?_append_right (by rw [rest.functions_length source pool]),
      rest.functions_length source pool, Nat.sub_self]
    rfl
  | _, .cons function rest, _, .there callee => by
    rw [EffectProg.functions, EffectVar.index,
      List.getElem?_append_left (by rw [rest.functions_length source pool]; exact callee.index_lt)]
    exact rest.function_typeIdx source pool callee

theorem EffectProg.function_signature (program : EffectProg pureSigs effectSigs)
    (source : Wasm.Module) (callee : EffectVar effectSigs signature)
    (pool : Bytes.LiteralPool) :
    ((program.functions source pool)[callee.index]?).map Encoding.Spec.signature =
      some signature.type := by
  rw [← List.getElem?_map, program.functions_signatures source pool, EffectProg.types_get]

@[simp] theorem EffectEntry.function_signature (source : Wasm.Module)
    (entry : EffectEntry effectSigs) (typeIdx : Nat) :
    Encoding.Spec.signature (entry.function source typeIdx) = entry.type := rfl

theorem EffectEntry.type_nil (signature : EffectSig) (callee : EffectVar effectSigs signature) :
    (EffectEntry.mk signature callee .nil).type = signature.entryType := rfl

@[simp] theorem EffectMain.function_signature (source : Wasm.Module)
    (main : EffectMain effectSigs) (typeIdx : Nat) :
    Encoding.Spec.signature (main.function source typeIdx) = startType := rfl

end Verified.Wasi
