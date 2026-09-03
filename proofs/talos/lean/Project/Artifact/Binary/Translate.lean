import Project.TalosPrelude
import Project.Artifact.Binary.Validate

namespace Wasm.Binary

def ValType.toTalos : ValType → Wasm.ValueType
  | .i32 => .i32
  | .i64 => .i64
  | .f64 => .f64

def Mutability.toTalos : Mutability → Bool
  | .immutable => false
  | .mutable => true

def ConstExpr.toTalos : ConstExpr → Wasm.Program
  | .i32Const value => [.const (UInt32.ofInt value)]
  | .i64Const value => [.constI64 (UInt64.ofInt value)]

def FuncType.toTalos (type : FuncType) : Wasm.FuncType :=
  { params := type.params.map ValType.toTalos
    results := type.results.map ValType.toTalos }

namespace Translation

def resultTypes : BlockType → List Wasm.ValueType
  | .empty => []
  | .value type => [type.toTalos]

def resultArity : BlockType → Nat
  | type => (resultTypes type).length

end Translation

mutual
  def Instr.toTalos : Instr → List Wasm.Instruction
    | .unreachable => [.unreachable]
    | .drop => [.drop]
    | .block type body =>
        [.block 0 (Translation.resultArity type) (Instr.listToTalos body)
          [] (Translation.resultTypes type)]
    | .loop type body =>
        [.loop 0 (Translation.resultArity type) (Instr.listToTalos body)
          [] (Translation.resultTypes type)]
    | .iff type thenBody elseBody =>
        let translatedElse :=
          match elseBody with
          | none => []
          | some body => Instr.listToTalos body
        [.iff 0 (Translation.resultArity type) (Instr.listToTalos thenBody) translatedElse
          [] (Translation.resultTypes type)]
    | .br depth => [.br depth.toNat]
    | .brIf depth => [.br_if depth.toNat]
    | .ret => [.ret]
    | .call index => [.call index.toNat]
    | .localGet index => [.localGet index.toNat]
    | .localSet index => [.localSet index.toNat]
    | .localTee index => [.localTee index.toNat]
    | .globalGet index => [.globalGet index.toNat]
    | .globalSet index => [.globalSet index.toNat]
    | .i32Const value => [.const (UInt32.ofInt value)]
    | .i64Const value => [.constI64 (UInt64.ofInt value)]
    | .i32Eqz => [.eqz]
    | .i32Eq => [.eq]
    | .i32And => [.and]
    | .i64Eqz => [.eqzI64]
    | .i64Eq => [.eqI64]
    | .i64Ne => [.neI64]
    | .i64LtU => [.ltUI64]
    | .i64LeU => [.leUI64]
    | .i64GeU => [.geUI64]
    | .i64Add => [.addI64]
    | .i64Sub => [.subI64]
    | .i64Mul => [.mulI64]
    | .i64DivU => [.divUI64]
    | .i64RemU => [.remUI64]
    | .i64And => [.andI64]
    | .i64Or => [.orI64]
    | .i64Xor => [.xorI64]
    | .i64Shl => [.shlI64]
    | .i64ShrU => [.shrUI64]
    | .f64Add => [.f64Add]
    | .f64Mul => [.f64Mul]
    | .i32WrapI64 => [.wrapI64]
    | .i64ExtendI32U => [.extendUI32]
    | .i64ReinterpretF64 => [.i64ReinterpretF64]
    | .f64ReinterpretI64 => [.f64ReinterpretI64]
    | .i64Load arg => [.load64 arg.offset]
    | .i32Load arg => [.load32 arg.offset]
    | .i32Load8U arg => [.load8U arg.offset]
    | .i64Store arg => [.store64 arg.offset]
    | .i32Store arg => [.store32 arg.offset]
    | .i32Store8 arg => [.store8 arg.offset]
    | .memorySize _ => [.memorySize]
    | .memoryGrow _ => [.memoryGrow]

  def Instr.listToTalos : List Instr → List Wasm.Instruction
    | [] => []
    | instr :: rest => instr.toTalos ++ Instr.listToTalos rest
end

namespace Translation

def expandLocals : List LocalDecl → List Wasm.ValueType
  | [] => []
  | decl :: rest =>
      List.replicate decl.count.toNat decl.type.toTalos ++ expandLocals rest

def globalValue : ConstExpr → Wasm.Value
  | .i32Const value => .i32 (UInt32.ofInt value)
  | .i64Const value => .i64 (UInt64.ofInt value)

def functionToTalos (raw : RawModule) (typeIndex : UInt32)
    (code : Code) : Wasm.Function :=
  let type := raw.types[typeIndex.toNat]!
  { params := type.params.map ValType.toTalos
    locals := expandLocals code.locals
    body := Instr.listToTalos code.body
    results := type.results.map ValType.toTalos
    typeIdx := some typeIndex.toNat }

def functions (raw : RawModule) : List Wasm.Function :=
  (raw.functionTypeIndices.zip raw.codes).map fun pair =>
    functionToTalos raw pair.1 pair.2

def functionExports (raw : RawModule) : List Wasm.Export :=
  raw.exports.filterMap fun entry =>
    match entry.desc with
    | .func index => some { name := entry.name.text, funcIdx := index.toNat }
    | _ => none

def globalExports (raw : RawModule) : List (String × Nat) :=
  raw.exports.filterMap fun entry =>
    match entry.desc with
    | .global index => some (entry.name.text, index.toNat)
    | _ => none

def memoryExports (raw : RawModule) : List (String × Nat) :=
  raw.exports.filterMap fun entry =>
    match entry.desc with
    | .memory index => some (entry.name.text, index.toNat)
    | _ => none

def memory (raw : RawModule) : Option Wasm.MemDecl :=
  raw.memories.head?.map fun memory =>
    { pagesMin := memory.limits.min, pagesMax := memory.limits.max, data := [] }

def globals (raw : RawModule) : List Wasm.GlobalDecl :=
  raw.globals.map fun global =>
    { init := globalValue global.init
      declaredType := some global.type.type.toTalos
      isMut := global.type.mutability.toTalos
      sourceInit := some global.init.toTalos }

def gcTypes (raw : RawModule) : List Wasm.GcTypeDef :=
  raw.types.map fun type =>
    { comp := .func type.toTalos }

def module (raw : RawModule) : Wasm.Module :=
  { funcs := functions raw
    exports := functionExports raw
    memory := memory raw
    globals := globals raw
    types := raw.types.map FuncType.toTalos
    gcTypes := gcTypes raw
    globalExports := globalExports raw
    memoryExports := memoryExports raw }

end Translation

def ValidatedModule.toTalos (validated : ValidatedModule) : Wasm.Module :=
  Translation.module validated.raw

end Wasm.Binary
