import LeanExe.Wasm.Binary

/-! # WAT text for the core module

Serializes the same lowering as `moduleBytes` to WebAssembly text.  The
function bodies come from the identical `List Instr` values the byte encoder
consumes, so the text and the binary cannot drift; the module skeleton
mirrors the section builders in `Binary.lean` item for item.  `tools/check-wat.sh`
holds the two serializers together by parsing the text back to a binary and
comparing it against `compile` output.
-/

namespace LeanExe.Wasm.Wat

open LeanExe.Wasm (Instr)
open LeanExe.Wasm.Binary.CoreWasm

abbrev Module := LeanExe.IR.Module

def pad (n : Nat) : String :=
  String.join (List.replicate n "  ")

mutual
  partial def instrLines (indent : Nat) : Instr → List String
    | .constI64 n => [s!"{pad indent}i64.const {n}"]
    | .constI32 n => [s!"{pad indent}i32.const {n}"]
    | .constI32NegOne => [s!"{pad indent}i32.const -1"]
    | .localGet n => [s!"{pad indent}local.get {n}"]
    | .localSet n => [s!"{pad indent}local.set {n}"]
    | .localTee n => [s!"{pad indent}local.tee {n}"]
    | .globalGet n => [s!"{pad indent}global.get {n}"]
    | .globalSet n => [s!"{pad indent}global.set {n}"]
    | .call n => [s!"{pad indent}call {n}"]
    | .addI64 => [s!"{pad indent}i64.add"]
    | .subI64 => [s!"{pad indent}i64.sub"]
    | .mulI64 => [s!"{pad indent}i64.mul"]
    | .divUI64 => [s!"{pad indent}i64.div_u"]
    | .remUI64 => [s!"{pad indent}i64.rem_u"]
    | .andI64 => [s!"{pad indent}i64.and"]
    | .orI64 => [s!"{pad indent}i64.or"]
    | .xorI64 => [s!"{pad indent}i64.xor"]
    | .shlI64 => [s!"{pad indent}i64.shl"]
    | .shrUI64 => [s!"{pad indent}i64.shr_u"]
    | .eqI64 => [s!"{pad indent}i64.eq"]
    | .neI64 => [s!"{pad indent}i64.ne"]
    | .ltUI64 => [s!"{pad indent}i64.lt_u"]
    | .leUI64 => [s!"{pad indent}i64.le_u"]
    | .geUI64 => [s!"{pad indent}i64.ge_u"]
    | .eqzI64 => [s!"{pad indent}i64.eqz"]
    | .eqI32 => [s!"{pad indent}i32.eq"]
    | .eqzI32 => [s!"{pad indent}i32.eqz"]
    | .andI32 => [s!"{pad indent}i32.and"]
    | .wrapI64 => [s!"{pad indent}i32.wrap_i64"]
    | .extendUI32 => [s!"{pad indent}i64.extend_i32_u"]
    | .load64 => [s!"{pad indent}i64.load"]
    | .load32 => [s!"{pad indent}i32.load"]
    | .load8U => [s!"{pad indent}i32.load8_u"]
    | .store64 => [s!"{pad indent}i64.store"]
    | .store32 => [s!"{pad indent}i32.store"]
    | .store8 => [s!"{pad indent}i32.store8"]
    | .memorySize => [s!"{pad indent}memory.size"]
    | .memoryGrow => [s!"{pad indent}memory.grow"]
    | .unreachable => [s!"{pad indent}unreachable"]
    | .ret => [s!"{pad indent}return"]
    | .drop => [s!"{pad indent}drop"]
    | .block body =>
        [s!"{pad indent}block"] ++ instrListLines (indent + 1) body ++
          [s!"{pad indent}end"]
    | .loop body =>
        [s!"{pad indent}loop"] ++ instrListLines (indent + 1) body ++
          [s!"{pad indent}end"]
    | .iff resultI64 thn els =>
        let head := if resultI64 then s!"{pad indent}if (result i64)" else s!"{pad indent}if"
        [head] ++ instrListLines (indent + 1) thn ++
          (match els with
           | some elseBody =>
               [s!"{pad indent}else"] ++ instrListLines (indent + 1) elseBody
           | none => []) ++
          [s!"{pad indent}end"]
    | .iffI32 thn els =>
        [s!"{pad indent}if (result i32)"] ++ instrListLines (indent + 1) thn ++
          (match els with
           | some elseBody =>
               [s!"{pad indent}else"] ++ instrListLines (indent + 1) elseBody
           | none => []) ++
          [s!"{pad indent}end"]
    | .br depth => [s!"{pad indent}br {depth}"]
    | .brIf depth => [s!"{pad indent}br_if {depth}"]

  partial def instrListLines (indent : Nat) : List Instr → List String
    | [] => []
    | instr :: rest => instrLines indent instr ++ instrListLines indent rest
end

/-- One function of the printed module: its type index, i64 parameter and
result counts, extra i64 locals, and the shared instruction lowering. -/
structure PlanFunc where
  typeIndex : Nat
  params : Nat
  results : Nat
  extraLocals : Nat
  code : List Instr

def corePlan (module_ : Module) : List PlanFunc :=
  let count := module_.funcs.size
  let releaseIndex := count + 3
  (module_.funcs.toList.zipIdx.map fun (func, index) =>
    { typeIndex := index,
      params := func.params,
      results := func.results.length,
      extraLocals := func.locals - func.params + funcScratch func,
      code := emitFuncInstrs releaseIndex func }) ++
    [{ typeIndex := count, params := 1, results := 1, extraLocals := 6,
       code := coreAllocInstrs },
     { typeIndex := count + 1, params := 0, results := 0, extraLocals := 0,
       code := coreResetInstrs },
     { typeIndex := count + 2, params := 1, results := 1, extraLocals := 1,
       code := coreRetainInstrs },
     { typeIndex := count + 3, params := 1, results := 0, extraLocals := 8,
       code := coreReleaseInstrs releaseIndex }]

def typeText (index params results : Nat) : String :=
  let paramText :=
    if params == 0 then
      ""
    else
      s!" (param{String.join (List.replicate params " i64")})"
  let resultText :=
    if results == 0 then
      ""
    else
      s!" (result{String.join (List.replicate results " i64")})"
  s!"  (type (;{index};) (func{paramText}{resultText}))"

def funcLines (index : Nat) (func : PlanFunc) : List String :=
  let paramText :=
    if func.params == 0 then
      ""
    else
      s!" (param{String.join (List.replicate func.params " i64")})"
  let resultText :=
    if func.results == 0 then
      ""
    else
      s!" (result{String.join (List.replicate func.results " i64")})"
  let localText :=
    if func.extraLocals == 0 then
      []
    else
      [s!"    (local{String.join (List.replicate func.extraLocals " i64")})"]
  [s!"  (func (;{index};) (type {func.typeIndex}){paramText}{resultText}"] ++
    localText ++ instrListLines 2 func.code ++ ["  )"]

def exportLines (module_ : Module) : List String :=
  let count := module_.funcs.size
  [s!"  (export \"memory\" (memory 0))"] ++
    (module_.funcs.toList.zipIdx.filterMap fun (func, index) =>
      func.exportName.map fun name => s!"  (export \"{name}\" (func {index}))") ++
    [s!"  (export \"alloc\" (func {count}))",
     s!"  (export \"reset\" (func {count + 1}))",
     s!"  (export \"retain\" (func {count + 2}))",
     s!"  (export \"release\" (func {count + 3}))",
     s!"  (export \"free\" (func {count + 3}))",
     s!"  (export \"allocCount\" (global {runtimeStatGlobal .allocs}))",
     s!"  (export \"retainCount\" (global {runtimeStatGlobal .retains}))",
     s!"  (export \"releaseCount\" (global {runtimeStatGlobal .releases}))",
     s!"  (export \"freeCount\" (global {runtimeStatGlobal .frees}))"]

def globalLines : List String :=
  [4096, 0, 0, 0, 0, 0].zipIdx.map fun (init, index) =>
    s!"  (global (;{index};) (mut i64) (i64.const {init}))"

def moduleWat (module_ : Module) : String :=
  let plan := corePlan module_
  let count := module_.funcs.size
  let typeLines :=
    (module_.funcs.toList.zipIdx.map fun (func, index) =>
      typeText index func.params func.results.length) ++
      [typeText count 1 1, typeText (count + 1) 0 0, typeText (count + 2) 1 1,
        typeText (count + 3) 1 0]
  let lines :=
    ["(module"] ++
      typeLines ++
      ["  (memory (;0;) 16)"] ++
      globalLines ++
      exportLines module_ ++
      (plan.zipIdx.flatMap fun (func, index) => funcLines index func) ++
      [")"]
  String.intercalate "\n" lines ++ "\n"

end LeanExe.Wasm.Wat
