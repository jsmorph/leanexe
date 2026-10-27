import Verified.Wasi.CodeAnalysis
import Verified.Wasi.Wrappers

namespace Verified.Wasi

open Wasm LeanExe.Wasi

/-- Command code uses final module indices.  Pure fragments, copies, and releases undergo the
three-import relocation once.  Normal returns leave owned result words on the stack.  Local
zero carries the incoming depth, and `live` identifies context values retained afterward. -/
def Command.code (source : Wasm.Module) (h : Nat) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) (pool : Bytes.LiteralPool) :
    {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Program
  | _, _, .unit => []
  | _, _, .ret (type := type) value =>
    Relocation.program (value.code (pool := pool) h slots base live ++
      coerceCode h type (value.mode (slots.map Slot.mode)) .owned base)
  | _, _, .bind (intermediate := .unit) first next =>
    first.code (pool := pool) source h slots base (fun i => live i || next.uses i) ++
      next.code (pool := pool) source h slots base live
  | _, _, .bind (intermediate := .value type) first next =>
    first.code (pool := pool) source h slots (base + type.width)
        (fun i => live i || next.uses (i + 1)) ++
      storeCode h base type.types ++
      (if next.uses 0 = false then Relocation.program (releaseCode type base) else []) ++
      next.code (pool := pool) source h (⟨base, .owned⟩ :: slots) (base + type.width)
        (shift 1 live)
  | context, result, .ite condition yes no =>
    let mid := fun i => live i || yes.uses i || no.uses i
    Relocation.program (condition.code (pool := pool) h slots base mid) ++
      [.eqzI64, .iff 0 0
        (Relocation.program (releaseWhere context slots
            (fun i => mid i && !(live i || no.uses i))) ++
          no.code (pool := pool) source h slots (base + result.width) live ++
          storeCode h base result.types)
        (Relocation.program (releaseWhere context slots
            (fun i => mid i && !(live i || yes.uses i))) ++
          yes.code (pool := pool) source h slots (base + result.width) live ++
          storeCode h base result.types) [] []] ++
      loadCode h base result.types
  | context, _, .call (signature := signature) callee args =>
    let all := fun i => live i || argsAny fun j => (args j).usesFast i
    let kept := fun i => all i &&
      !(argsAny fun j => signature.callMoves slots live args j && (args j).usesFast i)
    [.localGet 0, .constI64 1, .addI64] ++
      argsCode (fun i => Relocation.program (
        if (signature.params.get i).scalar then (args i).code (pool := pool) h slots base all
        else if signature.mode i = .owned then (args i).ownedCode h slots base kept
        else (args i).placeCode h slots)) ++
      [.call (Wrappers.effectIndex source callee.index)] ++
      Relocation.program (releaseWhere context slots (fun i => kept i && !live i))
  | _, _, .read capacity =>
    Relocation.program (capacity.code (pool := pool) h slots base live) ++
      [.call (Wrappers.readIndex source)]
  | context, _, .write output bytes =>
    loadCode h (slots.getD bytes.index default).loc Ty.bytes.types ++
      [.call (match output with
        | .stdout => Wrappers.stdoutIndex source
        | .stderr => Wrappers.stderrIndex source)] ++
      Relocation.program (releaseWhere context slots (fun i => i == bytes.index && !live i))
  | _, _, .exit code =>
    Relocation.program (code.code (pool := pool) h slots base live) ++
      [.localSet base] ++ exitCode base
  | context, _, .loop (type := type) count initial test step =>
    let used := fun i => test.uses (i + 2) || step.uses (i + 2)
    let all := fun i => live i || used i
    let captured := slots.map fun slot => { slot with mode := .borrowed }
    let state := base + 2
    let scratch := state + type.width
    Relocation.program (count.code (pool := pool) h slots base
        (fun i => all i || initial.usesFast i)) ++
      [.localSet base] ++
      Relocation.program (initial.code (pool := pool) h slots (base + 1) all ++
        coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1)) ++
      storeCode h state type.types ++ [.constI64 0, .localSet (base + 1),
        .block 0 0 [.loop 0 0
          ([.localGet (base + 1), .localGet base, .geUI64, .br_if 1] ++
            Relocation.program (test.code (pool := pool) h
              (⟨state, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: captured) scratch
              (fun i => i == 0 || shift 2 all i)) ++
            [.eqzI64, .br_if 1] ++
            (if step.uses 0 = false then Relocation.program (releaseCode type state) else []) ++
            step.code (pool := pool) source h
              (⟨state, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: captured) scratch (shift 2 all) ++
            storeCode h state type.types ++
            [.localGet (base + 1), .constI64 1, .addI64, .localSet (base + 1), .br 0]) [] []]
          [] []] ++
      Relocation.program (releaseWhere context slots (fun i => used i && !live i)) ++
      loadCode h state type.types

def EffectFunc.type (function : EffectFunc pureSigs effectSigs) : FuncType :=
  { params := codeParams function.params true
    results := function.result.types }

def EffectFunc.positions (function : EffectFunc pureSigs effectSigs) : Nat :=
  1 + widthSum function.params + function.body.width

def EffectFunc.function (source : Wasm.Module) (function : EffectFunc pureSigs effectSigs)
    (typeIdx : Nat) (pool : Bytes.LiteralPool) : Wasm.Function :=
  let slots := paramSlots function.params function.modes 1
  let h := function.positions
  { params := codeParams function.params true
    locals := List.replicate function.body.width .i64 ++
      List.replicate h .f64 ++ List.replicate h .f32
    body := guardCode ++ paramCopyCode h 1 (function.params.flatMap Ty.types) ++
      Relocation.program (releaseWhere function.params slots (fun i => !function.body.uses i)) ++
      function.body.code (pool := pool) source h slots (1 + widthSum function.params)
        (fun _ => false)
    results := function.result.types
    typeIdx := some typeIdx }

end Verified.Wasi
