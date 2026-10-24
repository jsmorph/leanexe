import Verified.Wasi.Code

namespace Verified.Wasi

open Wasm

def Command.fragments (h : Nat) (slots : List Slot) (base : Nat) (live : Nat → Bool)
    (pool : Bytes.LiteralPool) : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → List Program
  | _, _, .unit => []
  | _, _, .ret (type := type) value =>
    [value.code (pool := pool) h slots base live ++
      coerceCode h type (value.mode (slots.map Slot.mode)) .owned base]
  | _, _, .bind (intermediate := .unit) first next =>
    first.fragments h slots base (fun i => live i || next.uses i) pool ++
      next.fragments h slots base live pool
  | _, _, .bind (intermediate := .value type) first next =>
    first.fragments h slots (base + type.width) (fun i => live i || next.uses (i + 1)) pool ++
      [releaseCode type base] ++
      next.fragments h (⟨base, .owned⟩ :: slots) (base + type.width) (shift 1 live) pool
  | context, result, .ite condition yes no =>
    let mid := fun i => live i || yes.uses i || no.uses i
    [condition.code (pool := pool) h slots base mid,
      releaseWhere context slots (fun i => mid i && !(live i || yes.uses i)),
      releaseWhere context slots (fun i => mid i && !(live i || no.uses i))] ++
      yes.fragments h slots (base + result.width) live pool ++
      no.fragments h slots (base + result.width) live pool
  | context, _, .call (signature := signature) _ args =>
    let all := fun i => live i || argsAny fun j => (args j).usesFast i
    let kept := fun i => all i &&
      !(argsAny fun j => signature.callMoves slots live args j && (args j).usesFast i)
    [argsCode (fun i =>
      if (signature.params.get i).scalar then (args i).code (pool := pool) h slots base all
      else if signature.mode i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots),
      releaseWhere context slots (fun i => kept i && !live i)]
  | _, _, .read capacity => [capacity.code (pool := pool) h slots base live]
  | context, _, .write _ bytes =>
    [releaseWhere context slots (fun i => i == bytes.index && !live i)]
  | _, _, .exit status => [status.code (pool := pool) h slots base live]
  | context, _, .loop (type := type) count initial test step =>
    let used := fun i => test.uses (i + 2) || step.uses (i + 2)
    let all := fun i => live i || used i
    let captured := slots.map fun slot => { slot with mode := .borrowed }
    let state := base + 2
    let scratch := state + type.width
    [count.code (pool := pool) h slots base (fun i => all i || initial.usesFast i),
      initial.code (pool := pool) h slots (base + 1) all ++
        coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1),
      test.code (pool := pool) h
        (⟨state, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: captured) scratch
        (fun i => i == 0 || shift 2 all i),
      releaseCode type state,
      releaseWhere context slots (fun i => used i && !live i)] ++
      step.fragments h (⟨state, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: captured)
        scratch (shift 2 all) pool

def Command.Ready (source : Wasm.Module) (h : Nat) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) (pool : Bytes.LiteralPool)
    (command : Command pureSigs effectSigs context result) : Prop :=
  ∀ fragment ∈ command.fragments h slots base live pool,
    Encoding.ProgramForm fragment ∧ Relocation.programClosed source.funcs.length fragment = true

end Verified.Wasi
