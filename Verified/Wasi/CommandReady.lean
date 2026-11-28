module

public import Verified.Wasi.Code

@[expose] public section

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
  | _, _, .read buffer start count =>
    [(Expr.var (S := pureSigs) buffer).code (pool := pool) h slots (base + Ty.bytes.width)
        (sysTakeLive live [start, count] []) ++
      coerceCode h .bytes ((Expr.var (S := pureSigs) buffer).mode (slots.map Slot.mode)) .owned
        (base + Ty.bytes.width)]
  | _, _, .readAll limit => [limit.code (pool := pool) h slots base live]
  | context, _, .write _ buffer start count =>
    [releaseWhere context slots (fun i =>
      (i == buffer.index || (i == start.index || i == count.index)) && !live i)]
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
  | context, _, .sys _ _ args inputs buffers =>
    match buffers with
    | [] =>
      [releaseWhere context slots
        (fun i => (inputs.any fun input => i == input.index) && !live i)]
    | buffer :: _ =>
      [(Expr.var (S := pureSigs) buffer).code (pool := pool) h slots (base + Ty.bytes.width)
          (sysTakeLive live args inputs) ++
        coerceCode h .bytes ((Expr.var (S := pureSigs) buffer).mode (slots.map Slot.mode)) .owned
          (base + Ty.bytes.width),
        releaseWhere (.bytes :: context) (⟨base, .owned⟩ :: slots)
          (fun i => (inputs.any fun input => i == input.index + 1) && !shift 1 live i)]
  | _, _, .letPair (first := first) (second := second) pair body =>
    let mode := (Expr.var (S := pureSigs) pair).mode (slots.map Slot.mode)
    [(Expr.var (S := pureSigs) pair).code (pool := pool) h slots (base + first.width + second.width)
        (fun i => live i || body.uses (i + 2)),
      letPairReleaseCode first second mode base (body.uses 1) (body.uses 0)] ++
      body.fragments h (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots)
        (base + first.width + second.width) (shift 2 live) pool

/-- `Command.fragments` with the variables live after the command as a bitmask, together with the
command's `useMask`, in one pass, as `Command.codeMask` computes `Command.codeWith`.
`Command.fragmentsMask_eq` equates the two, and `EffectFunc.checkReadyWith` calls this one. -/
def Command.fragmentsMask (h : Nat) (slots : List Slot) (base : Nat) (live : Nat)
    (pool : Bytes.LiteralPool) : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → List Program × Nat
  | _, _, command@.unit
  | _, _, command@(.read _ _ _) =>
    (command.fragments h slots base live.testBit pool, command.useMask)
  | _, _, .ret (type := type) value =>
    ([value.codeMask h slots base live pool ++
        coerceCode h type (value.mode (slots.map Slot.mode)) .owned base],
      value.useMask)
  | _, _, .bind (intermediate := .unit) first next =>
    let after := next.fragmentsMask h slots base live pool
    let before := first.fragmentsMask h slots base (live ||| after.2) pool
    (before.1 ++ after.1, before.2 ||| after.2)
  | _, _, .bind (intermediate := .value type) first next =>
    let after := next.fragmentsMask h (⟨base, .owned⟩ :: slots) (base + type.width) (live <<< 1)
      pool
    let before := first.fragmentsMask h slots (base + type.width) (live ||| after.2 >>> 1) pool
    (before.1 ++ [releaseCode type base] ++ after.1, before.2 ||| after.2 >>> 1)
  | context, result, .ite condition yes no =>
    let yesFragments := yes.fragmentsMask h slots (base + result.width) live pool
    let noFragments := no.fragmentsMask h slots (base + result.width) live pool
    let mid := live ||| yesFragments.2 ||| noFragments.2
    ([condition.codeMask h slots base mid pool,
        releaseMask context slots (maskDiff mid (live ||| yesFragments.2)),
        releaseMask context slots (maskDiff mid (live ||| noFragments.2))] ++
        yesFragments.1 ++ noFragments.1,
      condition.useMask ||| yesFragments.2 ||| noFragments.2)
  | context, _, .call (signature := signature) _ args =>
    let all := live ||| argsMask fun j => (args j).useMask
    let kept := maskDiff all (argsMask fun j =>
      maskIf (signature.callMoves slots live.testBit args j) (args j).useMask)
    ([argsCode (fun i =>
        if (signature.params.get i).scalar then (args i).codeMask h slots base all pool
        else if signature.mode i = .owned then (args i).ownedCode h slots base kept.testBit
        else (args i).placeCode h slots),
        releaseMask context slots (maskDiff kept live)],
      argsMask fun i => (args i).useMask)
  | _, _, .readAll limit => ([limit.codeMask h slots base live pool], limit.useMask)
  | context, _, .write _ buffer start count =>
    ([releaseMask context slots
        (maskDiff (1 <<< buffer.index ||| (1 <<< start.index ||| 1 <<< count.index)) live)],
      1 <<< buffer.index ||| (1 <<< start.index ||| 1 <<< count.index))
  | _, _, .exit status => ([status.codeMask h slots base live pool], status.useMask)
  | context, _, .loop (type := type) count initial test step =>
    let used := test.useMask >>> 2 ||| step.useMask >>> 2
    let all := live ||| used
    let captured := slots.map fun slot => { slot with mode := .borrowed }
    let state := base + 2
    let scratch := state + type.width
    ([count.codeMask h slots base (all ||| initial.useMask) pool,
        initial.codeMask h slots (base + 1) all pool ++
          coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1),
        test.codeMask h
          (⟨state, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: captured) scratch
          (1 ||| all <<< 2) pool,
        releaseCode type state,
        releaseMask context slots (maskDiff used live)] ++
        (step.fragmentsMask h (⟨state, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: captured)
          scratch (all <<< 2) pool).1,
      count.useMask ||| initial.useMask ||| test.useMask >>> 2 ||| step.useMask >>> 2)
  | context, _, .sys _ _ args inputs buffers =>
    (match buffers with
      | [] => [releaseMask context slots (maskDiff (varsMask inputs) live)]
      | buffer :: _ =>
        [(Expr.var (S := pureSigs) buffer).code (pool := pool) h slots (base + Ty.bytes.width)
            (sysTakeLive live.testBit args inputs) ++
          coerceCode h .bytes ((Expr.var (S := pureSigs) buffer).mode (slots.map Slot.mode))
            .owned (base + Ty.bytes.width),
          releaseMask (.bytes :: context) (⟨base, .owned⟩ :: slots)
            (maskDiff (varsMask inputs <<< 1) (live <<< 1))],
      varsMask buffers ||| (varsMask inputs ||| varsMask args))
  | _, _, .letPair (first := first) (second := second) pair body =>
    let mode := (Expr.var (S := pureSigs) pair).mode (slots.map Slot.mode)
    let bodyFragments := body.fragmentsMask h (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots)
      (base + first.width + second.width) (live <<< 2) pool
    ([(Expr.var (S := pureSigs) pair).code (pool := pool) h slots
          (base + first.width + second.width) (live ||| bodyFragments.2 >>> 2).testBit,
        letPairReleaseCode first second mode base (bodyFragments.2.testBit 1)
          (bodyFragments.2.testBit 0)] ++
        bodyFragments.1,
      1 <<< pair.index ||| bodyFragments.2 >>> 2)

theorem Command.fragmentsMask_eq (h : Nat) (pool : Bytes.LiteralPool)
    (command : Command pureSigs effectSigs context result) :
    ∀ (slots : List Slot) (base live : Nat),
      command.fragmentsMask h slots base live pool =
        (command.fragments h slots base live.testBit pool, command.useMask) := by
  induction command with
  | unit | read => intro _ _ _; rfl
  | ret value | readAll value | exit value =>
    intro slots base live
    simp only [Command.fragmentsMask, Command.fragments, Command.useMask, Expr.codeMask_eq]
  | call callee args =>
    intro slots base live
    simp only [Command.fragmentsMask, Command.fragments, Command.useMask, Expr.codeMask_eq,
      releaseMask_eq, testBit_maskDiff_eq, testBit_maskIf_eq, testBit_or_eq, testBit_argsMask_eq,
      Expr.usesFast]
  | write output buffer start count =>
    intro slots base live
    simp only [Command.fragmentsMask, Command.fragments, Command.useMask, releaseMask_eq,
      testBit_maskDiff_eq, testBit_or_eq, testBit_one_shiftLeft_eq]
  | sys operation form args inputs buffers =>
    intro slots base live
    cases buffers with
    | nil =>
      simp only [Command.fragmentsMask, Command.fragments, Command.useMask, releaseMask_eq,
        testBit_maskDiff_eq, testBit_varsMask_eq]
    | cons buffer rest =>
      simp only [Command.fragmentsMask, Command.fragments, Command.useMask, releaseMask_eq,
        testBit_maskDiff_eq, testBit_varsMask_shiftLeft_one_eq]
      simp only [testBit_shiftLeft_eq]
  | @bind context intermediate result first next firstIh nextIh =>
    intro slots base live
    cases intermediate <;>
      simp only [Command.fragmentsMask, Command.fragments, Command.useMask, ResultTy.bindCount,
        Nat.shiftRight_zero, firstIh, nextIh, testBit_or_eq, testBit_shiftRight_eq,
        testBit_shiftLeft_eq, Command.useMask_testBit]
  | ite condition yes no yesIh noIh =>
    intro slots base live
    simp only [Command.fragmentsMask, Command.fragments, Command.useMask, yesIh, noIh,
      Expr.codeMask_eq, releaseMask_eq, testBit_maskDiff_eq, testBit_or_eq,
      Command.useMask_testBit]
  | loop count initial test step stepIh =>
    intro slots base live
    simp only [Command.fragmentsMask, Command.fragments, Command.useMask, stepIh,
      Expr.codeMask_eq, releaseMask_eq, testBit_maskDiff_eq, testBit_or_eq,
      testBit_shiftRight_eq, testBit_shiftLeft_eq, testBit_one_eq, Command.useMask_testBit,
      Expr.useMask_testBit, Expr.usesFast_eq]
  | letPair pair body bodyIh =>
    intro slots base live
    simp only [Command.fragmentsMask, Command.fragments, Command.useMask, bodyIh, testBit_or_eq,
      testBit_shiftRight_eq, testBit_shiftLeft_eq, Command.useMask_testBit]

/-- A command is ready for a module that imports `calls` when its fragments have the encoder's
form and call only source functions, and when `calls` holds the calls of its `sys` commands. -/
def Command.ReadyWith (calls : List LeanExe.Wasi.Call) (source : Wasm.Module) (h : Nat) (slots : List Slot)
    (base : Nat) (live : Nat → Bool) (pool : Bytes.LiteralPool)
    (command : Command pureSigs effectSigs context result) : Prop :=
  (∀ fragment ∈ command.fragments h slots base live pool,
    Encoding.ProgramForm fragment ∧ Relocation.programClosed source.funcs.length fragment = true) ∧
    command.callsReady calls = true

def Command.Ready (source : Wasm.Module) (h : Nat) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) (pool : Bytes.LiteralPool)
    (command : Command pureSigs effectSigs context result) : Prop :=
  command.ReadyWith [] source h slots base live pool

end Verified.Wasi
