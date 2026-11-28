module

public import Verified.Wasi.CodeAnalysis
public import Verified.Wasi.Wrappers
public import Verified.Wasi.ReadAllCode
public import Verified.Wasi.SysCode

@[expose] public section

namespace Verified.Wasi

open Wasm LeanExe.Wasi

/-- The releases after the stores of a pair's components, as `Expr.letPair` makes them: the first
component, at `base`, and then the second, after it, each when the pair is owned and the body does
not use the component. -/
def letPairReleaseCode (first second : Ty) (mode : Mode) (base : Nat)
    (firstUsed secondUsed : Bool) : Program :=
  (if mode = .owned ∧ firstUsed = false then releaseCode first base else []) ++
    (if mode = .owned ∧ secondUsed = false then releaseCode second (base + first.width) else [])

/-- The read of stdin into the window of the buffer whose root and size lie in the two locals
from `root`, from the window's start and count in locals `start` and `count`: the window's address
and length in `base + 1` and `base + 2`, the call of the read wrapper at `index`, the count in
`base + 3`, the errno in `base`, and the end of a fill, which stores 0 into the window after an
errno, with the index of the zero fill in `base + 4`, and pushes the errno, the count, and the
buffer's root and size. -/
def readFillCode (index root start count base : Nat) : Program :=
  windowCode root start count (base + 1) ++
    [.localGet (base + 1), .localGet (base + 2), .call index, .localSet (base + 3),
     .localSet base] ++
    fillTailCode root base

/-- Command code uses final module indices.  Pure fragments, copies, and releases undergo the
relocation past the module's imports once.  Normal returns leave owned result words on the stack.  Local
zero holds the incoming depth, and `live` identifies context values retained afterward.  A write
passes its buffer's root and size and its window's start and count to the wrapper, which computes
the window and reads the buffer in place.  A read and a `sys` command with a buffer take the
buffer as a `ret` of its variable takes it, which moves an owned buffer that dies there and copies
it otherwise, store its root and size at `base`, and run the call with the buffer as variable 0,
which the call consumes. -/
def Command.codeWith (calls : List Call) (source : Wasm.Module) (h : Nat) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) (pool : Bytes.LiteralPool) :
    {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Program
  | _, _, .unit => []
  | _, _, .ret (type := type) value =>
    Relocation.programWith calls (value.code (pool := pool) h slots base live ++
      coerceCode h type (value.mode (slots.map Slot.mode)) .owned base)
  | _, _, .bind (intermediate := .unit) first next =>
    first.codeWith calls (pool := pool) source h slots base (fun i => live i || next.uses i) ++
      next.codeWith calls (pool := pool) source h slots base live
  | _, _, .bind (intermediate := .value type) first next =>
    first.codeWith calls (pool := pool) source h slots (base + type.width)
        (fun i => live i || next.uses (i + 1)) ++
      storeCode h base type.types ++
      (if next.uses 0 = false then Relocation.programWith calls (releaseCode type base) else []) ++
      next.codeWith calls (pool := pool) source h (⟨base, .owned⟩ :: slots) (base + type.width)
        (shift 1 live)
  | context, result, .ite condition yes no =>
    let mid := fun i => live i || yes.uses i || no.uses i
    Relocation.programWith calls (condition.code (pool := pool) h slots base mid) ++
      [.eqzI64, .iff 0 0
        (Relocation.programWith calls (releaseWhere context slots
            (fun i => mid i && !(live i || no.uses i))) ++
          no.codeWith calls (pool := pool) source h slots (base + result.width) live ++
          storeCode h base result.types)
        (Relocation.programWith calls (releaseWhere context slots
            (fun i => mid i && !(live i || yes.uses i))) ++
          yes.codeWith calls (pool := pool) source h slots (base + result.width) live ++
          storeCode h base result.types) [] []] ++
      loadCode h base result.types
  | context, _, .call (signature := signature) callee args =>
    let all := fun i => live i || argsAny fun j => (args j).usesFast i
    let kept := fun i => all i &&
      !(argsAny fun j => signature.callMoves slots live args j && (args j).usesFast i)
    [.localGet 0, .constI64 1, .addI64] ++
      argsCode (fun i => Relocation.programWith calls (
        if (signature.params.get i).scalar then (args i).code (pool := pool) h slots base all
        else if signature.mode i = .owned then (args i).ownedCode h slots base kept
        else (args i).placeCode h slots)) ++
      [.call (Wrappers.effectIndexWith calls source callee.index)] ++
      Relocation.programWith calls (releaseWhere context slots (fun i => kept i && !live i))
  | _, _, .read buffer start count =>
    Relocation.programWith calls ((Expr.var (S := pureSigs) buffer).code (pool := pool) h slots
        (base + Ty.bytes.width) (sysTakeLive live [start, count] []) ++
      coerceCode h .bytes ((Expr.var (S := pureSigs) buffer).mode (slots.map Slot.mode)) .owned
        (base + Ty.bytes.width)) ++
      storeCode h base Ty.bytes.types ++
      readFillCode (Wrappers.readIndexWith calls source) base (slots.getD start.index default).loc
        (slots.getD count.index default).loc (base + Ty.bytes.width)
  | _, _, .readAll limit =>
    Relocation.programWith calls (limit.code (pool := pool) h slots base live) ++ readAllCodeWith calls base
  | context, _, .write output buffer start count =>
    [.localGet (slots.getD buffer.index default).loc,
     .localGet ((slots.getD buffer.index default).loc + 1),
     .localGet (slots.getD start.index default).loc,
     .localGet (slots.getD count.index default).loc,
     .call (match output with
      | .stdout => Wrappers.stdoutIndexWith calls source
      | .stderr => Wrappers.stderrIndexWith calls source)] ++
      Relocation.programWith calls (releaseWhere context slots (fun i =>
        (i == buffer.index || (i == start.index || i == count.index)) && !live i))
  | _, _, .exit code =>
    Relocation.programWith calls (code.code (pool := pool) h slots base live) ++
      [.localSet base] ++ exitCode base
  | context, _, .loop (type := type) count initial test step =>
    let used := fun i => test.uses (i + 2) || step.uses (i + 2)
    let all := fun i => live i || used i
    let captured := slots.map fun slot => { slot with mode := .borrowed }
    let state := base + 2
    let scratch := state + type.width
    Relocation.programWith calls (count.code (pool := pool) h slots base
        (fun i => all i || initial.usesFast i)) ++
      [.localSet base] ++
      Relocation.programWith calls (initial.code (pool := pool) h slots (base + 1) all ++
        coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1)) ++
      storeCode h state type.types ++ [.constI64 0, .localSet (base + 1),
        .block 0 0 [.loop 0 0
          ([.localGet (base + 1), .localGet base, .geUI64, .br_if 1] ++
            Relocation.programWith calls (test.code (pool := pool) h
              (⟨state, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: captured) scratch
              (fun i => i == 0 || shift 2 all i)) ++
            [.eqzI64, .br_if 1] ++
            (if step.uses 0 = false then Relocation.programWith calls (releaseCode type state) else []) ++
            step.codeWith calls (pool := pool) source h
              (⟨state, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: captured) scratch (shift 2 all) ++
            storeCode h state type.types ++
            [.localGet (base + 1), .constI64 1, .addI64, .localSet (base + 1), .br 0]) [] []]
          [] []] ++
      Relocation.programWith calls (releaseWhere context slots (fun i => used i && !live i)) ++
      loadCode h state type.types
  | context, _, .sys operation form args inputs buffers =>
    match buffers with
    | [] =>
      sysInputsCodeWith calls operation form
          (args.map fun arg => (slots.getD arg.index default).loc)
          (inputs.map fun input => (slots.getD input.index default).loc) [] base ++
        Relocation.programWith calls (releaseWhere context slots
          (fun i => (inputs.any fun input => i == input.index) && !live i))
    | buffer :: _ =>
      Relocation.programWith calls ((Expr.var (S := pureSigs) buffer).code (pool := pool) h slots
          (base + Ty.bytes.width) (sysTakeLive live args inputs) ++
        coerceCode h .bytes ((Expr.var (S := pureSigs) buffer).mode (slots.map Slot.mode)) .owned
          (base + Ty.bytes.width)) ++
        storeCode h base Ty.bytes.types ++
        sysInputsCodeWith calls operation form
          (args.map fun arg => (slots.getD arg.index default).loc)
          (inputs.map fun input => (slots.getD input.index default).loc) [base]
          (base + Ty.bytes.width) ++
        Relocation.programWith calls (releaseWhere (.bytes :: context) (⟨base, .owned⟩ :: slots)
          (fun i => (inputs.any fun input => i == input.index + 1) && !shift 1 live i))
  | _, _, .letPair (first := first) (second := second) pair body =>
    let mode := (Expr.var (S := pureSigs) pair).mode (slots.map Slot.mode)
    Relocation.programWith calls ((Expr.var (S := pureSigs) pair).code (pool := pool) h slots
        (base + first.width + second.width) (fun i => live i || body.uses (i + 2))) ++
      storeCode h (base + first.width) second.types ++ storeCode h base first.types ++
      Relocation.programWith calls (letPairReleaseCode first second mode base (body.uses 1)
        (body.uses 0)) ++
      body.codeWith calls (pool := pool) source h
        (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) (base + first.width + second.width)
        (shift 2 live)

/-- `Command.codeWith` with the variables live after the command as a bitmask, together with the
command's `useMask`, in one pass: a command with subcommands computes its masks from theirs, its
expressions take their code from `Expr.codeMask`, and each release is the `releaseMask` of the
variables that die there.  `.unit` and `.read`, which neither hold an expression nor release, are
their `codeWith` under `live.testBit`.  The variables live after a loop's step include those that
the step reads, since the step runs again, so the loop computes the step's mask before the step's
code.  `Command.codeMask_eq` equates the two, and `EffectFunc.functionWith` calls this one. -/
def Command.codeMask (calls : List Call) (source : Wasm.Module) (h : Nat) (slots : List Slot)
    (base : Nat) (live : Nat) (pool : Bytes.LiteralPool) :
    {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Program × Nat
  | _, _, command@.unit
  | _, _, command@(.read _ _ _) =>
    (command.codeWith calls (pool := pool) source h slots base live.testBit, command.useMask)
  | _, _, .ret (type := type) value =>
    (Relocation.programWith calls (value.codeMask h slots base live pool ++
        coerceCode h type (value.mode (slots.map Slot.mode)) .owned base),
      value.useMask)
  | _, _, .bind (intermediate := .unit) first next =>
    let after := next.codeMask calls source h slots base live pool
    let before := first.codeMask calls source h slots base (live ||| after.2) pool
    (before.1 ++ after.1, before.2 ||| after.2)
  | _, _, .bind (intermediate := .value type) first next =>
    let after := next.codeMask calls source h (⟨base, .owned⟩ :: slots) (base + type.width)
      (live <<< 1) pool
    let before := first.codeMask calls source h slots (base + type.width)
      (live ||| after.2 >>> 1) pool
    (before.1 ++ storeCode h base type.types ++
        (if after.2.testBit 0 = false then Relocation.programWith calls (releaseCode type base)
          else []) ++
        after.1,
      before.2 ||| after.2 >>> 1)
  | context, result, .ite condition yes no =>
    let yesCode := yes.codeMask calls source h slots (base + result.width) live pool
    let noCode := no.codeMask calls source h slots (base + result.width) live pool
    let mid := live ||| yesCode.2 ||| noCode.2
    (Relocation.programWith calls (condition.codeMask h slots base mid pool) ++
        [.eqzI64, .iff 0 0
          (Relocation.programWith calls (releaseMask context slots
              (maskDiff mid (live ||| noCode.2))) ++
            noCode.1 ++ storeCode h base result.types)
          (Relocation.programWith calls (releaseMask context slots
              (maskDiff mid (live ||| yesCode.2))) ++
            yesCode.1 ++ storeCode h base result.types) [] []] ++
        loadCode h base result.types,
      condition.useMask ||| yesCode.2 ||| noCode.2)
  | context, _, .call (signature := signature) callee args =>
    let all := live ||| argsMask fun j => (args j).useMask
    let kept := maskDiff all (argsMask fun j =>
      maskIf (signature.callMoves slots live.testBit args j) (args j).useMask)
    ([.localGet 0, .constI64 1, .addI64] ++
        argsCode (fun i => Relocation.programWith calls (
          if (signature.params.get i).scalar then (args i).codeMask h slots base all pool
          else if signature.mode i = .owned then (args i).ownedCode h slots base kept.testBit
          else (args i).placeCode h slots)) ++
        [.call (Wrappers.effectIndexWith calls source callee.index)] ++
        Relocation.programWith calls (releaseMask context slots (maskDiff kept live)),
      argsMask fun i => (args i).useMask)
  | _, _, .readAll limit =>
    (Relocation.programWith calls (limit.codeMask h slots base live pool) ++
        readAllCodeWith calls base,
      limit.useMask)
  | context, _, .write output buffer start count =>
    ([.localGet (slots.getD buffer.index default).loc,
        .localGet ((slots.getD buffer.index default).loc + 1),
        .localGet (slots.getD start.index default).loc,
        .localGet (slots.getD count.index default).loc,
        .call (match output with
          | .stdout => Wrappers.stdoutIndexWith calls source
          | .stderr => Wrappers.stderrIndexWith calls source)] ++
        Relocation.programWith calls (releaseMask context slots
          (maskDiff (1 <<< buffer.index ||| (1 <<< start.index ||| 1 <<< count.index)) live)),
      1 <<< buffer.index ||| (1 <<< start.index ||| 1 <<< count.index))
  | _, _, .exit code =>
    (Relocation.programWith calls (code.codeMask h slots base live pool) ++
        [.localSet base] ++ exitCode base,
      code.useMask)
  | context, _, .loop (type := type) count initial test step =>
    let used := test.useMask >>> 2 ||| step.useMask >>> 2
    let all := live ||| used
    let captured := slots.map fun slot => { slot with mode := .borrowed }
    let state := base + 2
    let scratch := state + type.width
    (Relocation.programWith calls (count.codeMask h slots base (all ||| initial.useMask) pool) ++
        [.localSet base] ++
        Relocation.programWith calls (initial.codeMask h slots (base + 1) all pool ++
          coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1)) ++
        storeCode h state type.types ++ [.constI64 0, .localSet (base + 1),
          .block 0 0 [.loop 0 0
            ([.localGet (base + 1), .localGet base, .geUI64, .br_if 1] ++
              Relocation.programWith calls (test.codeMask h
                (⟨state, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: captured) scratch
                (1 ||| all <<< 2) pool) ++
              [.eqzI64, .br_if 1] ++
              (if step.useMask.testBit 0 = false then
                Relocation.programWith calls (releaseCode type state) else []) ++
              (step.codeMask calls source h
                (⟨state, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: captured) scratch (all <<< 2)
                pool).1 ++
              storeCode h state type.types ++
              [.localGet (base + 1), .constI64 1, .addI64, .localSet (base + 1), .br 0]) [] []]
            [] []] ++
        Relocation.programWith calls (releaseMask context slots (maskDiff used live)) ++
        loadCode h state type.types,
      count.useMask ||| initial.useMask ||| test.useMask >>> 2 ||| step.useMask >>> 2)
  | context, _, .sys operation form args inputs buffers =>
    (match buffers with
      | [] =>
        sysInputsCodeWith calls operation form
            (args.map fun arg => (slots.getD arg.index default).loc)
            (inputs.map fun input => (slots.getD input.index default).loc) [] base ++
          Relocation.programWith calls
            (releaseMask context slots (maskDiff (varsMask inputs) live))
      | buffer :: _ =>
        Relocation.programWith calls ((Expr.var (S := pureSigs) buffer).code (pool := pool) h
            slots (base + Ty.bytes.width) (sysTakeLive live.testBit args inputs) ++
          coerceCode h .bytes ((Expr.var (S := pureSigs) buffer).mode (slots.map Slot.mode))
            .owned (base + Ty.bytes.width)) ++
          storeCode h base Ty.bytes.types ++
          sysInputsCodeWith calls operation form
            (args.map fun arg => (slots.getD arg.index default).loc)
            (inputs.map fun input => (slots.getD input.index default).loc) [base]
            (base + Ty.bytes.width) ++
          Relocation.programWith calls (releaseMask (.bytes :: context) (⟨base, .owned⟩ :: slots)
            (maskDiff (varsMask inputs <<< 1) (live <<< 1))),
      varsMask buffers ||| (varsMask inputs ||| varsMask args))
  | _, _, .letPair (first := first) (second := second) pair body =>
    let mode := (Expr.var (S := pureSigs) pair).mode (slots.map Slot.mode)
    let bodyCode := body.codeMask calls source h
      (⟨base + first.width, mode⟩ :: ⟨base, mode⟩ :: slots) (base + first.width + second.width)
      (live <<< 2) pool
    (Relocation.programWith calls ((Expr.var (S := pureSigs) pair).code (pool := pool) h slots
          (base + first.width + second.width) (live ||| bodyCode.2 >>> 2).testBit) ++
        storeCode h (base + first.width) second.types ++ storeCode h base first.types ++
        Relocation.programWith calls (letPairReleaseCode first second mode base
          (bodyCode.2.testBit 1) (bodyCode.2.testBit 0)) ++
        bodyCode.1,
      1 <<< pair.index ||| bodyCode.2 >>> 2)

theorem Command.codeMask_eq (calls : List Call) (source : Wasm.Module) (h : Nat)
    (pool : Bytes.LiteralPool) (command : Command pureSigs effectSigs context result) :
    ∀ (slots : List Slot) (base live : Nat),
      command.codeMask calls source h slots base live pool =
        (command.codeWith calls (pool := pool) source h slots base live.testBit,
          command.useMask) := by
  induction command with
  | unit | read => intro _ _ _; rfl
  | ret value | readAll value | exit value =>
    intro slots base live
    simp only [Command.codeMask, Command.codeWith, Command.useMask, Expr.codeMask_eq]
  | call callee args =>
    intro slots base live
    simp only [Command.codeMask, Command.codeWith, Command.useMask, Expr.codeMask_eq,
      releaseMask_eq, testBit_maskDiff_eq, testBit_maskIf_eq, testBit_or_eq, testBit_argsMask_eq,
      Expr.usesFast]
  | write output buffer start count =>
    intro slots base live
    cases output <;>
      simp only [Command.codeMask, Command.codeWith, Command.useMask, releaseMask_eq,
        testBit_maskDiff_eq, testBit_or_eq, testBit_one_shiftLeft_eq]
  | sys operation form args inputs buffers =>
    intro slots base live
    cases buffers with
    | nil =>
      simp only [Command.codeMask, Command.codeWith, Command.useMask, releaseMask_eq,
        testBit_maskDiff_eq, testBit_varsMask_eq]
    | cons buffer rest =>
      simp only [Command.codeMask, Command.codeWith, Command.useMask, releaseMask_eq,
        testBit_maskDiff_eq, testBit_varsMask_shiftLeft_one_eq]
      simp only [testBit_shiftLeft_eq]
  | @bind context intermediate result first next firstIh nextIh =>
    intro slots base live
    cases intermediate <;>
      simp only [Command.codeMask, Command.codeWith, Command.useMask, ResultTy.bindCount,
        Nat.shiftRight_zero, firstIh, nextIh, testBit_or_eq, testBit_shiftRight_eq,
        testBit_shiftLeft_eq, Command.useMask_testBit]
  | ite condition yes no yesIh noIh =>
    intro slots base live
    simp only [Command.codeMask, Command.codeWith, Command.useMask, yesIh, noIh,
      Expr.codeMask_eq, releaseMask_eq, testBit_maskDiff_eq, testBit_or_eq,
      Command.useMask_testBit]
  | loop count initial test step stepIh =>
    intro slots base live
    simp only [Command.codeMask, Command.codeWith, Command.useMask, stepIh, Expr.codeMask_eq,
      releaseMask_eq, testBit_maskDiff_eq, testBit_or_eq, testBit_shiftRight_eq,
      testBit_shiftLeft_eq, testBit_one_eq, Command.useMask_testBit, Expr.useMask_testBit,
      Expr.usesFast_eq]
  | letPair pair body bodyIh =>
    intro slots base live
    simp only [Command.codeMask, Command.codeWith, Command.useMask, bodyIh, testBit_or_eq,
      testBit_shiftRight_eq, testBit_shiftLeft_eq, Command.useMask_testBit]

/-- Command code of a module without imported calls. -/
def Command.code (source : Wasm.Module) (h : Nat) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) (pool : Bytes.LiteralPool) :
    {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Program :=
  Command.codeWith [] source h slots base live pool

def EffectFunc.type (function : EffectFunc pureSigs effectSigs) : FuncType :=
  { params := codeParams function.params true
    results := function.result.types }

def EffectFunc.positions (function : EffectFunc pureSigs effectSigs) : Nat :=
  1 + widthSum function.params + function.body.width

def EffectFunc.functionWith (calls : List Call) (source : Wasm.Module) (function : EffectFunc pureSigs effectSigs)
    (typeIdx : Nat) (pool : Bytes.LiteralPool) : Wasm.Function :=
  let slots := paramSlots function.params function.modes 1
  let h := function.positions
  let body := function.body.codeMask calls source h slots (1 + widthSum function.params) 0 pool
  { params := codeParams function.params true
    locals := List.replicate function.body.width .i64 ++
      List.replicate h .f64 ++ List.replicate h .f32
    body := guardCode ++ paramCopyCode h 1 (function.params.flatMap Ty.types) ++
      Relocation.programWith calls (releaseWhere function.params slots
        (fun i => !body.2.testBit i)) ++
      body.1
    results := function.result.types
    typeIdx := some typeIdx }

theorem EffectFunc.functionWith_body (calls : List Call) (source : Wasm.Module)
    (function : EffectFunc pureSigs effectSigs) (typeIdx : Nat) (pool : Bytes.LiteralPool) :
    (function.functionWith calls source typeIdx pool).body =
      guardCode ++ paramCopyCode function.positions 1 (function.params.flatMap Ty.types) ++
        Relocation.programWith calls (releaseWhere function.params
          (paramSlots function.params function.modes 1) (fun i => !function.body.uses i)) ++
        function.body.codeWith calls (pool := pool) source function.positions
          (paramSlots function.params function.modes 1) (1 + widthSum function.params)
          (fun _ => false) := by
  simp only [EffectFunc.functionWith, Command.codeMask_eq, Command.useMask_testBit,
    testBit_zero_eq]

def EffectFunc.function (source : Wasm.Module) (function : EffectFunc pureSigs effectSigs)
    (typeIdx : Nat) (pool : Bytes.LiteralPool) : Wasm.Function :=
  EffectFunc.functionWith [] source function typeIdx pool

end Verified.Wasi
