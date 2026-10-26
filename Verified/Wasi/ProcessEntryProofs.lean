import Verified.Wasi.ProcessIteration
import Verified.Wasi.ExitStack

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def ProcessEntry.beginAction (entry : ProcessEntry effectSigs) (functions : EffectFuns effectSigs) :
    Action (ProcessStep entry.state.denote) :=
  Action.bind (functions.get entry.begin .nil) fun result =>
    .pure (processNative entry.state result)

inductive ProcessCommandExec {World σ : Type} (host : Host World)
    (begin : Action (ProcessStep σ)) (process : Process σ) :
    World → List Event → Outcome Unit → World → Prop where
  | next {world first current middle rest outcome after last result final}
      (started : LeanExe.Wasi.Exec host begin world first (.returned current) middle)
      (continued : Process.Continue host process current middle rest outcome after)
      (finished : LeanExe.Wasi.Continue host (fun status => Action.exit (α := Unit) status)
        after outcome last result final) :
      ProcessCommandExec host begin process world (first ++ rest ++ last) result final
  | beginExit {world trace status final}
      (execution : LeanExe.Wasi.Exec host begin world trace (.exited status) final) :
      ProcessCommandExec host begin process world trace (.exited status) final
  | beginTrap {world trace message final}
      (execution : LeanExe.Wasi.Exec host begin world trace (.trapped message) final) :
      ProcessCommandExec host begin process world trace (.trapped message) final

inductive ProcessCommandPrefix {World σ : Type} (host : Host World)
    (begin : Action (ProcessStep σ)) (process : Process σ) :
    World → List Event → Action (ProcessStep σ) → World → Prop where
  | begin {world trace residual final}
      (progress : LeanExe.Wasi.Prefix host begin world trace residual final) :
      ProcessCommandPrefix host begin process world trace residual final
  | next {world first current middle rest residual final}
      (started : LeanExe.Wasi.Exec host begin world first (.returned current) middle)
      (progress : Process.Pending host process current middle rest residual final) :
      ProcessCommandPrefix host begin process world (first ++ rest) residual final

inductive ProcessEntryResult {World σ : Type} (host : Host World)
    (begin : Action (ProcessStep σ)) (process : Process σ) (world : World) :
    Continuation World → Prop where
  | terminal (final : Store World) (trace : List Event) (outcome : Outcome Unit) (message : String)
      (execution : ProcessCommandExec host begin process world trace outcome final.host)
      (terminal : TerminalMessage message outcome) :
      ProcessEntryResult host begin process world (.Trap final message)
  | resource (final : Store World) (trace : List Event) (residual : Action (ProcessStep σ))
      (progress : ProcessCommandPrefix host begin process world trace residual final.host) :
      ProcessEntryResult host begin process world (.Trap final "unreachable")

inductive ProcessBeginResult {World : Type} (host : Host World) (target : Wasm.Module)
    (state : Ty) (pool : Bytes.LiteralPool) (base : UInt64)
    (begin : Action (ProcessStep state.denote))
    (world : Observed World) : Continuation (Observed World) → Prop where
  | returned (current : ProcessStep state.denote) (final : Store (Observed World))
      (after : Locals) (trace : List Event)
      (execution : LeanExe.Wasi.Exec (observedHost host) begin world trace (.returned current) final.host)
      (stored : ProcessStored target state pool base current final after) :
      ProcessBeginResult host target state pool base begin world (.Fallthrough final after)
  | terminal (final : Store (Observed World)) (trace : List Event)
      (outcome : Outcome (ProcessStep state.denote)) (message : String)
      (execution : LeanExe.Wasi.Exec (observedHost host) begin world trace outcome final.host)
      (terminal : TerminalMessage message outcome) :
      ProcessBeginResult host target state pool base begin world (.Trap final message)
  | resource (final : Store (Observed World)) (trace : List Event)
      (residual : Action (ProcessStep state.denote))
      (progress : LeanExe.Wasi.Prefix (observedHost host) begin world trace residual final.host) :
      ProcessBeginResult host target state pool base begin world (.Trap final "unreachable")

/-- `begin`, the store of its result, and the result's compaction, from locals whose position
`processAux` holds the heap top `base`. -/
theorem wp_process_begin {World : Type} {source target : Wasm.Module} {host : Host World}
    {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {functions : EffectFuns effectSigs} {pool : Bytes.LiteralPool}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)}
    {heap : Heap} {locals : Locals} {function : Wasm.Function}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (compactable : entry.state.compactable = true)
    (compactForm : Encoding.ProgramForm (processCompaction entry.state))
    (compactClosed :
      Relocation.programClosed source.funcs.length (processCompaction entry.state) = true)
    (spec : EffectSpec target ⟨entry.beginName, [], [], .value (processResultTy entry.state)⟩
      (Wrappers.effectIndex source entry.begin.index) (functions.get entry.begin) pool)
    (noImport : target.imports[Wrappers.effectIndex source entry.begin.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndex source entry.begin.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (params : locals.params = []) (positions : locals.positions = processPositions entry.state)
    (baseLocal : locals.get (processAux entry.state) = some (.i64 heap.top)) :
    wp target ([.constI64 0, .call (Wrappers.effectIndex source entry.begin.index)] ++
      (storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
        Relocation.program (processCompaction entry.state)))
      (ProcessBeginResult host target entry.state pool heap.top (entry.beginAction functions)
        initial.host)
      initial locals targetHost := by
  let Q := ProcessBeginResult host target entry.state pool heap.top (entry.beginAction functions)
    initial.host
  have poolBelow := static.below
  have call := wp_effect_helper (locals := locals) (values := locals.values) (depth := 0)
    (signature := ⟨entry.beginName, [], [], .value (processResultTy entry.state)⟩)
    (params := []) (args := (Env.nil : Env []))
    (rest := storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
      (Relocation.program (processCompaction entry.state) ++ []))
    (Q := Q) spec noImport lookup (by simpa [widthSum] using arity) valid at_ rfl
    Separate.nil ⟨static, fun _ _ => Apart.nil⟩ (by intro _ member; exact nomatch member) cap
    (fun (value : (processResultTy entry.state).denote) finalHeap final words trace execution step rep => by
      have resultRep : (processResultTy entry.state).Rep .owned finalHeap
          (PureTransport.erase final) words value := rep
      have preserved := static.step step (fun region member => ⟨Apart.nil, poolScratch region member⟩)
      let current := processNative entry.state value
      have nativeExecution : LeanExe.Wasi.Exec (observedHost host) (entry.beginAction functions)
          initial.host trace (.returned current) final.host := by
        simpa only [ProcessEntry.beginAction, List.append_nil] using
          execution.bind (next := fun result => Action.pure (processNative entry.state result))
            (LeanExe.Wasi.Exec.pure final.host current)
      have nativeMemory : ProcessMemory (processResultTy entry.state) pool finalHeap
          (PureTransport.erase final) words (processValue entry.state current) := by
        change ProcessMemory (processResultTy entry.state) pool finalHeap (PureTransport.erase final)
          words (processValue entry.state (processNative entry.state value))
        rw [processValue_native entry.state value]
        exact ⟨step.at_, resultRep, preserved.1, preserved.2⟩
      have grown := step.top_le at_ free ⟨Apart.nil, scratch_apart_above _⟩
      refine wp_process_store_compact runtime layout profile compactable compactForm compactClosed
        nativeMemory grown baseLocal at_.base poolBelow params positions
        (by rw [step.cap target]; exact cap) (fun _ ended sameHost => ?_)
        fun ended after sameHost _ stored _ => ?_
      · refine ProcessBeginResult.resource ended trace (.pure current) ?_
        rw [sameHost]
        exact LeanExe.Wasi.Exec.returned_prefix _ nativeExecution
      · rw [wp_nil]
        exact ProcessBeginResult.returned current ended after trace
          (by simpa only [sameHost] using nativeExecution) stored)
    (fun final trace outcome message execution terminal => by
      cases outcome with
      | returned value => exact terminal.elim
      | exited status =>
          refine ProcessBeginResult.terminal final trace (.exited status) message ?_ terminal
          simpa only [ProcessEntry.beginAction, List.append_nil] using
            execution.bind (next := fun result => Action.pure (processNative entry.state result))
              ⟨rfl, rfl, rfl⟩
      | trapped cause =>
          refine ProcessBeginResult.terminal final trace (.trapped cause) message ?_ terminal
          simpa only [ProcessEntry.beginAction, List.append_nil] using
            execution.bind (next := fun result => Action.pure (processNative entry.state result))
              ⟨rfl, rfl, rfl⟩)
    (fun final trace residual progress =>
      ProcessBeginResult.resource final trace
        (Action.bind residual fun result => Action.pure (processNative entry.state result)) progress.bind)
  change wp target (.constI64 0 :: .call (Wrappers.effectIndex source entry.begin.index) ::
    (storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
      Relocation.program (processCompaction entry.state))) Q initial locals targetHost
  simp only [wp_constI64_cons]
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_nil] using call

theorem pwp_process_loop_exit {World : Type} {source target : Wasm.Module} {host : Host World}
    {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs} {pool : Bytes.LiteralPool}
    {begin : Action (ProcessStep entry.state.denote)} {process : Process entry.state.denote}
    {base : UInt64}
    {world : Observed World} {first : List Event} {current : ProcessStep entry.state.denote}
    {middle : Store (Observed World)} {locals : Locals} {targetHost : HostEnv (Observed World)}
    (imports : target.imports = ABI.imports)
    (valid : targetHost.Satisfies target (hostSpec host))
    (started : LeanExe.Wasi.Exec (observedHost host) begin world first (.returned current) middle.host)
    (stored : ProcessStored target entry.state pool base current middle locals)
    (iteration : ∀ current store locals,
      ProcessStored target entry.state pool base current store locals →
      pwp target (entry.iteration source)
        (ProcessIterationResult (observedHost host) process current store.host
          (ProcessStored target entry.state pool base) locals.values) store locals targetHost) :
    pwp target ([.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []] ++
      [.localGet 1, .wrapI64, .call 2, .unreachable])
      (ProcessEntryResult (observedHost host) begin process world) middle locals targetHost := by
  let Q := ProcessEntryResult (observedHost host) begin process world
  have block := pwp_process_block (ProcessStored target entry.state pool base) stored iteration
  refine pwp_append (module := target)
    (first := [.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []])
    (rest := [.localGet 1, .wrapI64, .call 2, .unreachable]) (post := Q)
    (store := middle) (locals := locals) (host := targetHost) ?_
  exact block.conseq (fun continuation classification => by
    cases classification with
    | stopped next final after trace history stopped rep =>
        apply wp.pwp
        simp only [wp_localGet_cons, Locals.get_values, rep.status]
        refine wp_exit_stack imports valid ?_ ?_
        · intro ended accepted _
          have finished : LeanExe.Wasi.Continue (observedHost host)
              (fun status => Action.exit (α := Unit) status) final.host (.returned next.status)
              [.exit (exitStatus next.status)] (.exited (exitStatus next.status)) ended.host := by
            change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) next.status)
              final.host [.exit (exitStatus next.status)] (.exited (exitStatus next.status)) ended.host
            exact LeanExe.Wasi.Exec.exit accepted
          exact ProcessEntryResult.terminal ended
            (first ++ trace ++ [.exit (exitStatus next.status)])
            (.exited (exitStatus next.status)) exitTrap
            (ProcessCommandExec.next started (history.done stopped) finished) rfl
        · intro ended message rejected _
          have finished : LeanExe.Wasi.Continue (observedHost host)
              (fun status => Action.exit (α := Unit) status) final.host (.returned next.status)
              [.exitTrap (exitStatus next.status) message] (.trapped message) ended.host := by
            change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) next.status)
              final.host [.exitTrap (exitStatus next.status) message] (.trapped message) ended.host
            exact LeanExe.Wasi.Exec.exitTrap rejected
          exact ProcessEntryResult.terminal ended
            (first ++ trace ++ [.exitTrap (exitStatus next.status) message]) (.trapped message) message
            (ProcessCommandExec.next started (history.done stopped) finished) rfl
    | terminal final trace outcome message nativeExecution terminal =>
        cases outcome with
        | returned value => exact terminal.elim
        | exited status =>
            exact ProcessEntryResult.terminal final (first ++ trace ++ []) (.exited status) message
              (ProcessCommandExec.next started nativeExecution ⟨rfl, rfl, rfl⟩) terminal
        | trapped cause =>
            exact ProcessEntryResult.terminal final (first ++ trace ++ []) (.trapped cause) message
              (ProcessCommandExec.next started nativeExecution ⟨rfl, rfl, rfl⟩) terminal
    | resource final trace residual progress =>
        exact ProcessEntryResult.resource final (first ++ trace) residual
          (ProcessCommandPrefix.next started progress))

/-- The value of the heap top saved in local `processAux` at the start of `_start`. -/
theorem wp_saveBase {World : Type} {target : Wasm.Module} {heap : Heap}
    {store : Store (Observed World)} {locals : Locals} {index : Nat} {rest : Program}
    {Q : Assertion (Observed World)} {targetHost : HostEnv (Observed World)}
    (at_ : heap.At (PureTransport.erase store)) (low : locals.params.length ≤ index)
    (high : index < locals.params.length + locals.locals.length)
    (next : wp target rest Q store (setLocal { locals with values := locals.values } index
      (.i64 heap.top)) targetHost) :
    wp target (.globalGet 0 :: .localSet index :: rest) Q store locals targetHost := by
  have globals : store.globals.globals = heap.globals := at_.globals
  simp only [wp_globalGet_cons, globals, Heap.globals, List.getElem?_cons_zero]
  exact wp_localSet_local low high next

theorem pwp_process_entry_body {World : Type} {source target : Wasm.Module} {host : Host World}
    {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {functions : EffectFuns effectSigs} {pool : Bytes.LiteralPool}
    {process : Process entry.state.denote} {typeIdx : Nat}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)}
    {heap : Heap} {function : Wasm.Function}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (compactable : entry.state.compactable = true)
    (compactForm : Encoding.ProgramForm (processCompaction entry.state))
    (compactClosed :
      Relocation.programClosed source.funcs.length (processCompaction entry.state) = true)
    (spec : EffectSpec target ⟨entry.beginName, [], [], .value (processResultTy entry.state)⟩
      (Wrappers.effectIndex source entry.begin.index) (functions.get entry.begin) pool)
    (noImport : target.imports[Wrappers.effectIndex source entry.begin.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndex source entry.begin.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1)
    (imports : target.imports = ABI.imports)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (iteration : ∀ current store locals,
      ProcessStored target entry.state pool heap.top current store locals →
      pwp target (entry.iteration source)
        (ProcessIterationResult (observedHost host) process current store.host
          (ProcessStored target entry.state pool heap.top) locals.values) store locals targetHost) :
    pwp target (entry.function source typeIdx).body
      (ProcessEntryResult (observedHost host) (entry.beginAction functions) process initial.host)
      initial ((entry.function source typeIdx).toLocals []) targetHost := by
  let locals := (entry.function source typeIdx).toLocals []
  let beginCode : Program := [.constI64 0, .call (Wrappers.effectIndex source entry.begin.index)] ++
    (storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
      Relocation.program (processCompaction entry.state))
  let tailCode : Program := [.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []] ++
    [.localGet 1, .wrapI64, .call 2, .unreachable]
  let Q := ProcessEntryResult (observedHost host) (entry.beginAction functions) process initial.host
  have positions : locals.positions = processPositions entry.state := by
    simp only [locals, ProcessEntry.function, Function.toLocals, Locals.positions,
      List.length_nil, List.length_map, List.length_append, List.length_replicate, Nat.zero_add]
    omega
  have params : locals.params = [] := rfl
  have total : processAux entry.state < locals.params.length + locals.locals.length := by
    have := Locals.lt_total (s := locals) (i := processAux entry.state)
      (by rw [positions]; simp only [processPositions]; omega)
    exact this
  have low : locals.params.length ≤ processAux entry.state := by rw [params]; exact Nat.zero_le _
  let saved := setLocal { locals with values := locals.values } (processAux entry.state)
    (.i64 heap.top)
  have low' : ({ locals with values := locals.values } : Locals).params.length ≤
      processAux entry.state := low
  have savedBase : saved.get (processAux entry.state) = some (.i64 heap.top) :=
    Locals.get_setLocal_same low' total
  have savedPositions : saved.positions = processPositions entry.state := by
    simp only [saved, Locals.positions_setLocal]; exact positions
  have began := wp_process_begin (locals := saved) runtime layout profile compactable compactForm
    compactClosed spec noImport lookup arity valid at_ free static poolScratch cap rfl
    savedPositions savedBase
  have composed : pwp target (beginCode ++ tailCode) Q initial saved targetHost := by
    refine pwp_append (module := target) (first := beginCode) (rest := tailCode) (post := Q)
      (store := initial) (locals := saved) (host := targetHost) ?_
    exact began.pwp.conseq (fun continuation classification => by
      cases classification with
      | returned current final after trace nativeExecution stored =>
          exact pwp_process_loop_exit imports valid nativeExecution stored iteration
      | terminal final trace outcome message nativeExecution terminal =>
          cases outcome with
          | returned value => exact terminal.elim
          | exited status =>
              exact ProcessEntryResult.terminal final trace (.exited status) message
                (ProcessCommandExec.beginExit nativeExecution) terminal
          | trapped cause =>
              exact ProcessEntryResult.terminal final trace (.trapped cause) message
                (ProcessCommandExec.beginTrap nativeExecution) terminal
      | resource final trace residual progress =>
          exact ProcessEntryResult.resource final trace residual (ProcessCommandPrefix.begin progress))
  have whole : pwp target ([.globalGet 0, .localSet (processAux entry.state)] ++
      (beginCode ++ tailCode)) Q initial locals targetHost := by
    refine pwp_append ?_
    apply wp.pwp
    refine wp_saveBase (rest := []) at_ low total ?_
    rw [wp_nil]
    exact composed
  simpa only [beginCode, tailCode, Q, locals, ProcessEntry.function, ProcessEntry.result,
    List.append_assoc, List.cons_append, List.nil_append] using whole

end Verified.Wasi
