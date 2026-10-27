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
    (state : Ty) (pool : Bytes.LiteralPool) (begin : Action (ProcessStep state.denote))
    (world : Observed World) : Continuation (Observed World) → Prop where
  | returned (current : ProcessStep state.denote) (final : Store (Observed World))
      (after : Locals) (trace : List Event)
      (execution : LeanExe.Wasi.Exec (observedHost host) begin world trace (.returned current) final.host)
      (stored : ProcessStored target state pool current final after) :
      ProcessBeginResult host target state pool begin world (.Fallthrough final after)
  | terminal (final : Store (Observed World)) (trace : List Event)
      (outcome : Outcome (ProcessStep state.denote)) (message : String)
      (execution : LeanExe.Wasi.Exec (observedHost host) begin world trace outcome final.host)
      (terminal : TerminalMessage message outcome) :
      ProcessBeginResult host target state pool begin world (.Trap final message)
  | resource (final : Store (Observed World)) (trace : List Event)
      (residual : Action (ProcessStep state.denote))
      (progress : LeanExe.Wasi.Prefix (observedHost host) begin world trace residual final.host) :
      ProcessBeginResult host target state pool begin world (.Trap final "unreachable")

theorem wp_process_begin {World : Type} {source target : Wasm.Module} {host : Host World}
    {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {functions : EffectFuns effectSigs} {pool : Bytes.LiteralPool}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)}
    {heap : Heap} {locals : Locals} {function : Wasm.Function}
    (spec : EffectSpec target ⟨entry.beginName, [], [], .value (processResultTy entry.state)⟩
      (Wrappers.effectIndex source entry.begin.index) (functions.get entry.begin) pool)
    (noImport : target.imports[Wrappers.effectIndex source entry.begin.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndex source entry.begin.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (params : locals.params = []) (positions : locals.positions = 2 * (processResultTy entry.state).width) :
    wp target ([.constI64 0, .call (Wrappers.effectIndex source entry.begin.index)] ++
      storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types)
      (ProcessBeginResult host target entry.state pool (entry.beginAction functions) initial.host)
      initial locals targetHost := by
  let Q := ProcessBeginResult host target entry.state pool (entry.beginAction functions) initial.host
  have call := wp_effect_helper (locals := locals) (values := locals.values) (depth := 0)
    (signature := ⟨entry.beginName, [], [], .value (processResultTy entry.state)⟩)
    (params := []) (args := (Env.nil : Env []))
    (rest := storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types) (Q := Q)
    spec noImport lookup (by simpa [widthSum] using arity) valid at_ rfl
    Separate.nil ⟨static, fun _ _ => Apart.nil⟩ (by intro _ member; exact nomatch member) cap
    (fun (value : (processResultTy entry.state).denote) finalHeap final words trace execution step rep => by
      have resultRep : (processResultTy entry.state).Rep .owned finalHeap
          (PureTransport.erase final) words value := rep
      have preserved := static.step step (fun region member => ⟨Apart.nil, poolScratch region member⟩)
      have memory : ProcessMemory (processResultTy entry.state) pool finalHeap
          (PureTransport.erase final) words value :=
        ⟨step.at_, resultRep, preserved.1, preserved.2⟩
      let current := processNative entry.state value
      have nativeExecution : LeanExe.Wasi.Exec (observedHost host) (entry.beginAction functions)
          initial.host trace (.returned current) final.host := by
        simpa only [ProcessEntry.beginAction, List.append_nil] using
          execution.bind (next := fun result => Action.pure (processNative entry.state result))
            (LeanExe.Wasi.Exec.pure final.host current)
      have nativeMemory : ProcessMemory (processResultTy entry.state) pool finalHeap (PureTransport.erase final)
          words (processValue entry.state current) := by
        change ProcessMemory (processResultTy entry.state) pool finalHeap (PureTransport.erase final)
          words (processValue entry.state (processNative entry.state value))
        rw [processValue_native entry.state value]
        exact memory
      simpa only [List.append_nil] using
        (wp_storeCode (rest := []) (Q := Q) words (2 * (processResultTy entry.state).width) 0
          (processResultTy entry.state).types locals locals.values
          resultRep.typed positions (by simp only [params, List.length_nil, Nat.le_refl])
          (by rw [Ty.types_length, positions]; omega)
          (fun after frame held _ => by
            rw [wp_nil]
            refine ProcessBeginResult.returned current final { after with values := locals.values }
              trace nativeExecution ?_
            exact ⟨⟨finalHeap, words, nativeMemory, held⟩,
              frame.params.trans params, frame.positions.trans positions,
              by rw [step.cap target]; exact cap⟩)))
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
    storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types)
      Q initial locals targetHost
  simp only [wp_constI64_cons]
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using call

theorem pwp_process_loop_exit {World : Type} {source target : Wasm.Module} {host : Host World}
    {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs} {pool : Bytes.LiteralPool}
    {begin : Action (ProcessStep entry.state.denote)} {process : Process entry.state.denote}
    {world : Observed World} {first : List Event} {current : ProcessStep entry.state.denote}
    {middle : Store (Observed World)} {locals : Locals} {targetHost : HostEnv (Observed World)}
    (imports : target.imports = ABI.imports)
    (valid : targetHost.Satisfies target (hostSpec host))
    (started : LeanExe.Wasi.Exec (observedHost host) begin world first (.returned current) middle.host)
    (stored : ProcessStored target entry.state pool current middle locals)
    (iteration : ∀ current store locals, ProcessStored target entry.state pool current store locals →
      pwp target (entry.iteration source)
        (ProcessIterationResult (observedHost host) process current store.host
          (ProcessStored target entry.state pool) locals.values) store locals targetHost) :
    pwp target ([.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []] ++
      [.localGet 1, .wrapI64, .call 2, .unreachable])
      (ProcessEntryResult (observedHost host) begin process world) middle locals targetHost := by
  let Q := ProcessEntryResult (observedHost host) begin process world
  have block := pwp_process_block (ProcessStored target entry.state pool) stored iteration
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

theorem pwp_process_entry_body {World : Type} {source target : Wasm.Module} {host : Host World}
    {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {functions : EffectFuns effectSigs} {pool : Bytes.LiteralPool}
    {process : Process entry.state.denote} {typeIdx : Nat}
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)}
    {heap : Heap} {function : Wasm.Function}
    (spec : EffectSpec target ⟨entry.beginName, [], [], .value (processResultTy entry.state)⟩
      (Wrappers.effectIndex source entry.begin.index) (functions.get entry.begin) pool)
    (noImport : target.imports[Wrappers.effectIndex source entry.begin.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndex source entry.begin.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1)
    (imports : target.imports = ABI.imports)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (iteration : ∀ current store locals, ProcessStored target entry.state pool current store locals →
      pwp target (entry.iteration source)
        (ProcessIterationResult (observedHost host) process current store.host
          (ProcessStored target entry.state pool) locals.values) store locals targetHost) :
    pwp target (entry.function source typeIdx).body
      (ProcessEntryResult (observedHost host) (entry.beginAction functions) process initial.host)
      initial ((entry.function source typeIdx).toLocals []) targetHost := by
  let locals := (entry.function source typeIdx).toLocals []
  let beginCode : Program := [.constI64 0, .call (Wrappers.effectIndex source entry.begin.index)] ++
    storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types
  let tailCode : Program := [.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []] ++
    [.localGet 1, .wrapI64, .call 2, .unreachable]
  let Q := ProcessEntryResult (observedHost host) (entry.beginAction functions) process initial.host
  have positions : locals.positions = 2 * (processResultTy entry.state).width := by
    simp only [locals, ProcessEntry.function, ProcessEntry.result, Function.toLocals, Locals.positions,
      List.length_nil, List.length_map, List.length_append, List.length_replicate, Nat.zero_add]
    omega
  have began := wp_process_begin (locals := locals) spec noImport lookup arity valid
    at_ static poolScratch cap rfl positions
  have composed : pwp target (beginCode ++ tailCode) Q initial locals targetHost := by
    refine pwp_append (module := target) (first := beginCode) (rest := tailCode) (post := Q)
      (store := initial) (locals := locals) (host := targetHost) ?_
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
  simpa only [beginCode, tailCode, Q, locals, ProcessEntry.function, ProcessEntry.result,
    List.append_assoc] using composed

end Verified.Wasi
