import Verified.Wasi.ProcessCompact
import Verified.Wasi.ProcessLoop
import Verified.Wasi.CallHelper

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem _root_.LeanExe.Pipeline.Heap.At.top_eq {heap other : Heap} {store : Store Unit}
    (first : heap.At store) (second : other.At store) : heap.top = other.top := by
  have same := first.globals.symm.trans second.globals
  simp only [Heap.globals, List.cons.injEq, Value.i64.injEq] at same
  exact same.1

/-- The store of a call's result over the current state, followed by the state's compaction. -/
theorem wp_process_store_compact {World : Type} {source target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {targetHost : HostEnv (Observed World)}
    {store : Store (Observed World)} {heap : Heap} {locals : Locals} {words : List Value}
    {value : ProcessStep state.denote} {rest : Program} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (compactable : state.compactable = true)
    (form : Encoding.ProgramForm (processCompaction state))
    (closed : Relocation.programClosed source.funcs.length (processCompaction state) = true)
    (memory : ProcessMemory (processResultTy state) pool heap (PureTransport.erase store) words
      (processValue state value))
    (baseTop : base.toNat ≤ heap.top.toNat)
    (baseLocal : locals.get (processAux state) = some (.i64 base)) (low : 4096 ≤ base.toNat)
    (poolBelow : ∀ region ∈ pool.regions, region.1 + region.2 ≤ base.toNat)
    (params : locals.params = []) (positions : locals.positions = processPositions state)
    (cap : (PureTransport.erase store).memoryCap target 0 ≤ 65535)
    (trap : ¬ roundWord heap.top.toNat + state.copyCost value.state ≤
        65536 * (PureTransport.erase store).memoryCap source 0 →
      ∀ final : Store (Observed World), final.host = store.host → Q (.Trap final "unreachable"))
    (next : ∀ final after, final.host = store.host →
      (PureTransport.erase final).memoryCaps = (PureTransport.erase store).memoryCaps →
      ProcessStored target state pool base value final after → after.values = locals.values →
      wp target rest Q final after targetHost) :
    wp target (storeCode (processPositions state) 0 (processResultTy state).types ++
        (Relocation.program (processCompaction state) ++ rest)) Q store
      { locals with values := words.reverse ++ locals.values } targetHost := by
  have hWidth : (processResultTy state).width ≤ processPositions state := by
    simp only [processPositions, processAux]; omega
  refine wp_storeCode words (processPositions state) 0 (processResultTy state).types locals
    locals.values memory.rep.typed positions (by rw [params]; exact Nat.zero_le _)
    (by rw [Ty.types_length, positions]; omega) fun after frame held above => ?_
  have baseAfter : ({ after with values := locals.values } : Locals).get (processAux state) =
      some (.i64 base) := by
    rw [Locals.get_values, (above (processAux state) (by rw [Ty.types_length]; rfl)
      (by rw [positions]; simp only [processPositions]; omega)).1]
    exact baseLocal
  exact wp_process_compact runtime layout profile compactable form closed memory held baseTop
    baseAfter low poolBelow (frame.params.trans params) (frame.positions.trans positions) cap
    trap fun final after' host caps stored values => next final after' host caps stored values

theorem wp_process_iteration {World : Type} {source target : Wasm.Module}
    {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {functions : EffectFuns effectSigs} {process : Process entry.state.denote}
    {host : Host World} {targetHost : HostEnv (Observed World)} {pool : Bytes.LiteralPool}
    {base : UInt64} {initial : Store (Observed World)} {locals : Locals}
    {current : ProcessStep entry.state.denote} {function : Wasm.Function}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (compactable : entry.state.compactable = true)
    (compactForm : Encoding.ProgramForm (processCompaction entry.state))
    (compactClosed :
      Relocation.programClosed source.funcs.length (processCompaction entry.state) = true)
    (spec : EffectSpec target
      ⟨entry.stepName, [entry.state], [.borrowed], .value (processResultTy entry.state)⟩
      (Wrappers.effectIndex source entry.step.index) (functions.get entry.step) pool)
    (noImport : target.imports[Wrappers.effectIndex source entry.step.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndex source entry.step.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1 + widthSum [entry.state])
    (valid : targetHost.Satisfies target (hostSpec host))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (stepMeaning : ∀ state, process.step state = entry.action functions state)
    (stored : ProcessStored target entry.state pool base current initial locals) :
    wp target (entry.iteration source)
      (ProcessIterationResult (observedHost host) process current initial.host
        (ProcessStored target entry.state pool base) locals.values) initial locals targetHost := by
  let Q := ProcessIterationResult (observedHost host) process current initial.host
    (ProcessStored target entry.state pool base) locals.values
  obtain ⟨heap, stateWords, memory, held, control, free, baseTop, _⟩ := stored.parts
  simp only [ProcessEntry.iteration, ProcessEntry.result, List.append_assoc,
    List.cons_append, List.nil_append, wp_localGet_cons, control, wp_eqzI64_cons]
  cases running : current.running with
  | false =>
      simpa [running, boolWord] using
        (ProcessIterationResult.stopped initial locals rfl running stored : Q (.Break 1 initial locals))
  | true =>
      let signature : EffectSig :=
        ⟨entry.stepName, [entry.state], [.borrowed], .value (processResultTy entry.state)⟩
      let args : Env [entry.state] := .cons current.state .nil
      have mode : signature.mode = fun _ => .borrowed := by
        funext index
        cases index with
        | zero =>
            change entry.state.paramMode .borrowed = .borrowed
            cases entry.state <;> rfl
        | succ index => rfl
      have takeWords : stateWords.take entry.state.width = stateWords := by
        rw [← memory.rep.length]
        exact List.take_length
      have moves : Env.moves (PureTransport.erase initial) signature.mode stateWords args = [] := by
        simp only [args, mode, Env.moves, List.nil_append]
      have reads : Env.reads (PureTransport.erase initial) signature.mode stateWords args =
          entry.state.reads (PureTransport.erase initial) stateWords current.state := by
        simp only [args, mode, Env.reads, List.append_nil, takeWords]
      have argsRep : Env.Rep signature.mode heap (PureTransport.erase initial) stateWords args := by
        rw [mode]
        exact ⟨stateWords, [], (List.append_nil _).symm, memory.rep.borrow, rfl⟩
      have separate : Separate (PureTransport.erase initial)
          (Env.moves (PureTransport.erase initial) signature.mode stateWords args)
          (Env.reads (PureTransport.erase initial) signature.mode stateWords args) := by
        rw [moves]
        exact Separate.nil
      have input : @Bytes.LiteralPool.Input (Env signature.params)
          (Env.represent signature.params signature.modes) pool heap (PureTransport.erase initial)
          stateWords args := by
        refine ⟨memory.static, ?_⟩
        change ∀ region ∈ pool.regions,
          Apart (PureTransport.erase initial)
            (Env.moves (PureTransport.erase initial) signature.mode stateWords args) region
        intro region _
        rw [moves]
        exact Apart.nil
      have scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) signature.mode stateWords args,
          regionsDisjoint ABI.scratch region := by
        rw [reads]
        exact memory.rep.reads_apart ABI.scratch (owned_scratch memory.rep)
      have callExecution := wp_effect_helper (locals := locals) (values := locals.values)
        (depth := 0) (params := stateWords) (args := args) (Q := Q)
        (rest := storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
          (Relocation.program (processCompaction entry.state) ++ [.br 0]))
        spec noImport lookup arity valid memory.at_ argsRep separate input scratch stored.cap
        (fun value finalHeap final words trace execution callStep representation => by
          have called : Step heap (PureTransport.erase initial)
              (fun region => regionsDisjoint region ABI.scratch)
              finalHeap (PureTransport.erase final)
              ((processResultTy entry.state).blocks (PureTransport.erase final) words value) := by
            exact callStep.mono (fun region kept => by
              refine ⟨?_, kept⟩
              rw [moves]
              exact Apart.nil) (fun _ member => member)
          have nativeExecution : LeanExe.Wasi.Exec (observedHost host) (process.step current.state)
              initial.host trace (.returned (processNative entry.state value)) final.host := by
            rw [stepMeaning]
            have composed := execution.bind
              (next := fun result => Action.pure (processNative entry.state result))
              (Exec.pure final.host (processNative entry.state value))
            simpa only [ProcessEntry.action, List.append_nil] using composed
          have resultMemory : ProcessMemory (processResultTy entry.state) pool finalHeap
              (PureTransport.erase final) words
              (processValue entry.state (processNative entry.state value)) := by
            rw [processValue_native]
            exact memory.called poolScratch called representation
          have grown := called.top_le memory.at_ free (scratch_apart_above _)
          refine wp_process_store_compact runtime layout profile compactable compactForm
            compactClosed resultMemory (by omega) stored.base stored.low stored.pool stored.params
            stored.positions (by rw [called.cap target]; exact stored.cap) (fun _ ended sameHost => ?_)
            fun ended after sameHost _ nextStored _ => ?_
          · apply ProcessIterationResult.resource ended trace
              (.pure (processNative entry.state value)) running
            rw [sameHost]
            exact LeanExe.Wasi.Exec.returned_prefix _ nativeExecution
          · rw [wp_br_cons]
            exact ProcessIterationResult.next (processNative entry.state value) ended after trace
              running (by simpa only [sameHost] using nativeExecution)
              (ProcessStored.values locals.values nextStored))
        (fun final trace outcome message execution terminal => by
          cases outcome with
          | returned value => exact terminal.elim
          | exited status =>
              apply ProcessIterationResult.terminal final trace (.exited status) message running
                (terminal := terminal)
              rw [stepMeaning]
              have composed := execution.bind
                (next := fun result => Action.pure (processNative entry.state result)) ⟨rfl, rfl, rfl⟩
              simpa only [ProcessEntry.action, List.append_nil] using composed
          | trapped cause =>
              apply ProcessIterationResult.terminal final trace (.trapped cause) message running
                (terminal := terminal)
              rw [stepMeaning]
              have composed := execution.bind
                (next := fun result => Action.pure (processNative entry.state result)) ⟨rfl, rfl, rfl⟩
              simpa only [ProcessEntry.action, List.append_nil] using composed)
        (fun final trace residual progress => by
          apply ProcessIterationResult.resource final trace
            (Action.bind residual fun result => .pure (processNative entry.state result)) running
          rw [stepMeaning, ProcessEntry.action]
          exact progress.bind)
      have loaded := wp_loadCode stateWords memory.rep.typed stored.positions held
        (s := { locals with values := .i64 0 :: locals.values })
        (by simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append] using callExecution)
      simpa [running, boolWord] using loaded

end Verified.Wasi
