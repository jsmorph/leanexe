import Verified.Wasi.ProcessIteration
import Verified.Wasi.ProcessTotalLoop
import Verified.Wasi.CostCallHelper

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def ProcessTotalInvariant {World Ghost : Type} (target : Wasm.Module) (state : Ty)
    (pool : Bytes.LiteralPool)
    (represented : Ghost → ProcessStep state.denote → Observed World → Prop)
    (ghost : Ghost) (store : Store (Observed World)) (locals : Locals) : Prop :=
  ∃ current, ProcessStored target state pool current store locals ∧
    represented ghost current store.host

def ProcessTotalStopped {World Ghost : Type} (target : Wasm.Module) (state : Ty)
    (pool : Bytes.LiteralPool)
    (represented : Ghost → ProcessStep state.denote → Observed World → Prop) :
    Assertion (Observed World)
  | .Break 0 final after =>
      ∃ ghost current, ProcessStored target state pool current final after ∧
        represented ghost current final.host ∧ current.running = false
  | _ => False

theorem wp_process_iteration_total {World Ghost : Type} {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {entry : ProcessEntry effectSigs} {host : Host World}
    {targetHost : HostEnv (Observed World)} {pool : Bytes.LiteralPool}
    {initial : Store (Observed World)} {locals : Locals}
    {current : ProcessStep entry.state.denote} {function : Wasm.Function}
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop) (ghost : Ghost)
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (releaseForm : Encoding.ProgramForm (releaseCode entry.state 2))
    (releaseClosed : Relocation.programClosed source.funcs.length (releaseCode entry.state 2) = true)
    (spec : CostEffectSpec source target pure program entry.step
      (Wrappers.effectIndex source entry.step.index) pool)
    (noImport : target.imports[Wrappers.effectIndex source entry.step.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndex source entry.step.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1 + widthSum [entry.state])
    (valid : targetHost.Satisfies target (hostSpec host))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (stored : ProcessStored target entry.state pool current initial locals)
    (held : represented ghost current initial.host)
    (resources : current.running = true → ∀ heap words,
      ProcessMemory entry.state pool heap (PureTransport.erase initial) words current.state →
      LocalsHold locals 2 entry.state.types words →
      ∃ budget, heap.Within (PureTransport.erase initial) source budget ∧
        Resource.CallPrefixBound (observedHost host) pure program entry.step 0
          (.cons current.state .nil) initial.host budget)
    (replies : current.running = true → ∀ trace outcome final,
      LeanExe.Wasi.Exec (observedHost host) (entry.action (program.funs pure.funs) current.state)
        initial.host trace outcome final →
      ∃ nextGhost next, outcome = .returned next ∧ represented nextGhost next final ∧
        relation nextGhost ghost) :
    wp target (entry.iteration source)
      (GhostLoopPost (ProcessTotalInvariant target entry.state pool represented) relation ghost
        (ProcessTotalStopped target entry.state pool represented) locals.values)
      initial locals targetHost := by
  let Q := GhostLoopPost (ProcessTotalInvariant target entry.state pool represented) relation ghost
    (ProcessTotalStopped target entry.state pool represented) locals.values
  obtain ⟨heap, stateWords, memory, stateHeld, control⟩ := stored.parts
  simp only [ProcessEntry.iteration, ProcessEntry.result, List.append_assoc,
    List.cons_append, List.nil_append, wp_localGet_cons, control, wp_eqzI64_cons]
  cases running : current.running with
  | false =>
      have stopped : Q (.Break 1 initial locals) := ⟨ghost, current, stored, held, running⟩
      simpa [running, boolWord] using stopped
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
      obtain ⟨budget, within, bounded⟩ := resources running heap stateWords memory stateHeld
      have callExecution := wp_cost_effect_helper (locals := locals) (values := locals.values)
        (depth := 0) (params := stateWords) (args := args) (Q := Q) (budget := budget) (aborts := false)
        (rest := storeCode (2 * (processResultTy entry.state).width) (processResultTy entry.state).width
            (processResultTy entry.state).types ++
          Relocation.program (releaseCode entry.state 2) ++
          loadCode (2 * (processResultTy entry.state).width) (processResultTy entry.state).width
            (processResultTy entry.state).types ++
          storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types ++ [.br 0])
        spec noImport lookup arity valid memory.at_ argsRep separate input scratch stored.cap
        (fun _ => ⟨within, bounded⟩)
        (fun value finalHeap final words trace spent fits execution callStep representation _ => by
          have called : Step heap (PureTransport.erase initial)
              (fun region => regionsDisjoint region ABI.scratch)
              finalHeap (PureTransport.erase final)
              ((processResultTy entry.state).blocks (PureTransport.erase final) words value) := by
            exact callStep.mono (fun region kept => by
              refine ⟨?_, kept⟩
              rw [moves]
              exact Apart.nil) (fun _ member => member)
          have nativeExecution : LeanExe.Wasi.Exec (observedHost host)
              (entry.action (program.funs pure.funs) current.state)
              initial.host trace (.returned (processNative entry.state value)) final.host := by
            have composed := execution.erase.bind
              (next := fun result => Action.pure (processNative entry.state result))
              (Exec.pure final.host (processNative entry.state value))
            simpa only [ProcessEntry.action, List.append_nil] using composed
          obtain ⟨nextGhost, next, same, nextRep, smaller⟩ :=
            replies running trace (.returned (processNative entry.state value)) final.host nativeExecution
          cases same
          apply wp_process_replace runtime layout profile releaseForm releaseClosed memory stateHeld
            stored.params stored.positions stored.cap poolScratch called representation
          intro released after sameWorld nextStored
          exact ⟨nextGhost, ⟨_, nextStored.values locals.values,
            by simpa only [sameWorld] using nextRep⟩, smaller⟩)
        (fun final message classification => by
          cases classification with
          | terminal final trace outcome message execution terminal =>
              cases outcome with
              | returned value => exact terminal.elim
              | exited status =>
                  have mapped : LeanExe.Wasi.Exec (observedHost host)
                      (entry.action (program.funs pure.funs) current.state)
                      initial.host trace (.exited status) final.host := by
                    simpa only [ProcessEntry.action, List.append_nil] using
                      execution.bind (next := fun result => Action.pure (processNative entry.state result))
                        ⟨rfl, rfl, rfl⟩
                  obtain ⟨_, _, impossible, _⟩ := replies running trace (.exited status) final.host mapped
                  cases impossible
              | trapped cause =>
                  have mapped : LeanExe.Wasi.Exec (observedHost host)
                      (entry.action (program.funs pure.funs) current.state)
                      initial.host trace (.trapped cause) final.host := by
                    simpa only [ProcessEntry.action, List.append_nil] using
                      execution.bind (next := fun result => Action.pure (processNative entry.state result))
                        ⟨rfl, rfl, rfl⟩
                  obtain ⟨_, _, impossible, _⟩ := replies running trace (.trapped cause) final.host mapped
                  cases impossible
          | resource final trace residual allowed progress => exact Bool.noConfusion allowed)
      have loaded := wp_loadCode stateWords memory.rep.typed stored.positions stateHeld
        (s := { locals with values := .i64 0 :: locals.values })
        (by simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append] using callExecution)
      simpa [running, boolWord] using loaded

end Verified.Wasi
