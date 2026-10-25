import Verified.Wasi.ProcessTotalBegin
import Verified.Wasi.WrapperDispatch

namespace Verified.Wasi

open Wasm LeanExe.Wasi

def ProcessTotalExited {World Ghost : Type} (host : Host World) (state : Ty)
    (represented : Ghost → ProcessStep state.denote → Observed World → Prop) :
    Assertion (Observed World)
  | .Trap final message => message = exitTrap ∧
      ∃ ghost current before, represented ghost current before ∧ current.running = false ∧
        (observedHost host).exit before (exitStatus current.status) final.host
  | _ => False

inductive ProcessReachable {World : Type} {effectSigs : List EffectSig}
    (source target : Wasm.Module) (entry : ProcessEntry effectSigs)
    (initial : Store World) (initialLocals : Locals) (host : HostEnv World) :
    Store World → Locals → Prop where
  | begin {fuel store locals}
      (execution : exec fuel target initial initialLocals
        ([.constI64 0, .call (Wrappers.effectIndex source entry.begin.index)] ++
          storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types)
        host = .Fallthrough store locals) :
      ProcessReachable source target entry initial initialLocals host store locals
  | next {fuel store locals final after}
      (previous : ProcessReachable source target entry initial initialLocals host store locals)
      (execution : exec fuel target store locals (entry.iteration source) host = .Break 0 final after) :
      ProcessReachable source target entry initial initialLocals host final
        { after with values := locals.values }

theorem wp_process_loop_total {World Ghost : Type} {source target : Wasm.Module}
    {host : Host World} {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {pool : Bytes.LiteralPool} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {locals : Locals}
    {ghost : Ghost} {current : ProcessStep entry.state.denote}
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    (reachable : Store (Observed World) → Locals → Prop)
    (advance : ∀ {fuel store locals final after}, reachable store locals →
      exec fuel target store locals (entry.iteration source) targetHost = .Break 0 final after →
      reachable final { after with values := locals.values })
    (imports : target.imports = ABI.imports)
    (valid : targetHost.Satisfies target (hostSpec host))
    (stored : ProcessStored target entry.state pool current initial locals)
    (held : represented ghost current initial.host)
    (reached : reachable initial locals)
    (iteration : ∀ ghost current store locals,
      ProcessStored target entry.state pool current store locals →
      represented ghost current store.host →
      reachable store locals →
      wp target (entry.iteration source)
        (GhostLoopPost (ProcessTotalInvariant target entry.state pool represented) relation ghost
          (ProcessTotalStopped target entry.state pool represented) locals.values)
        store locals targetHost)
    (accepted : ∀ ghost current world, represented ghost current world →
      current.running = false → ∀ message final,
      (observedHost host).exitTrap world (exitStatus current.status) message final → False) :
    wp target ([.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []] ++
      [.localGet 1, .wrapI64, .call 2, .unreachable])
      (ProcessTotalExited host entry.state represented) initial locals targetHost := by
  let invariant := fun ghost store locals =>
    ProcessTotalInvariant target entry.state pool represented ghost store locals ∧ reachable store locals
  have loop := wp_loop_ghost invariant relation wellFounded
    (ghost := ghost) ⟨⟨current, stored, held⟩, reached⟩ (fun ghost store locals rep => by
      obtain ⟨⟨current, stored, held⟩, reached⟩ := rep
      apply (iteration ghost current store locals stored held reached).with_execution.conseq
      intro continuation classification
      obtain ⟨classification, fuel, execution⟩ := classification
      cases continuation with
      | Break index final after =>
          cases index with
          | zero =>
              obtain ⟨nextGhost, nextRep, smaller⟩ := classification
              exact ⟨nextGhost, ⟨nextRep, advance reached execution⟩, smaller⟩
          | succ index => exact classification
      | _ => exact classification)
  apply wp_block_cons
  apply loop.conseq
  intro continuation stopped
  cases continuation with
  | Break index final after =>
      cases index with
      | zero =>
          obtain ⟨ghost, current, stored, held, stopped⟩ := stopped
          change wp target [.localGet 1, .wrapI64, .call 2, .unreachable]
            (ProcessTotalExited host entry.state represented) final
            { after with values := locals.values } targetHost
          simp only [wp_localGet_cons, Locals.get_values, stored.status]
          apply wp_exit_stack imports valid
          · intro ended exited _
            exact ⟨rfl, ghost, current, final.host, held, stopped, exited⟩
          · intro ended message rejected _
            exact (accepted ghost current final.host held stopped message ended.host rejected).elim
      | succ index => exact stopped.elim
  | _ => exact stopped.elim

theorem wp_process_entry_total {World Ghost : Type} {source target : Wasm.Module}
    {host : Host World} {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {pool : Bytes.LiteralPool} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {typeIdx : Nat}
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    (imports : target.imports = ABI.imports)
    (valid : targetHost.Satisfies target (hostSpec host))
    (began : wp target
      ([.constI64 0, .call (Wrappers.effectIndex source entry.begin.index)] ++
        storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types)
      (ProcessTotalBegan target entry.state pool represented) initial
      ((entry.function source typeIdx).toLocals []) targetHost)
    (iteration : ∀ ghost current store locals,
      ProcessStored target entry.state pool current store locals →
      represented ghost current store.host →
      ProcessReachable source target entry initial
        ((entry.function source typeIdx).toLocals []) targetHost store locals →
      wp target (entry.iteration source)
        (GhostLoopPost (ProcessTotalInvariant target entry.state pool represented) relation ghost
          (ProcessTotalStopped target entry.state pool represented) locals.values)
        store locals targetHost)
    (accepted : ∀ ghost current world, represented ghost current world →
      current.running = false → ∀ message final,
      (observedHost host).exitTrap world (exitStatus current.status) message final → False) :
    wp target (entry.function source typeIdx).body
      (ProcessTotalExited host entry.state represented) initial
      ((entry.function source typeIdx).toLocals []) targetHost := by
  let tailCode : Program := [.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []] ++
    [.localGet 1, .wrapI64, .call 2, .unreachable]
  have body := wp_append (rest := tailCode)
    (Q := ProcessTotalExited host entry.state represented)
    (began.with_execution.conseq (fun continuation classification => by
      obtain ⟨classification, fuel, execution⟩ := classification
      cases continuation with
      | Fallthrough final after =>
          obtain ⟨ghost, current, stored, held⟩ := classification
          exact wp_process_loop_total represented relation wellFounded
            (ProcessReachable source target entry initial
              ((entry.function source typeIdx).toLocals []) targetHost)
            (fun previous execution => .next previous execution)
            imports valid stored held (.begin execution) iteration accepted
      | _ => exact classification.elim))
  simpa only [ProcessEntry.function, ProcessEntry.result, tailCode, List.append_assoc] using body

def ProcessTotalRunExited {World Ghost : Type} (host : Host World) (state : Ty)
    (represented : Ghost → ProcessStep state.denote → Observed World → Prop) :
    Result (Observed World) → Prop
  | .Trap final message => ProcessTotalExited host state represented (.Trap final message)
  | _ => False

theorem process_entry_total_run {World Ghost : Type} {target : Wasm.Module}
    {host : Host World} {state : Ty}
    {represented : Ghost → ProcessStep state.denote → Observed World → Prop}
    {function : Wasm.Function} {index : Nat} {initial : Store (Observed World)}
    {targetHost : HostEnv (Observed World)}
    (imports : target.imports = ABI.imports)
    (lookup : target.funcs[index]? = some function)
    (arity : function.numParams = 0)
    (body : wp target function.body (ProcessTotalExited host state represented)
      initial (function.toLocals []) targetHost) :
    ∃ bound, ∀ fuel ≥ bound,
      ProcessTotalRunExited host state represented
        (run fuel target (3 + index) initial [] targetHost) := by
  apply defined_function_run_post (params := []) (width := function.results.length)
    imports lookup (by simpa only [List.length_nil] using arity.symm) rfl
  apply body.conseq
  intro continuation terminal
  cases continuation with
  | Trap final message => exact terminal
  | _ => exact terminal.elim

end Verified.Wasi
