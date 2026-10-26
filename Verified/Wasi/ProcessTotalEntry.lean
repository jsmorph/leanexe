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

theorem wp_process_loop_total {World Ghost : Type} {source target : Wasm.Module}
    {host : Host World} {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {pool : Bytes.LiteralPool} {base : UInt64} {limit : Nat}
    {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {locals : Locals} {ghost : Ghost}
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    (imports : target.imports = ABI.imports)
    (valid : targetHost.Satisfies target (hostSpec host))
    (held : ProcessTotalInvariant source target entry.state pool base limit represented ghost
      initial locals)
    (iteration : ∀ ghost store locals,
      ProcessTotalInvariant source target entry.state pool base limit represented ghost store
        locals →
      wp target (entry.iteration source)
        (GhostLoopPost (ProcessTotalInvariant source target entry.state pool base limit represented)
          relation ghost (ProcessTotalStopped target entry.state pool base represented) locals.values)
        store locals targetHost)
    (accepted : ∀ ghost current world, represented ghost current world →
      current.running = false → ∀ message final,
      (observedHost host).exitTrap world (exitStatus current.status) message final → False) :
    wp target ([.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []] ++
      [.localGet 1, .wrapI64, .call 2, .unreachable])
      (ProcessTotalExited host entry.state represented) initial locals targetHost := by
  have loop := wp_loop_ghost
    (ProcessTotalInvariant source target entry.state pool base limit represented) relation
    wellFounded (ghost := ghost) held iteration
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
    {pool : Bytes.LiteralPool} {limit : Nat} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {typeIdx : Nat}
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    (imports : target.imports = ABI.imports)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (began : ∀ locals, locals.params = [] → locals.positions = processPositions entry.state →
      locals.get (processAux entry.state) = some (.i64 heap.top) →
      wp target
        ([.constI64 0, .call (Wrappers.effectIndex source entry.begin.index)] ++
          (storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
            Relocation.program (processCompaction entry.state)))
        (ProcessTotalBegan source target entry.state pool heap.top limit represented) initial
        locals targetHost)
    (iteration : ∀ ghost store locals,
      ProcessTotalInvariant source target entry.state pool heap.top limit represented ghost store
        locals →
      wp target (entry.iteration source)
        (GhostLoopPost (ProcessTotalInvariant source target entry.state pool heap.top limit
          represented) relation ghost (ProcessTotalStopped target entry.state pool heap.top
          represented) locals.values)
        store locals targetHost)
    (accepted : ∀ ghost current world, represented ghost current world →
      current.running = false → ∀ message final,
      (observedHost host).exitTrap world (exitStatus current.status) message final → False) :
    wp target (entry.function source typeIdx).body
      (ProcessTotalExited host entry.state represented) initial
      ((entry.function source typeIdx).toLocals []) targetHost := by
  let locals := (entry.function source typeIdx).toLocals []
  let tailCode : Program := [.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []] ++
    [.localGet 1, .wrapI64, .call 2, .unreachable]
  have positions : locals.positions = processPositions entry.state := by
    simp only [locals, ProcessEntry.function, Function.toLocals, Locals.positions,
      List.length_nil, List.length_map, List.length_append, List.length_replicate, Nat.zero_add]
    omega
  have total : processAux entry.state < locals.params.length + locals.locals.length :=
    Locals.lt_total (by rw [positions]; simp only [processPositions]; omega)
  have low : locals.params.length ≤ processAux entry.state := Nat.zero_le _
  have low' : ({ locals with values := locals.values } : Locals).params.length ≤
      processAux entry.state := low
  have body := wp_append (rest := tailCode)
    (Q := ProcessTotalExited host entry.state represented)
    ((began (setLocal { locals with values := locals.values } (processAux entry.state)
        (.i64 heap.top)) rfl
      (by simp only [Locals.positions_setLocal, Locals.positions_values]; exact positions)
      (Locals.get_setLocal_same low' total)).conseq (fun continuation classification => by
      cases continuation with
      | Fallthrough final after =>
          obtain ⟨ghost, held⟩ := classification
          exact wp_process_loop_total represented relation wellFounded imports valid held
            iteration accepted
      | _ => exact classification.elim))
  have whole := wp_saveBase (target := target) (rest := _) at_ low total body
  simpa only [ProcessEntry.function, ProcessEntry.result, tailCode, List.append_assoc,
    List.cons_append, List.nil_append] using whole

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
