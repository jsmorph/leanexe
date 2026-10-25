import Verified.Wasi.ProcessEntryProofs
import Verified.Wasi.ProcessTotalIteration

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def ProcessTotalBegan {World Ghost : Type} (target : Wasm.Module) (state : Ty)
    (pool : Bytes.LiteralPool)
    (represented : Ghost → ProcessStep state.denote → Observed World → Prop) :
    Assertion (Observed World)
  | .Fallthrough final after =>
      ∃ ghost current, ProcessStored target state pool current final after ∧
        represented ghost current final.host
  | _ => False

theorem wp_process_begin_total {World Ghost : Type} {source target : Wasm.Module}
    {host : Host World} {pure : Resource.PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {entry : ProcessEntry effectSigs}
    {pool : Bytes.LiteralPool} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {locals : Locals}
    {function : Wasm.Function} {budget : Nat}
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (spec : CostEffectSpec source target pure program entry.begin
      (Wrappers.effectIndex source entry.begin.index) pool)
    (noImport : target.imports[Wrappers.effectIndex source entry.begin.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndex source entry.begin.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (params : locals.params = [])
    (positions : locals.positions = 2 * (processResultTy entry.state).width)
    (within : heap.Within (PureTransport.erase initial) source budget)
    (bounded : Resource.CallPrefixBound (observedHost host) pure program entry.begin 0 .nil
      initial.host budget)
    (replies : ∀ trace outcome final,
      LeanExe.Wasi.Exec (observedHost host) (entry.beginAction (program.funs pure.funs))
        initial.host trace outcome final →
      ∃ ghost current, outcome = .returned current ∧ represented ghost current final) :
    wp target ([.constI64 0, .call (Wrappers.effectIndex source entry.begin.index)] ++
      storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types)
      (ProcessTotalBegan target entry.state pool represented) initial locals targetHost := by
  let Q := ProcessTotalBegan target entry.state pool represented
  have call := wp_cost_effect_helper (locals := locals) (values := locals.values) (depth := 0)
    (signature := ⟨entry.beginName, [], [], .value (processResultTy entry.state)⟩)
    (params := []) (args := (Env.nil : Env [])) (budget := budget) (aborts := false)
    (rest := storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types)
    (Q := Q) spec noImport lookup (by simpa [widthSum] using arity) valid at_ rfl
    Separate.nil ⟨static, fun _ _ => Apart.nil⟩ (by intro _ member; exact nomatch member) cap
    (fun _ => ⟨within, bounded⟩)
    (fun (value : (processResultTy entry.state).denote) finalHeap final words trace spent fits
        execution step rep _ => by
      have resultRep : (processResultTy entry.state).Rep .owned finalHeap
          (PureTransport.erase final) words value := rep
      have preserved := static.step step (fun region member => ⟨Apart.nil, poolScratch region member⟩)
      have memory : ProcessMemory (processResultTy entry.state) pool finalHeap
          (PureTransport.erase final) words value :=
        ⟨step.at_, resultRep, preserved.1, preserved.2⟩
      let current := processNative entry.state value
      have nativeExecution : LeanExe.Wasi.Exec (observedHost host)
          (entry.beginAction (program.funs pure.funs)) initial.host trace (.returned current)
          final.host := by
        simpa only [ProcessEntry.beginAction, List.append_nil] using
          execution.erase.bind (next := fun result => Action.pure (processNative entry.state result))
            (LeanExe.Wasi.Exec.pure final.host current)
      obtain ⟨ghost, native, same, held⟩ := replies trace (.returned current) final.host nativeExecution
      cases same
      have nativeMemory : ProcessMemory (processResultTy entry.state) pool finalHeap
          (PureTransport.erase final) words (processValue entry.state current) := by
        change ProcessMemory (processResultTy entry.state) pool finalHeap (PureTransport.erase final)
          words (processValue entry.state (processNative entry.state value))
        rw [processValue_native entry.state value]
        exact memory
      simpa only [List.append_nil] using
        (wp_storeCode (rest := []) (Q := Q) words (2 * (processResultTy entry.state).width) 0
          (processResultTy entry.state).types locals locals.values
          resultRep.typed positions (by simp only [params, List.length_nil, Nat.le_refl])
          (by rw [Ty.types_length, positions]; omega)
          (fun after frame stored _ => by
            rw [wp_nil]
            exact ⟨ghost, current,
              ⟨⟨finalHeap, words, nativeMemory, stored⟩,
                frame.params.trans params, frame.positions.trans positions,
                by rw [step.cap target]; exact cap⟩, held⟩)) )
    (fun final message classification => by
      cases classification with
      | terminal final trace outcome message execution terminal =>
          cases outcome with
          | returned value => exact terminal.elim
          | exited status =>
              have mapped : LeanExe.Wasi.Exec (observedHost host)
                  (entry.beginAction (program.funs pure.funs)) initial.host trace (.exited status)
                  final.host := by
                simpa only [ProcessEntry.beginAction, List.append_nil] using
                  execution.bind (next := fun result => Action.pure (processNative entry.state result))
                    ⟨rfl, rfl, rfl⟩
              obtain ⟨_, _, impossible, _⟩ := replies trace (.exited status) final.host mapped
              cases impossible
          | trapped cause =>
              have mapped : LeanExe.Wasi.Exec (observedHost host)
                  (entry.beginAction (program.funs pure.funs)) initial.host trace (.trapped cause)
                  final.host := by
                simpa only [ProcessEntry.beginAction, List.append_nil] using
                  execution.bind (next := fun result => Action.pure (processNative entry.state result))
                    ⟨rfl, rfl, rfl⟩
              obtain ⟨_, _, impossible, _⟩ := replies trace (.trapped cause) final.host mapped
              cases impossible
      | resource final trace residual allowed progress => exact Bool.noConfusion allowed)
  change wp target (.constI64 0 :: .call (Wrappers.effectIndex source entry.begin.index) ::
    storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types)
      Q initial locals targetHost
  simp only [wp_constI64_cons]
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using call

end Verified.Wasi
