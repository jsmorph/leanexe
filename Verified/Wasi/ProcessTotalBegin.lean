import Verified.Wasi.ProcessEntryProofs
import Verified.Wasi.ProcessTotalIteration

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def ProcessTotalBegan {World Ghost : Type} (source target : Wasm.Module) (state : Ty)
    (pool : Bytes.LiteralPool) (base : UInt64) (limit : Nat)
    (represented : Ghost → ProcessStep state.denote → Observed World → Prop) :
    Assertion (Observed World)
  | .Fallthrough final after =>
      ∃ ghost, ProcessTotalInvariant source target state pool base limit represented ghost final after
  | _ => False

theorem wp_process_begin_total {World Ghost : Type} {source target : Wasm.Module}
    {host : Host World} {pure : Resource.PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {entry : ProcessEntry effectSigs}
    {pool : Bytes.LiteralPool} {targetHost : HostEnv (Observed World)}
    {initial : Store (Observed World)} {heap : Heap} {locals : Locals}
    {function : Wasm.Function} {limit charge : Nat}
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (compactable : entry.state.compactable = true)
    (compactForm : Encoding.ProgramForm (processCompaction entry.state))
    (compactClosed :
      Relocation.programClosed source.funcs.length (processCompaction entry.state) = true)
    (spec : CostEffectSpec source target pure program entry.begin
      (Wrappers.effectIndex source entry.begin.index) pool)
    (noImport : target.imports[Wrappers.effectIndex source entry.begin.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndex source entry.begin.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1)
    (valid : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (params : locals.params = [])
    (positions : locals.positions = processPositions entry.state)
    (baseLocal : locals.get (processAux entry.state) = some (.i64 heap.top))
    (limitCap : limit ≤ 65536 * (PureTransport.erase initial).memoryCap source 0)
    (within : heap.top.toNat + charge ≤ limit)
    (bounded : Resource.CallPrefixBound (observedHost host) pure program entry.begin 0 .nil
      initial.host charge)
    (replies : ∀ trace outcome final,
      LeanExe.Wasi.Exec (observedHost host) (entry.beginAction (program.funs pure.funs))
        initial.host trace outcome final →
      ∃ ghost current, outcome = .returned current ∧ represented ghost current final ∧
        heap.top.toNat + charge + entry.state.copyCost current.state ≤ limit) :
    wp target ([.constI64 0, .call (Wrappers.effectIndex source entry.begin.index)] ++
      (storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
        Relocation.program (processCompaction entry.state)))
      (ProcessTotalBegan source target entry.state pool heap.top limit represented) initial locals
      targetHost := by
  let Q := ProcessTotalBegan source target entry.state pool heap.top limit represented
  have poolBelow := static.below
  have heapWithin : heap.Within (PureTransport.erase initial) source charge := by
    unfold Heap.Within
    omega
  have call := wp_cost_effect_helper (locals := locals) (values := locals.values) (depth := 0)
    (signature := ⟨entry.beginName, [], [], .value (processResultTy entry.state)⟩)
    (params := []) (args := (Env.nil : Env [])) (budget := charge) (aborts := false)
    (rest := storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
      (Relocation.program (processCompaction entry.state) ++ []))
    (Q := Q) spec noImport lookup (by simpa [widthSum] using arity) valid at_ rfl
    Separate.nil ⟨static, fun _ _ => Apart.nil⟩ (by intro _ member; exact nomatch member) cap
    (fun _ => ⟨heapWithin, bounded⟩)
    (fun (value : (processResultTy entry.state).denote) finalHeap final words trace spent callFits
        execution step rep rise => by
      obtain ⟨spentLe, callFitsTrue⟩ := bounded.returned execution
      have topBound : finalHeap.top.toNat ≤ heap.top.toNat + charge := by
        have := rise callFitsTrue
        omega
      have resultRep : (processResultTy entry.state).Rep .owned finalHeap
          (PureTransport.erase final) words value := rep
      have preserved := static.step step (fun region member => ⟨Apart.nil, poolScratch region member⟩)
      let current := processNative entry.state value
      have nativeExecution : LeanExe.Wasi.Exec (observedHost host)
          (entry.beginAction (program.funs pure.funs)) initial.host trace (.returned current)
          final.host := by
        simpa only [ProcessEntry.beginAction, List.append_nil] using
          execution.erase.bind (next := fun result => Action.pure (processNative entry.state result))
            (LeanExe.Wasi.Exec.pure final.host current)
      obtain ⟨ghost, native, same, held, room⟩ :=
        replies trace (.returned current) final.host nativeExecution
      cases same
      have nativeMemory : ProcessMemory (processResultTy entry.state) pool finalHeap
          (PureTransport.erase final) words (processValue entry.state current) := by
        change ProcessMemory (processResultTy entry.state) pool finalHeap (PureTransport.erase final)
          words (processValue entry.state (processNative entry.state value))
        rw [processValue_native entry.state value]
        exact ⟨step.at_, resultRep, preserved.1, preserved.2⟩
      have grown := step.top_le at_ free ⟨Apart.nil, scratch_apart_above _⟩
      have sameCap : (PureTransport.erase final).memoryCap source 0 =
          (PureTransport.erase initial).memoryCap source 0 := by
        simp only [Store.memoryCap, step.caps]
      refine wp_process_store_compact runtime layout profile compactable compactForm compactClosed
        nativeMemory grown baseLocal at_.base poolBelow params positions
        (by rw [step.cap target]; exact cap)
        (fun noRoom _ _ => absurd (compaction_room compactable topBound (by
          rw [sameCap]; omega)) noRoom)
        fun ended after sameHost sameCaps stored _ => ?_
      rw [wp_nil]
      have endedCap : (PureTransport.erase ended).memoryCap source 0 =
          (PureTransport.erase final).memoryCap source 0 := by
        simp only [Store.memoryCap, sameCaps]
      exact ⟨ghost, current, stored, by simpa only [sameHost] using held,
        by rw [endedCap, sameCap]; exact limitCap⟩)
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
    (storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
      Relocation.program (processCompaction entry.state))) Q initial locals targetHost
  simp only [wp_constI64_cons]
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.append_nil] using call

end Verified.Wasi
