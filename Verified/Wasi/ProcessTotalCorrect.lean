import Verified.Wasi.ProcessFacts
import Verified.Wasi.ProcessTotalEntry

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem compiled_process_total_body {World Ghost : Type} {source : Wasm.Module}
    {host : Host World} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool)
    (calls : CostEffectCalls source (compileProcess source program entry pool) pure program pool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (releaseForm : Encoding.ProgramForm (releaseCode entry.state 2))
    (releaseClosed : Relocation.programClosed source.funcs.length (releaseCode entry.state 2) = true)
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    (valid : targetHost.Satisfies (compileProcess source program entry pool) (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap (compileProcess source program entry pool) 0 ≤ 65535)
    (beginResources : ∃ budget, heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program entry.begin 0 .nil initial.host budget)
    (beginReplies : ∀ trace outcome final,
      LeanExe.Wasi.Exec (observedHost host) (entry.beginAction (program.funs pure.funs))
        initial.host trace outcome final →
      ∃ ghost current, outcome = .returned current ∧ represented ghost current final)
    (stepResources : ∀ ghost current (store : Store (Observed World)) locals heap words,
      ProcessReachable source (compileProcess source program entry pool) entry initial
        ((entry.function source (effectTypeIndex source effectSigs.length)).toLocals [])
        targetHost store locals →
      represented ghost current store.host →
      current.running = true →
      ProcessMemory entry.state pool heap (PureTransport.erase store) words current.state →
      LocalsHold locals 2 entry.state.types words →
      ∃ budget, heap.Within (PureTransport.erase store) source budget ∧
        Resource.CallPrefixBound (observedHost host) pure program entry.step 0
          (.cons current.state .nil) store.host budget)
    (stepReplies : ∀ ghost current world, represented ghost current world →
      current.running = true → ∀ trace outcome final,
      LeanExe.Wasi.Exec (observedHost host) (entry.action (program.funs pure.funs) current.state)
        world trace outcome final →
      ∃ nextGhost next, outcome = .returned next ∧ represented nextGhost next final ∧
        relation nextGhost ghost)
    (accepted : ∀ ghost current world, represented ghost current world →
      current.running = false → ∀ message final,
      (observedHost host).exitTrap world (exitStatus current.status) message final → False) :
    wp (compileProcess source program entry pool)
      (entry.function source (effectTypeIndex source effectSigs.length)).body
      (ProcessTotalExited host entry.state represented) initial
      ((entry.function source (effectTypeIndex source effectSigs.length)).toLocals []) targetHost := by
  let target := compileProcess source program entry pool
  have notImported (index : Nat) : target.imports[Wrappers.effectIndex source index]? = none :=
    List.getElem?_eq_none (by
      rw [compileProcess_imports, ABI.imports_length]
      simp only [Wrappers.effectIndex, Module.extraIndex]
      omega)
  obtain ⟨beginFunction, beginLookup, beginArity⟩ :=
    compileProcess_effect_arity source program entry pool entry.begin
  obtain ⟨stepFunction, stepLookup, stepArity⟩ :=
    compileProcess_effect_arity source program entry pool entry.step
  let locals := (entry.function source (effectTypeIndex source effectSigs.length)).toLocals []
  have positions : locals.positions = 2 * (processResultTy entry.state).width := by
    simp only [locals, ProcessEntry.function, ProcessEntry.result, Function.toLocals, Locals.positions,
      List.length_nil, List.length_map, List.length_append, List.length_replicate, Nat.zero_add]
    omega
  obtain ⟨budget, within, bounded⟩ := beginResources
  have began := wp_process_begin_total represented (locals := locals) (calls entry.begin)
    (notImported _) beginLookup
    (by simpa only [widthSum, List.map_nil, List.sum_nil, Nat.add_zero] using beginArity)
    valid at_ static poolScratch cap rfl positions within bounded beginReplies
  apply wp_process_entry_total represented relation wellFounded
    (compileProcess_imports source program entry pool) valid began
  · intro ghost current store locals stored held reached
    apply wp_process_iteration_total represented relation ghost runtime
      (compileProcess_layout program entry pool runtime.imports) profile releaseForm releaseClosed
      (calls entry.step) (notImported _) stepLookup stepArity valid poolScratch stored held
    · intro running heap words memory active
      exact stepResources ghost current store locals heap words reached held running memory active
    · exact stepReplies ghost current store.host held
  · exact accepted

theorem compiled_process_total_run {World Ghost : Type} {source : Wasm.Module}
    {host : Host World} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool)
    (calls : CostEffectCalls source (compileProcess source program entry pool) pure program pool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (releaseForm : Encoding.ProgramForm (releaseCode entry.state 2))
    (releaseClosed : Relocation.programClosed source.funcs.length (releaseCode entry.state 2) = true)
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    (valid : targetHost.Satisfies (compileProcess source program entry pool) (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap (compileProcess source program entry pool) 0 ≤ 65535)
    (beginResources : ∃ budget, heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost host) pure program entry.begin 0 .nil initial.host budget)
    (beginReplies : ∀ trace outcome final,
      LeanExe.Wasi.Exec (observedHost host) (entry.beginAction (program.funs pure.funs))
        initial.host trace outcome final →
      ∃ ghost current, outcome = .returned current ∧ represented ghost current final)
    (stepResources : ∀ ghost current (store : Store (Observed World)) locals heap words,
      ProcessReachable source (compileProcess source program entry pool) entry initial
        ((entry.function source (effectTypeIndex source effectSigs.length)).toLocals [])
        targetHost store locals →
      represented ghost current store.host →
      current.running = true →
      ProcessMemory entry.state pool heap (PureTransport.erase store) words current.state →
      LocalsHold locals 2 entry.state.types words →
      ∃ budget, heap.Within (PureTransport.erase store) source budget ∧
        Resource.CallPrefixBound (observedHost host) pure program entry.step 0
          (.cons current.state .nil) store.host budget)
    (stepReplies : ∀ ghost current world, represented ghost current world →
      current.running = true → ∀ trace outcome final,
      LeanExe.Wasi.Exec (observedHost host) (entry.action (program.funs pure.funs) current.state)
        world trace outcome final →
      ∃ nextGhost next, outcome = .returned next ∧ represented nextGhost next final ∧
        relation nextGhost ghost)
    (accepted : ∀ ghost current world, represented ghost current world →
      current.running = false → ∀ message final,
      (observedHost host).exitTrap world (exitStatus current.status) message final → False) :
    ∃ bound, ∀ fuel ≥ bound,
      ProcessTotalRunExited host entry.state represented
        (run fuel (compileProcess source program entry pool)
          (Wrappers.effectIndex source effectSigs.length) initial [] targetHost) := by
  have body := compiled_process_total_body program entry pool calls runtime profile releaseForm
    releaseClosed represented relation wellFounded valid at_ static poolScratch cap
    beginResources beginReplies stepResources stepReplies accepted
  have indexEq : Wrappers.effectIndex source effectSigs.length =
      3 + (source.funcs.length + (3 + effectSigs.length)) := by
    simp only [Wrappers.effectIndex, Module.extraIndex]
    omega
  rw [indexEq]
  exact process_entry_total_run (compileProcess_imports source program entry pool)
    (compileProcess_start source program entry pool) rfl body

end Verified.Wasi
