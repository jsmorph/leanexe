import Verified.Wasi.ProcessFacts
import Verified.Wasi.ProcessRunProofs

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem compiled_process_body {World : Type} {source : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool)
    (calls : CostEffectCalls source (compileProcess source program entry pool) pure program pool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (compactable : entry.state.compactable = true)
    (compactForm : Encoding.ProgramForm (processCompaction entry.state))
    (compactClosed :
      Relocation.programClosed source.funcs.length (processCompaction entry.state) = true)
    {process : Process entry.state.denote}
    (stepMeaning : ∀ state, process.step state = entry.action (program.funs pure.funs) state)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    (valid : targetHost.Satisfies (compileProcess source program entry pool) (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap (compileProcess source program entry pool) 0 ≤ 65535) :
    pwp (compileProcess source program entry pool)
      (entry.function source (effectTypeIndex source effectSigs.length)).body
      (ProcessEntryResult (observedHost host) (entry.beginAction (program.funs pure.funs))
        process initial.host)
      initial ((entry.function source (effectTypeIndex source effectSigs.length)).toLocals []) targetHost := by
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
  have layout := compileProcess_layout program entry pool runtime.imports
  apply pwp_process_entry_body (functions := program.funs pure.funs) runtime layout profile
    compactable compactForm compactClosed
    (calls.safety entry.begin) (notImported _) beginLookup
    (by simpa only [widthSum, List.map_nil, List.sum_nil, Nat.add_zero] using beginArity)
    (compileProcess_imports source program entry pool) valid at_ free static poolScratch cap
  intro current store locals stored
  exact (wp_process_iteration runtime layout profile compactable compactForm compactClosed
    (calls.safety entry.step) (notImported _) stepLookup stepArity valid poolScratch stepMeaning
    stored).pwp

theorem compiled_process_run {World : Type} {source : Wasm.Module} {host : Host World}
    {pure : Resource.PureContext pureSigs} (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool)
    (calls : CostEffectCalls source (compileProcess source program entry pool) pure program pool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (compactable : entry.state.compactable = true)
    (compactForm : Encoding.ProgramForm (processCompaction entry.state))
    (compactClosed :
      Relocation.programClosed source.funcs.length (processCompaction entry.state) = true)
    {process : Process entry.state.denote}
    (stepMeaning : ∀ state, process.step state = entry.action (program.funs pure.funs) state)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap} {fuel : Nat}
    (valid : targetHost.Satisfies (compileProcess source program entry pool) (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap (compileProcess source program entry pool) 0 ≤ 65535)
    (completed : run fuel (compileProcess source program entry pool)
      (Wrappers.effectIndex source effectSigs.length) initial [] targetHost ≠ .OutOfFuel) :
    ProcessEntryRunResult (observedHost host) (entry.beginAction (program.funs pure.funs))
      process initial.host (run fuel (compileProcess source program entry pool)
        (Wrappers.effectIndex source effectSigs.length) initial [] targetHost) := by
  have body := compiled_process_body program entry pool calls runtime profile compactable
    compactForm compactClosed stepMeaning valid at_ free static poolScratch cap
  have indexEq : Wrappers.effectIndex source effectSigs.length =
      3 + (source.funcs.length + (3 + effectSigs.length)) := by
    simp only [Wrappers.effectIndex, Module.extraIndex]
    omega
  rw [indexEq] at completed ⊢
  exact process_entry_run (compileProcess_imports source program entry pool)
    (compileProcess_start source program entry pool) body completed

end Verified.Wasi
