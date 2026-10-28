import Verified.Wasi.ProcessFacts
import Verified.Wasi.ProcessTotalEntry

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

/-- The premises of the total process theorem.  `begin` and each step from a represented running
state have prefix bounds `beginCharge` and `charge`, every outcome of either is a returned state,
and the room conditions hold: with `base` the heap top before `begin`, `base + beginCharge` plus
the copy of `begin`'s state, and `base` plus the copy of a running state, its step's charge, and
the copy of the next state, fit in the memory cap. -/
structure ProcessTotalPremises {World Ghost : Type} (source : Wasm.Module)
    (host : Host World) (pure : Resource.PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop)
    (charge : Ghost → ProcessStep entry.state.denote → Nat) (beginCharge : Nat)
    (initial : Store (Observed World)) (heap : Heap) : Prop where
  beginRoom : heap.top.toNat + beginCharge ≤
    65536 * (PureTransport.erase initial).memoryCap source 0
  beginBounded : Resource.CallPrefixBound (observedHost host) pure program entry.begin 0 .nil
    initial.host beginCharge
  beginReplies : ∀ trace outcome final,
    LeanExe.Wasi.Exec (observedHost host) (entry.beginAction (program.funs pure.funs))
      initial.host trace outcome final →
    ∃ ghost current, outcome = .returned current ∧ represented ghost current final ∧
      heap.top.toNat + beginCharge + entry.state.copyCost current.state ≤
        65536 * (PureTransport.erase initial).memoryCap source 0
  stepRoom : ∀ ghost current world, represented ghost current world →
    current.running = true →
    heap.top.toNat + entry.state.copyCost current.state + charge ghost current ≤
      65536 * (PureTransport.erase initial).memoryCap source 0
  stepBounded : ∀ ghost current world, represented ghost current world →
    current.running = true →
    Resource.CallPrefixBound (observedHost host) pure program entry.step 0
      (.cons current.state .nil) world (charge ghost current)
  stepReplies : ∀ ghost current world, represented ghost current world →
    current.running = true → ∀ trace outcome final,
    LeanExe.Wasi.Exec (observedHost host) (entry.action (program.funs pure.funs) current.state)
      world trace outcome final →
    ∃ nextGhost next, outcome = .returned next ∧ represented nextGhost next final ∧
      relation nextGhost ghost ∧
      heap.top.toNat + entry.state.copyCost current.state + charge ghost current +
        entry.state.copyCost next.state ≤
        65536 * (PureTransport.erase initial).memoryCap source 0

theorem compiled_process_total_body {World Ghost : Type} {source : Wasm.Module}
    {host : Host World} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool)
    (calls : CostEffectCalls source (compileProcess source program entry pool) pure program pool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (compactable : entry.state.compactable = true)
    (compactForm : Encoding.ProgramForm (processCompaction entry.state))
    (compactClosed :
      Relocation.programClosed source.funcs.length (processCompaction entry.state) = true)
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    (charge : Ghost → ProcessStep entry.state.denote → Nat) (beginCharge : Nat)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    (valid : targetHost.Satisfies (compileProcess source program entry pool) (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap (compileProcess source program entry pool) 0 ≤ 65535)
    (premises : ProcessTotalPremises source host pure program entry represented
      relation charge beginCharge initial heap)
    (accepted : ∀ ghost current world, represented ghost current world →
      current.running = false → ∀ message final,
      (observedHost host).exitTrap world (exitStatus current.status) message final → False) :
    wp (compileProcess source program entry pool)
      (entry.function source (effectTypeIndex source effectSigs.length)).body
      (ProcessTotalExited host entry.state represented) initial
      ((entry.function source (effectTypeIndex source effectSigs.length)).toLocals []) targetHost := by
  let target := compileProcess source program entry pool
  let limit := 65536 * (PureTransport.erase initial).memoryCap source 0
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
  apply wp_process_entry_total (limit := limit) represented relation wellFounded
    (compileProcess_imports source program entry pool) valid at_
  · intro locals params positions baseLocal
    exact wp_process_begin_total represented runtime layout profile compactable compactForm
      compactClosed (calls entry.begin) (notImported _) beginLookup
      (by simpa only [widthSum, List.map_nil, List.sum_nil, Nat.add_zero] using beginArity)
      valid at_ free static poolScratch cap params positions baseLocal le_rfl premises.beginRoom
      premises.beginBounded premises.beginReplies
  · rintro ghost store locals ⟨current, stored, held, limitCap⟩
    exact wp_process_iteration_total represented relation charge ghost runtime layout profile
      compactable compactForm compactClosed (calls entry.step) (notImported _) stepLookup
      stepArity valid poolScratch stored held limitCap
      (fun running => ⟨premises.stepRoom ghost current store.host held running,
        premises.stepBounded ghost current store.host held running⟩)
      (premises.stepReplies ghost current store.host held)
  · exact accepted

theorem compiled_process_total_run {World Ghost : Type} {source : Wasm.Module}
    {host : Host World} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool)
    (calls : CostEffectCalls source (compileProcess source program entry pool) pure program pool)
    (runtime : Runtime source) (profile : Relocation.Profile source)
    (compactable : entry.state.compactable = true)
    (compactForm : Encoding.ProgramForm (processCompaction entry.state))
    (compactClosed :
      Relocation.programClosed source.funcs.length (processCompaction entry.state) = true)
    (represented : Ghost → ProcessStep entry.state.denote → Observed World → Prop)
    (relation : Ghost → Ghost → Prop) (wellFounded : WellFounded relation)
    (charge : Ghost → ProcessStep entry.state.denote → Nat) (beginCharge : Nat)
    {targetHost : HostEnv (Observed World)} {initial : Store (Observed World)} {heap : Heap}
    (valid : targetHost.Satisfies (compileProcess source program entry pool) (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : pool.Static heap (PureTransport.erase initial))
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap (compileProcess source program entry pool) 0 ≤ 65535)
    (premises : ProcessTotalPremises source host pure program entry represented
      relation charge beginCharge initial heap)
    (accepted : ∀ ghost current world, represented ghost current world →
      current.running = false → ∀ message final,
      (observedHost host).exitTrap world (exitStatus current.status) message final → False) :
    ∃ bound, ∀ fuel ≥ bound,
      ProcessTotalRunExited host entry.state represented
        (run fuel (compileProcess source program entry pool)
          (Wrappers.effectIndex source effectSigs.length) initial [] targetHost) := by
  have body := compiled_process_total_body program entry pool calls runtime profile compactable
    compactForm compactClosed represented relation wellFounded charge beginCharge valid at_ free
    static poolScratch cap premises accepted
  have indexEq : Wrappers.effectIndex source effectSigs.length =
      3 + (source.funcs.length + (3 + effectSigs.length)) := by
    simp only [Wrappers.effectIndex, Module.extraIndex]
    omega
  rw [indexEq]
  exact process_entry_total_run (compileProcess_imports source program entry pool)
    (compileProcess_start source program entry pool) rfl body

end Verified.Wasi
