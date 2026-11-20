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

/-- The step's argument: the state's words represent the state in the step's mode, and the call
moves the state's objects and reads none.  A state without heap values has no objects. -/
theorem ProcessEntry.step_args (entry : ProcessEntry effectSigs) {heap : Heap}
    {store : Store Unit} {stateWords : List Value} {value : entry.state.denote}
    (rep : entry.state.Rep .owned heap store stateWords value) :
    Env.Rep (EffectSig.mode
        ⟨entry.stepName, [entry.state], [entry.stepMode], .value (processResultTy entry.state)⟩)
      heap store stateWords (.cons value .nil) ∧
    Env.moves store (EffectSig.mode
        ⟨entry.stepName, [entry.state], [entry.stepMode], .value (processResultTy entry.state)⟩)
      stateWords (.cons value .nil) = entry.state.pointers store stateWords value ∧
    Env.reads store (EffectSig.mode
        ⟨entry.stepName, [entry.state], [entry.stepMode], .value (processResultTy entry.state)⟩)
      stateWords (.cons value .nil) = [] := by
  have takeWords : stateWords.take entry.state.width = stateWords := by
    rw [← rep.length]
    exact List.take_length
  rcases entry.moved with owned | scalar
  · have mode : EffectSig.mode
        ⟨entry.stepName, [entry.state], [entry.stepMode], .value (processResultTy entry.state)⟩ 0 =
        .owned := owned
    refine ⟨⟨stateWords, [], (List.append_nil _).symm, by rw [mode]; exact rep, rfl⟩, ?_, ?_⟩
    · simp only [Env.moves, mode, takeWords, List.append_nil]
    · simp only [Env.reads, mode, List.append_nil]
  · have mode : EffectSig.mode
        ⟨entry.stepName, [entry.state], [entry.stepMode], .value (processResultTy entry.state)⟩ 0 =
        .borrowed := Ty.paramMode_scalar _ scalar _
    refine ⟨⟨stateWords, [], (List.append_nil _).symm, by rw [mode]; exact rep.borrow, rfl⟩, ?_,
      ?_⟩
    · simp only [Env.moves, mode, List.append_nil, Ty.pointers_scalar _ scalar]
    · simp only [Env.reads, mode, List.append_nil, Ty.reads_scalar _ scalar]

/-- The objects of a stored state lie apart from one another. -/
theorem ProcessMemory.separate {state : Ty} {pool : Bytes.LiteralPool} {heap : Heap}
    {store : Store Unit} {words : List Value} {value : state.denote}
    (memory : ProcessMemory state pool heap store words value) :
    Separate store (state.pointers store words value) [] :=
  ⟨by rw [← Ty.blocks_pointers]; exact memory.rep.pairwise, fun _ member => nomatch member⟩

/-- The objects of a stored state lie apart from the literal pool. -/
theorem ProcessMemory.pool_apart {state : Ty} {pool : Bytes.LiteralPool} {heap : Heap}
    {store : Store Unit} {words : List Value} {value : state.denote}
    (memory : ProcessMemory state pool heap store words value) :
    ∀ region ∈ pool.regions, Apart store (state.pointers store words value) region :=
  fun region member pointer pointed => memory.apart region member _
    (by rw [Ty.blocks_pointers]; exact List.mem_map_of_mem pointed)

/-- The region from the end of the reserved area to `base` lies apart from the objects of a value
whose blocks lie at or above `base`. -/
theorem below_base_apart {state : Ty} {store : Store Unit} {words : List Value}
    {value : state.denote} {base : Nat} (low : 4096 ≤ base)
    (above : ∀ block ∈ state.blocks store words value, base ≤ block.1) :
    Apart store (state.pointers store words value) (4096, base - 4096) := by
  intro pointer pointed
  have := above _ (by rw [Ty.blocks_pointers]; exact List.mem_map_of_mem pointed)
  simp only [regionsDisjoint]
  omega

/-- The store of a call's result over the current state, followed by the state's compaction. -/
theorem wp_process_store_compact_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {targetHost : HostEnv (Observed World)}
    {store : Store (Observed World)} {heap : Heap} {locals : Locals} {words : List Value}
    {value : ProcessStep state.denote} {rest : Program} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
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
        (Relocation.programWith calls (processCompaction state) ++ rest)) Q store
      { locals with values := words.reverse ++ locals.values } targetHost := by
  have hWidth : (processResultTy state).width ≤ processPositions state := by
    simp only [processPositions, processAux]; omega
  refine wp_storeCode words (processPositions state) 0 (processResultTy state).types locals
    locals.values memory.rep.typed positions (by rw [params]; exact Nat.zero_le _)
    (by rw [Ty.types_length, positions]; omega) fun after frame held above => ?_
  have baseAfter : ({ after with values := locals.values } : Locals).get (processAux state) =
      some (.i64 base) := by
    rw [Locals.get_values, (above (processAux state)
      (by rw [Ty.types_length]; simp only [processAux]; omega)
      (by rw [positions]; simp only [processPositions]; omega)).1]
    exact baseLocal
  exact wp_process_compact_with runtime layout profile compactable form closed memory held baseTop
    baseAfter low poolBelow (frame.params.trans params) (frame.positions.trans positions) cap
    trap fun final after' host caps stored values => next final after' host caps stored values

/-- The store of a step's result over the current state, followed by the state's compaction when
the heap above the base exceeds four times the state's copy cost. -/
theorem wp_process_store_compact_when_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {base : UInt64} {targetHost : HostEnv (Observed World)}
    {store : Store (Observed World)} {heap : Heap} {locals : Locals} {words : List Value}
    {value : ProcessStep state.denote} {rest : Program} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (compactable : state.compactable = true)
    (form : Encoding.ProgramForm (processCompaction state))
    (closed : Relocation.programClosed source.funcs.length (processCompaction state) = true)
    (memory : ProcessMemory (processResultTy state) pool heap (PureTransport.erase store) words
      (processValue state value))
    (free : ∀ node ∈ heap.free, base.toNat ≤ node.region.1)
    (blocksAbove : ∀ block ∈ state.blocks (PureTransport.erase store) (words.drop 2) value.state,
      base.toNat ≤ block.1)
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
        (Relocation.programWith calls (processCompactWhen state) ++ rest)) Q store
      { locals with values := words.reverse ++ locals.values } targetHost := by
  have hWidth : (processResultTy state).width ≤ processPositions state := by
    simp only [processPositions, processAux]; omega
  refine wp_storeCode words (processPositions state) 0 (processResultTy state).types locals
    locals.values memory.rep.typed positions (by rw [params]; exact Nat.zero_le _)
    (by rw [Ty.types_length, positions]; omega) fun after frame held above => ?_
  have baseAfter : ({ after with values := locals.values } : Locals).get (processAux state) =
      some (.i64 base) := by
    rw [Locals.get_values, (above (processAux state)
      (by rw [Ty.types_length]; simp only [processAux]; omega)
      (by rw [positions]; simp only [processPositions]; omega)).1]
    exact baseLocal
  exact wp_process_compact_when_with runtime layout profile compactable form closed memory held
    free blocksAbove baseTop baseAfter low poolBelow (frame.params.trans params)
    (frame.positions.trans positions) cap trap
    fun final after' host caps stored values => next final after' host caps stored values

/-- Every block of a value has a positive length: a header and its payload. -/
theorem blocks_positive {store : Store Unit} {t : Ty} {words : List Value} {value : t.denote}
    {b : Nat × Nat} (member : b ∈ t.blocks store words value) : 0 < b.2 := by
  rw [Ty.blocks_pointers] at member
  obtain ⟨pointer, _, rfl⟩ := List.mem_map.mp member
  simp only [block]
  omega

/-- The state's blocks of a step's result lie at or above `base` when every block that the step
leaves fresh apart from the reserved area does. -/
theorem result_blocks_above {state : Ty} {heap : Heap} {store : Store Unit} {words : List Value}
    {value : (processResultTy state).denote} {base : Nat}
    (rep : (processResultTy state).Rep .owned heap store words value)
    (fresh : ∀ b ∈ (processResultTy state).blocks store words value, 0 < b.2 →
      regionsDisjoint b ABI.low → base ≤ b.1) :
    ∀ block ∈ state.blocks store (words.drop 2) (processNative state value).state,
      base ≤ block.1 := by
  intro block member
  have inResult : block ∈ (processResultTy state).blocks store words value := by
    rw [← processValue_native state value, processValue_blocks]
    exact member
  exact fresh block inResult (blocks_positive inResult)
    (regionsDisjoint_symm (owned_low rep block inResult))

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
  layout_instance wp_process_store_compact_with

theorem wp_process_iteration_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Wasm.Module}
    {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {functions : EffectFuns effectSigs} {process : Process entry.state.denote}
    {host : Host World} {targetHost : HostEnv (Observed World)} {pool : Bytes.LiteralPool}
    {base : UInt64} {initial : Store (Observed World)} {locals : Locals}
    {current : ProcessStep entry.state.denote} {function : Wasm.Function}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (compactable : entry.state.compactable = true)
    (compactForm : Encoding.ProgramForm (processCompaction entry.state))
    (compactClosed :
      Relocation.programClosed source.funcs.length (processCompaction entry.state) = true)
    (spec : EffectSpecWith calls target
      ⟨entry.stepName, [entry.state], [entry.stepMode], .value (processResultTy entry.state)⟩
      (Wrappers.effectIndexWith calls source entry.step.index) (functions.get entry.step) pool)
    (noImport : target.imports[Wrappers.effectIndexWith calls source entry.step.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndexWith calls source entry.step.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1 + widthSum [entry.state])
    (valid : targetHost.Satisfies target (hostSpecWith host calls))
    (poolLow : ∀ region ∈ pool.regions, regionsDisjoint region ABI.low)
    (stepMeaning : ∀ state, process.step state = entry.action functions state)
    (stored : ProcessStored target entry.state pool base current initial locals) :
    wp target (entry.iterationWith calls source)
      (ProcessIterationResult (observedHost host) process current initial.host
        (ProcessStored target entry.state pool base) locals.values) initial locals targetHost := by
  let Q := ProcessIterationResult (observedHost host) process current initial.host
    (ProcessStored target entry.state pool base) locals.values
  obtain ⟨heap, stateWords, memory, held, control, free, above, baseTop, _⟩ := stored.parts
  simp only [ProcessEntry.iterationWith, ProcessEntry.result, List.append_assoc,
    List.cons_append, List.nil_append, wp_localGet_cons, control, wp_eqzI64_cons]
  cases running : current.running with
  | false =>
      simpa [running, boolWord] using
        (ProcessIterationResult.stopped initial locals rfl running stored : Q (.Break 1 initial locals))
  | true =>
      let signature : EffectSig :=
        ⟨entry.stepName, [entry.state], [entry.stepMode], .value (processResultTy entry.state)⟩
      let args : Env [entry.state] := .cons current.state .nil
      have shape := entry.step_args (store := PureTransport.erase initial) memory.rep
      have argsRep : Env.Rep signature.mode heap (PureTransport.erase initial) stateWords args :=
        shape.1
      have moves : Env.moves (PureTransport.erase initial) signature.mode stateWords args =
          entry.state.pointers (PureTransport.erase initial) stateWords current.state := shape.2.1
      have reads : Env.reads (PureTransport.erase initial) signature.mode stateWords args = [] :=
        shape.2.2
      have separate : Separate (PureTransport.erase initial)
          (Env.moves (PureTransport.erase initial) signature.mode stateWords args)
          (Env.reads (PureTransport.erase initial) signature.mode stateWords args) := by
        rw [moves, reads]
        exact memory.separate
      have input : @Bytes.LiteralPool.Input (Env signature.params)
          (Env.represent signature.params signature.modes) pool heap (PureTransport.erase initial)
          stateWords args := by
        refine ⟨memory.static, ?_⟩
        change ∀ region ∈ pool.regions,
          Apart (PureTransport.erase initial)
            (Env.moves (PureTransport.erase initial) signature.mode stateWords args) region
        rw [moves]
        exact memory.pool_apart
      have scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) signature.mode stateWords args,
          regionsDisjoint ABI.low region := by
        rw [reads]
        exact fun _ member => nomatch member
      have callExecution := wp_effect_helper_with (calls := calls) (locals := locals) (values := locals.values)
        (depth := 0) (params := stateWords) (args := args) (Q := Q)
        (rest := storeCode (processPositions entry.state) 0 (processResultTy entry.state).types ++
          (Relocation.programWith calls (processCompactWhen entry.state) ++ [.br 0]))
        spec noImport lookup arity valid memory.at_ argsRep separate input scratch stored.cap
        (fun value finalHeap final words trace execution callStep representation => by
          have called : Step heap (PureTransport.erase initial)
              (fun region => Apart (PureTransport.erase initial)
                  (entry.state.pointers (PureTransport.erase initial) stateWords current.state)
                  region ∧ regionsDisjoint region ABI.low)
              finalHeap (PureTransport.erase final)
              ((processResultTy entry.state).blocks (PureTransport.erase final) words value) :=
            callStep.mono (fun region kept => by rw [moves]; exact kept) (fun _ member => member)
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
            rw [processValue_native entry.state value]
            exact memory.called (fun region member => ⟨memory.pool_apart region member,
              poolLow region member⟩) called representation
          obtain ⟨grown, freeAbove, freshAbove⟩ := called.base_le stored.low baseTop free
            ⟨below_base_apart stored.low above, low_apart_above _⟩
          refine wp_process_store_compact_when_with runtime layout profile compactable compactForm
            compactClosed resultMemory freeAbove (result_blocks_above representation freshAbove)
            grown stored.baseLocal stored.low stored.pool stored.params
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
      ⟨entry.stepName, [entry.state], [entry.stepMode], .value (processResultTy entry.state)⟩
      (Wrappers.effectIndex source entry.step.index) (functions.get entry.step) pool)
    (noImport : target.imports[Wrappers.effectIndex source entry.step.index]? = none)
    (lookup : target.funcs[Wrappers.effectIndex source entry.step.index - target.imports.length]? =
      some function)
    (arity : function.numParams = 1 + widthSum [entry.state])
    (valid : targetHost.Satisfies target (hostSpec host))
    (poolLow : ∀ region ∈ pool.regions, regionsDisjoint region ABI.low)
    (stepMeaning : ∀ state, process.step state = entry.action functions state)
    (stored : ProcessStored target entry.state pool base current initial locals) :
    wp target (entry.iteration source)
      (ProcessIterationResult (observedHost host) process current initial.host
        (ProcessStored target entry.state pool base) locals.values) initial locals targetHost := by
  layout_instance wp_process_iteration_with

end Verified.Wasi
