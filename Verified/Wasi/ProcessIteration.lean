import Verified.Wasi.ProcessMemory
import Verified.Wasi.ProcessLoop
import Verified.Wasi.CallHelper
import Verified.Wasi.PurePrefix
import Verified.Heap

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

structure ProcessStored {World : Type} (target : Wasm.Module) (state : Ty)
    (pool : Bytes.LiteralPool) (current : ProcessStep state.denote)
    (store : Store (Observed World)) (locals : Locals) : Prop where
  represented : ∃ heap words,
    ProcessMemory (processResultTy state) pool heap (PureTransport.erase store)
      words (processValue state current) ∧
    LocalsHold locals 0 (processResultTy state).types words
  params : locals.params = []
  positions : locals.positions = 2 * (processResultTy state).width
  cap : (PureTransport.erase store).memoryCap target 0 ≤ 65535

theorem ProcessStored.parts {World : Type} {target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {current : ProcessStep state.denote}
    {store : Store (Observed World)} {locals : Locals}
    (stored : ProcessStored target state pool current store locals) :
    ∃ heap stateWords,
      ProcessMemory state pool heap (PureTransport.erase store) stateWords current.state ∧
      LocalsHold locals 2 state.types stateWords ∧
      locals.get 0 = some (.i64 (boolWord current.running)) := by
  obtain ⟨heap, words, memory, held⟩ := stored.represented
  obtain ⟨stateWords, wordsEq, _⟩ := processValue_rep.mp memory.rep
  have dropped : words.drop 2 = stateWords := by simp [wordsEq]
  have stateMemory : ProcessMemory state pool heap (PureTransport.erase store)
      stateWords current.state := by
    simpa only [dropped] using memory.state
  have split := (LocalsHold.append (s := locals) (loc := 0)
    (tys1 := [.i64, .i64]) (tys2 := state.types)
    (first := [.i64 (boolWord current.running), .i64 current.status])
    (second := stateWords) rfl).mp
      (by simpa only [processResult_types, wordsEq] using held)
  refine ⟨heap, stateWords, stateMemory, ?_, ?_⟩
  · simpa only [List.length_cons, List.length_nil, Nat.zero_add] using split.2
  · have first := split.1 0 (by simp)
    change locals.get 0 = some (.i64 (boolWord current.running)) at first
    exact first

theorem ProcessStored.status {World : Type} {target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {current : ProcessStep state.denote}
    {store : Store (Observed World)} {locals : Locals}
    (stored : ProcessStored target state pool current store locals) :
    locals.get 1 = some (.i64 current.status) := by
  obtain ⟨heap, words, memory, held⟩ := stored.represented
  obtain ⟨stateWords, wordsEq, _⟩ := processValue_rep.mp memory.rep
  have split := (LocalsHold.append (s := locals) (loc := 0)
    (tys1 := [.i64, .i64]) (tys2 := state.types)
    (first := [.i64 (boolWord current.running), .i64 current.status])
    (second := stateWords) rfl).mp
      (by simpa only [processResult_types, wordsEq] using held)
  have status := split.1 1 (by simp)
  change locals.get 1 = some (.i64 current.status) at status
  exact status

theorem ProcessStored.values {World : Type} {target : Wasm.Module} {state : Ty}
    {pool : Bytes.LiteralPool} {current : ProcessStep state.denote}
    {store : Store (Observed World)} {locals : Locals} (values : List Value)
    (stored : ProcessStored target state pool current store locals) :
    ProcessStored target state pool current store { locals with values } :=
  { represented := by
      obtain ⟨heap, words, memory, held⟩ := stored.represented
      exact ⟨heap, words, memory, held⟩
    params := stored.params
    positions := stored.positions
    cap := stored.cap }

theorem wp_process_replace {World : Type} {source target : Wasm.Module}
    {state : Ty} {pool : Bytes.LiteralPool} {targetHost : HostEnv (Observed World)}
    {initial middle : Store (Observed World)} {heap middleHeap : Heap} {locals : Locals}
    {oldWords resultWords : List Value} {oldValue : state.denote}
    {resultValue : (processResultTy state).denote} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (releaseForm : Encoding.ProgramForm (releaseCode state 2))
    (releaseClosed : Relocation.programClosed source.funcs.length (releaseCode state 2) = true)
    (memory : ProcessMemory state pool heap (PureTransport.erase initial) oldWords oldValue)
    (held : LocalsHold locals 2 state.types oldWords)
    (params : locals.params = [])
    (positions : locals.positions = 2 * (processResultTy state).width)
    (cap : (PureTransport.erase initial).memoryCap target 0 ≤ 65535)
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (called : Step heap (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch) middleHeap (PureTransport.erase middle)
      ((processResultTy state).blocks (PureTransport.erase middle) resultWords resultValue))
    (rep : (processResultTy state).Rep .owned middleHeap (PureTransport.erase middle)
      resultWords resultValue)
    (next : ∀ final after, final.host = middle.host →
      ProcessStored target state pool (processNative state resultValue) final after →
      Q (.Break 0 final after)) :
    wp target
      (storeCode (2 * (processResultTy state).width) (processResultTy state).width
          (processResultTy state).types ++
        Relocation.program (releaseCode state 2) ++
        loadCode (2 * (processResultTy state).width) (processResultTy state).width
          (processResultTy state).types ++
        storeCode (2 * (processResultTy state).width) 0 (processResultTy state).types ++ [.br 0])
      Q middle { locals with values := resultWords.reverse ++ locals.values } targetHost := by
  simp only [List.append_assoc]
  refine wp_storeCode resultWords (2 * (processResultTy state).width)
    (processResultTy state).width (processResultTy state).types locals locals.values
    rep.typed positions (by rw [params]; exact Nat.zero_le _) (by
      rw [Ty.types_length, positions]
      omega) fun stored frame resultHeld _ => ?_
  let saved := { stored with values := locals.values }
  have savedPositions : saved.positions = 2 * (processResultTy state).width :=
    frame.positions.trans positions
  have savedParams : saved.params = [] := frame.params.trans params
  have oldHeld : LocalsHold saved 2 state.types oldWords := by
    apply (LocalsHold.frame (loc := 2) (tys := state.types) (ws := oldWords) frame memory.rep.typed
      (by simp only [Ty.types_length, processResult_width, Nat.le_refl])).mpr
    exact held
  have oldRep := (memory.rep.step called (fun region member =>
    regionsDisjoint_symm (owned_scratch memory.rep region member))).1
  let releasePost : Assertion Unit := fun continuation => match continuation with
    | .Fallthrough final after => ∃ finalHeap,
        Step middleHeap (PureTransport.erase middle)
          (fun region => ∀ block ∈ state.blocks (PureTransport.erase middle) oldWords oldValue,
            regionsDisjoint region block) finalHeap final [] ∧ after = saved
    | _ => False
  have releasePure : wp source (releaseCode state 2) releasePost
      (PureTransport.erase middle) saved (HostEnv.empty : HostEnv Unit) := by
    have released := wp_releaseCode (host := HostEnv.empty) runtime state called.at_ oldRep oldHeld
      (rest := []) (Q := releasePost) fun finalHeap final evolution _ => by
        rw [wp_nil]
        exact ⟨finalHeap, evolution, rfl⟩
    simpa only [List.append_nil] using released
  have transported := PureTransport.wp_prefix layout profile releaseForm releaseClosed middle.host
    releasePure (targetHost := targetHost)
    (rest := loadCode (2 * (processResultTy state).width) (processResultTy state).width
        (processResultTy state).types ++
      storeCode (2 * (processResultTy state).width) 0 (processResultTy state).types ++ [.br 0])
    (Q := Q) (fun continuation post => by
      cases continuation with
      | Fallthrough final after =>
          obtain ⟨finalHeap, evolution, rfl⟩ := post
          have resultMemory := (memory.afterStep poolScratch called rep evolution).1
          have storedMemory : ProcessMemory (processResultTy state) pool finalHeap final
              resultWords (processValue state (processNative state resultValue)) := by
            simpa only [processValue_native] using resultMemory
          have finalCap : final.memoryCap target 0 ≤ 65535 := by
            rw [evolution.cap target, called.cap target]
            exact cap
          simp only [List.append_assoc]
          refine wp_loadCode resultWords rep.typed savedPositions resultHeld ?_
          refine wp_storeCode resultWords (2 * (processResultTy state).width) 0
            (processResultTy state).types saved locals.values rep.typed savedPositions
            (by rw [savedParams]; rfl) (by rw [Ty.types_length, savedPositions]; omega)
            fun copied copiedFrame copiedHeld _ => ?_
          rw [wp_br_cons]
          apply next (PureTransport.restore middle.host final)
            { copied with values := locals.values } rfl
          refine ⟨⟨finalHeap, resultWords, ?_, copiedHeld⟩,
            copiedFrame.params.trans savedParams, copiedFrame.positions.trans savedPositions, ?_⟩
          · simpa only [PureTransport.erase_restore] using storedMemory
          · simpa only [PureTransport.erase_restore] using finalCap
      | _ => exact False.elim post)
  simpa only [PureTransport.restore_erase, saved, List.append_assoc] using transported

theorem wp_process_iteration {World : Type} {source target : Wasm.Module}
    {effectSigs : List EffectSig} {entry : ProcessEntry effectSigs}
    {functions : EffectFuns effectSigs} {process : Process entry.state.denote}
    {host : Host World} {targetHost : HostEnv (Observed World)} {pool : Bytes.LiteralPool}
    {initial : Store (Observed World)} {locals : Locals}
    {current : ProcessStep entry.state.denote} {function : Wasm.Function}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (releaseForm : Encoding.ProgramForm (releaseCode entry.state 2))
    (releaseClosed : Relocation.programClosed source.funcs.length (releaseCode entry.state 2) = true)
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
    (stored : ProcessStored target entry.state pool current initial locals) :
    wp target (entry.iteration source)
      (ProcessIterationResult (observedHost host) process current initial.host
        (ProcessStored target entry.state pool) locals.values) initial locals targetHost := by
  let Q := ProcessIterationResult (observedHost host) process current initial.host
    (ProcessStored target entry.state pool) locals.values
  obtain ⟨heap, stateWords, memory, held, control⟩ := stored.parts
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
        (rest := storeCode (2 * (processResultTy entry.state).width) (processResultTy entry.state).width
            (processResultTy entry.state).types ++
          Relocation.program (releaseCode entry.state 2) ++
          loadCode (2 * (processResultTy entry.state).width) (processResultTy entry.state).width
            (processResultTy entry.state).types ++
          storeCode (2 * (processResultTy entry.state).width) 0 (processResultTy entry.state).types ++ [.br 0])
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
          apply wp_process_replace runtime layout profile releaseForm releaseClosed memory held
            stored.params stored.positions stored.cap poolScratch called representation
          intro released after sameWorld nextStored
          exact ProcessIterationResult.next (processNative entry.state value) released after trace running
            (by simpa only [sameWorld] using nativeExecution)
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
