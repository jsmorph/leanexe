import Verified.Wasi.CallWrappers
import Verified.Wasi.AfterScratch
import Verified.Wasi.CommandSpec
import Verified.Wasi.Return

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem read_result_rep {heap : Heap} {store : Store Unit} {root length errno : UInt64}
    {bytes : LeanExe.Bytes} (rep : Bytes.Rep heap store root length bytes) :
    (Ty.pair .word .bytes).Rep .owned heap store [.i64 errno, .i64 root, .i64 length]
      (errno, bytes) := by
  refine ⟨[.i64 errno], [.i64 root, .i64 length], rfl, rfl, ⟨root, length, rfl, rep⟩, ?_⟩
  intro _ region member
  exact nomatch member

theorem read_result_regions (mode : Mode) (store : Store Unit) (root length errno : UInt64)
    (bytes : LeanExe.Bytes) :
    (Ty.pair .word .bytes).regions mode store [.i64 errno, .i64 root, .i64 length]
      (errno, bytes) = Bytes.regions store root := by
  cases mode <;>
    change (Bytes.roots [.i64 root, .i64 length]).map (block store) = Bytes.regions store root
  all_goals exact Bytes.roots_regions store root length

theorem read_after {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {live : Nat → Bool} {base : Nat} {heap finalHeap : Heap}
    {initial final : Store World} {locals : Locals} {root length errno : UInt64}
    {bytes : LeanExe.Bytes}
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots live (PureTransport.erase initial) locals ABI.scratch)
    (step : Step heap (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      finalHeap (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root))
    (rep : Bytes.Rep finalHeap (PureTransport.erase final) root length bytes) :
    After env slots live live base heap initial locals (.value (.pair .word .bytes))
      (errno, bytes) finalHeap final locals [.i64 errno, .i64 root, .i64 length] := by
  refine ⟨?_, Frame.refl base locals,
    vars.step_scratch apart step (Frame.refl base locals), read_result_rep rep, ?_⟩
  · have fresh : (ResultTy.value (.pair .word .bytes)).fresh (PureTransport.erase final)
        [.i64 errno, .i64 root, .i64 length] (errno, bytes) =
        Bytes.regions (PureTransport.erase final) root :=
      read_result_regions .owned _ _ _ _ _
    rw [fresh]
    exact step.mono (fun _ kept => kept.2) (fun _ member => member)
  · intro type x hLive _ words held width resultRegion hResult region member
    obtain ⟨same, fresh⟩ := vars.regions_after step hLive held width
      (fun block hBlock => regionsDisjoint_symm (apart type x hLive words held width block hBlock))
    rw [same] at member
    have hResult' : resultRegion ∈ Bytes.regions (PureTransport.erase final) root := by
      exact (read_result_regions .owned (PureTransport.erase final) root length errno bytes) ▸ hResult
    exact regionsDisjoint_symm (fresh region member resultRegion hResult')

theorem wp_read_command_call {World : Type} {source target : Module} {host : Host World}
    {context : List Ty} {env : Env context} {slots : List Slot} {live : Nat → Bool}
    {base : Nat} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {capacity : UInt64} {typeIdx : Nat} {aborts : Bool} {targetHost : HostEnv (Observed World)}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit)
    (hFunction : target.funcs[source.funcs.length]? = some (readFunction typeIdx))
    (hHost : targetHost.Satisfies target (hostSpec host))
    (hHeap : heap.At (PureTransport.erase initial))
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots live (PureTransport.erase initial) locals ABI.scratch)
    (hCap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hRoom : capacity.toNat < 4294967296 → capacity ≠ 0 → aborts = false →
      heap.Room (PureTransport.erase initial) source (allocSize capacity)) :
    wp target [.call (Wrappers.readIndex source)]
      (CommandResult host env slots live live base (.value (.pair .word .bytes))
        (Action.bind (readSome capacity) fun result => .pure (result.errno, result.bytes))
        heap initial locals aborts)
      initial { locals with values := .i64 capacity :: locals.values } targetHost := by
  refine wp_read_helper runtime layout profile hImports sourceHost hFunction hHost hHeap hCap
    hRoom ?_ ?_ ?_
  · intro finalHeap final root length result trace execution step rep _
    rw [wp_nil]
    have flat : Exec (observedHost host)
        (Action.bind (readSome capacity) fun result => .pure (result.errno, result.bytes))
        initial.host trace (.returned (result.errno, result.bytes)) final.host := by
      simpa only [List.append_nil] using
        execution.bind (next := fun result => .pure (result.errno, result.bytes))
          (rest := []) (.pure final.host (result.errno, result.bytes))
    exact CommandResult.returned (result := .value (.pair .word .bytes))
      (result.errno, result.bytes) finalHeap final locals
      [.i64 result.errno, .i64 root, .i64 length] trace flat
      (read_after vars apart step rep)
  · intro finalHeap final root message trace execution _ _
    have flat : Exec (observedHost host)
        (Action.bind (readSome capacity) fun result => .pure (result.errno, result.bytes))
        initial.host trace (.trapped message) final.host := by
      simpa only [List.append_nil] using
        execution.bind (next := fun result => .pure (result.errno, result.bytes))
          (rest := []) ⟨rfl, rfl, rfl⟩
    exact CommandResult.terminal final trace (.trapped message) message flat rfl
  · intro allowed final sameWorld
    exact CommandResult.resource_refl allowed sameWorld

theorem wp_command_read {World : Type} {source target : Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs} {effectFuns : EffectFuns effectSigs}
    {flags : Flags pureSigs} {bounds : Bounds pureSigs} {fits : Fits pureSigs}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {pool : Bytes.LiteralPool} {context : List Ty} {capacity : Expr pureSigs context .word}
    {env : Env context} {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    {params : List Value} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {h base typeIdx : Nat} {aborts : Bool}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (hFunction : target.funcs[source.funcs.length]? = some (readFunction typeIdx))
    (hHost : targetHost.Satisfies target (hostSpec host))
    (spec : CodeSpec source funs flags bounds fits sourceHost params capacity env slots paid live pool)
    (form : Encoding.ProgramForm (capacity.code (pool := pool) h slots base live ++
      coerceCode h .word (capacity.mode (slots.map Slot.mode)) .owned base))
    (closed : Relocation.programClosed source.funcs.length
      (capacity.code (pool := pool) h slots base live ++
        coerceCode h .word (capacity.mode (slots.map Slot.mode)) .owned base) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => live i || capacity.uses i) base heap
      (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots (fun i => live i || capacity.uses i)
      (PureTransport.erase initial) locals ABI.scratch)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || capacity.uses i) heap
      (PureTransport.erase initial) locals)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + max capacity.width (copyWidth .word) ≤ h)
    (place : capacity.placeArgs = true)
    (prefixFailure : (!(capacity.fits funs fits env) || !decide
      (heap.Within (PureTransport.erase initial) source
        (returnCost funs flags bounds capacity env slots paid live
          (PureTransport.erase initial) locals))) = true → aborts = true)
    (readRoom : ∀ middleHeap (middle : Store (Observed World)) middleLocals,
      After env slots (fun i => live i || capacity.uses i) live base heap initial locals
        (.value .word) (capacity.denote funs env) middleHeap middle middleLocals
        [.i64 (capacity.denote funs env)] →
      (capacity.fits funs fits env = true → middleHeap.top.toNat ≤ heap.top.toNat +
        returnCost funs flags bounds capacity env slots paid live
          (PureTransport.erase initial) locals) →
      (capacity.denote funs env).toNat < 4294967296 → capacity.denote funs env ≠ 0 →
      aborts = false → middleHeap.Room (PureTransport.erase middle) source
        (allocSize (capacity.denote funs env))) :
    wp target ((Command.read (effectSigs := effectSigs) capacity).code
        (pool := pool) source h slots base live)
      (CommandResult host env slots (fun i => live i || capacity.uses i) live base
        (.value (.pair .word .bytes))
        ((Command.read capacity).denote funs effectFuns env)
        heap initial locals aborts) initial locals targetHost := by
  have selected : ∀ i, live i = true → (live i || capacity.uses i) = true := by
    intro i hLive
    simp only [hLive, Bool.true_or]
  have noCoerce : coerceCode h .word (capacity.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  have execution := wp_return runtime layout profile spec form closed positions parameters
    vars at_ safe cap low room place (rest := [.call (Wrappers.readIndex source)])
    (Q := CommandResult host env slots (fun i => live i || capacity.uses i) live base
      (.value (.pair .word .bytes))
      ((Command.read capacity).denote funs effectFuns env) heap initial locals aborts)
    (fun failure final sameWorld => CommandResult.resource_refl (prefixFailure failure) sameWorld)
    (fun middleHeap middle middleLocals words first sameWorld prefixTop => by
      have wordsEq : words = [.i64 (capacity.denote funs env)] := first.rep
      subst words
      refine wp_read_helper runtime layout profile hImports sourceHost hFunction hHost first.step.at_
        (by rw [first.step.cap source]; exact cap)
        (readRoom middleHeap middle middleLocals first prefixTop) ?_ ?_ ?_
      · intro finalHeap final root length result trace readExecution readStep rep _
        rw [wp_nil]
        have primitive := read_after (errno := result.errno) first.holds
          (first.scratch vars apart selected) readStep rep
        have after := After.thenWord vars apart first primitive selected (fun _ hLive => hLive)
        have returned : Exec (observedHost host) (readSome (capacity.denote funs env))
            initial.host trace (.returned result) final.host := by
          rw [← sameWorld]
          exact readExecution
        have flat : Exec (observedHost host)
            ((Command.read capacity).denote funs effectFuns env)
            initial.host trace (.returned (result.errno, result.bytes)) final.host := by
          simpa only [Command.denote, List.append_nil] using
            returned.bind (β := (ResultTy.value (.pair .word .bytes)).denote)
              (next := fun result => .pure (result.errno, result.bytes))
              (rest := [])
              (Exec.pure (α := (ResultTy.value (.pair .word .bytes)).denote)
                final.host (result.errno, result.bytes))
        exact CommandResult.returned (result := .value (.pair .word .bytes))
          (result.errno, result.bytes) finalHeap final middleLocals
          [.i64 result.errno, .i64 root, .i64 length] trace flat after
      · intro finalHeap final root message trace readExecution _ _
        have trapped : Exec (observedHost host) (readSome (capacity.denote funs env))
            initial.host trace (.trapped message) final.host := by
          rw [← sameWorld]
          exact readExecution
        have flat : Exec (observedHost host)
            ((Command.read capacity).denote funs effectFuns env)
            initial.host trace (.trapped message) final.host := by
          simpa only [Command.denote, List.append_nil] using
            trapped.bind (β := (ResultTy.value (.pair .word .bytes)).denote)
              (next := fun result => .pure (result.errno, result.bytes))
              (rest := []) ⟨rfl, rfl, rfl⟩
        exact CommandResult.terminal final trace (.trapped message) message flat rfl
      · intro allowed final finalWorld
        exact CommandResult.resource_refl allowed (finalWorld.trans sameWorld))
  simpa only [noCoerce, List.append_nil, Command.code] using execution

theorem wp_command_read_budget {World : Type} {source target : Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs} {effectFuns : EffectFuns effectSigs}
    {flags : Flags pureSigs} {bounds : Bounds pureSigs} {fits : Fits pureSigs}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {pool : Bytes.LiteralPool} {context : List Ty} {capacity : Expr pureSigs context .word}
    {env : Env context} {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    {params : List Value} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {h base typeIdx : Nat}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (hFunction : target.funcs[source.funcs.length]? = some (readFunction typeIdx))
    (hHost : targetHost.Satisfies target (hostSpec host))
    (spec : CodeSpec source funs flags bounds fits sourceHost params capacity env slots paid live pool)
    (form : Encoding.ProgramForm (capacity.code (pool := pool) h slots base live ++
      coerceCode h .word (capacity.mode (slots.map Slot.mode)) .owned base))
    (closed : Relocation.programClosed source.funcs.length
      (capacity.code (pool := pool) h slots base live ++
        coerceCode h .word (capacity.mode (slots.map Slot.mode)) .owned base) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => live i || capacity.uses i) base heap
      (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots (fun i => live i || capacity.uses i)
      (PureTransport.erase initial) locals ABI.scratch)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || capacity.uses i) heap
      (PureTransport.erase initial) locals)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + max capacity.width (copyWidth .word) ≤ h)
    (place : capacity.placeArgs = true) (fits_ : capacity.fits funs fits env = true)
    (budget : heap.Within (PureTransport.erase initial) source
      (returnCost funs flags bounds capacity env slots paid live
        (PureTransport.erase initial) locals + readCost (capacity.denote funs env))) :
    wp target ((Command.read (effectSigs := effectSigs) capacity).code
        (pool := pool) source h slots base live)
      (CommandResult host env slots (fun i => live i || capacity.uses i) live base
        (.value (.pair .word .bytes))
        ((Command.read capacity).denote funs effectFuns env)
        heap initial locals false) initial locals targetHost := by
  refine wp_command_read runtime layout profile hImports hFunction hHost spec form closed
    positions parameters vars apart at_ safe cap low room place ?_ ?_
  · intro failure
    have prefixBudget : heap.Within (PureTransport.erase initial) source
        (returnCost funs flags bounds capacity env slots paid live
          (PureTransport.erase initial) locals) := budget.mono (Nat.le_add_right _ _)
    simp [fits_, prefixBudget] at failure
  · intro middleHeap middle middleLocals first prefixTop small nonzero _
    apply read_room_of_budget small nonzero (by rw [first.step.cap source]; exact cap)
    exact budget.shift (prefixTop fits_) le_rfl (first.step.cap source)

end Verified.Wasi
