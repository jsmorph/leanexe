import Verified.Wasi.ReadAllProof
import Verified.Wasi.ReadCommand
import Verified.Wasi.CommandCodeSpec
import Verified.Wasi.CostCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.ResourceCompilerCost
import Verified.AlignedCorrect

/-! The command `readAll limit`: the code of the limit, then the code of `readAll` in the calling
function, with its correctness and its cost. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem readAll_after {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {live : Nat → Bool} {base : Nat} {heap finalHeap : Heap}
    {initial final : Store World} {locals finalLocals : Locals} {root length errno : UInt64}
    {bytes : LeanExe.Bytes}
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots live (PureTransport.erase initial) locals ABI.scratch)
    (step : Step heap (PureTransport.erase initial)
      (fun region => regionsDisjoint region ABI.scratch)
      finalHeap (PureTransport.erase final) (Bytes.regions (PureTransport.erase final) root))
    (frame : Frame base locals finalLocals)
    (rep : Bytes.Rep finalHeap (PureTransport.erase final) root length bytes) :
    After env slots live live base heap initial locals (.value (.pair .word .bytes))
      (errno, bytes) finalHeap final finalLocals [.i64 errno, .i64 root, .i64 length] := by
  refine ⟨?_, frame, vars.step_scratch apart step frame, read_result_rep rep, ?_⟩
  · have fresh : (ResultTy.value (.pair .word .bytes)).fresh (PureTransport.erase final)
        [.i64 errno, .i64 root, .i64 length] (errno, bytes) =
        Bytes.regions (PureTransport.erase final) root :=
      read_result_regions .owned _ _ _ _ _
    rw [fresh]
    exact step.mono (fun _ kept => kept.2) (fun _ member => member)
  · intro type x hLive _ words held width resultRegion hResult region member
    have heldBefore := (vars.hold_agree frame hLive width).mp held
    obtain ⟨same, fresh⟩ := vars.regions_after step hLive heldBefore width
      (fun block hBlock =>
        regionsDisjoint_symm (apart type x hLive words heldBefore width block hBlock))
    rw [same] at member
    have hResult' : resultRegion ∈ Bytes.regions (PureTransport.erase final) root := by
      exact (read_result_regions .owned (PureTransport.erase final) root length errno bytes) ▸
        hResult
    exact regionsDisjoint_symm (fresh region member resultRegion hResult')

theorem readAll_flat {World : Type} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs} {effectFuns : EffectFuns effectSigs} {context : List Ty}
    {limit : Expr pureSigs context .word} {env : Env context} {world final : World}
    {trace : List Event} {outcome : Outcome LeanExe.Wasi.ReadResult}
    (execution : Exec host (readAll (limit.denote funs env)) world trace outcome final) :
    Exec host ((Command.readAll (effectSigs := effectSigs) limit).denote funs effectFuns env)
      world trace (match outcome with
        | .returned result => .returned (result.errno, result.bytes)
        | .exited code => .exited code
        | .trapped message => .trapped message) final := by
  cases outcome with
  | returned result =>
    simpa only [Command.denote, List.append_nil] using
      execution.bind (β := (ResultTy.value (.pair .word .bytes)).denote)
        (next := fun result => .pure (result.errno, result.bytes)) (rest := [])
        (Exec.pure (α := (ResultTy.value (.pair .word .bytes)).denote)
          final (result.errno, result.bytes))
  | exited code =>
    simpa only [Command.denote, List.append_nil] using
      execution.bind (β := (ResultTy.value (.pair .word .bytes)).denote)
        (next := fun result => .pure (result.errno, result.bytes)) (rest := []) ⟨rfl, rfl, rfl⟩
  | trapped message =>
    simpa only [Command.denote, List.append_nil] using
      execution.bind (β := (ResultTy.value (.pair .word .bytes)).denote)
        (next := fun result => .pure (result.errno, result.bytes)) (rest := []) ⟨rfl, rfl, rfl⟩

theorem wp_command_readAll_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs}
    {flags : Flags pureSigs} {bounds : Bounds pureSigs} {fits : Fits pureSigs}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {pool : Bytes.LiteralPool} {context : List Ty} {limit : Expr pureSigs context .word}
    {env : Env context} {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    {params : List Value} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {h base : Nat} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source)
    (spec : CodeSpec source funs flags bounds fits sourceHost params limit env slots paid live pool)
    (form : Encoding.ProgramForm (limit.code (pool := pool) h slots base live ++
      coerceCode h .word (limit.mode (slots.map Slot.mode)) .owned base))
    (closed : Relocation.programClosed source.funcs.length
      (limit.code (pool := pool) h slots base live ++
        coerceCode h .word (limit.mode (slots.map Slot.mode)) .owned base) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => live i || limit.uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || limit.uses i) heap
      (PureTransport.erase initial) locals)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + max limit.width 6 ≤ h)
    (place : limit.placeArgs = true)
    (prefixFailure : (!(limit.fits funs fits env) || !decide
      (heap.Within (PureTransport.erase initial) source
        (returnCost funs flags bounds limit env slots paid live
          (PureTransport.erase initial) locals))) = true →
      ∀ final : Store (Observed World), final.host = initial.host →
        Q (.Trap final "unreachable"))
    (next : ∀ middleHeap (middle : Store (Observed World)) middleLocals,
      After env slots (fun i => live i || limit.uses i) live base heap initial locals
        (.value .word) (limit.denote funs env) middleHeap middle middleLocals
        [.i64 (limit.denote funs env)] →
      middle.host = initial.host →
      (limit.fits funs fits env = true → middleHeap.top.toNat ≤ heap.top.toNat +
        returnCost funs flags bounds limit env slots paid live
          (PureTransport.erase initial) locals) →
      wp target (readAllCodeWith calls base) Q middle
        { middleLocals with values := .i64 (limit.denote funs env) :: locals.values }
        targetHost) :
    wp target ((Command.readAll (effectSigs := effectSigs) limit).codeWith calls
        (pool := pool) source h slots base live) Q initial locals targetHost := by
  have noCoerce : coerceCode h .word (limit.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  have execution := wp_return_with (calls := calls) runtime layout profile spec form closed positions parameters
    vars at_ safe cap low (by simp only [copyWidth, Ty.scalar, ite_true]; omega) place
    (rest := readAllCodeWith calls base) (Q := Q) prefixFailure
    (fun middleHeap middle middleLocals words first sameWorld prefixTop => by
      have wordsEq : words = [.i64 (limit.denote funs env)] := first.rep
      subst words
      exact next middleHeap middle middleLocals first sameWorld prefixTop)
  simpa only [noCoerce, List.append_nil, Command.codeWith] using execution

/-- The code of `readAll` after the limit's code, from the state that the limit's code leaves. -/

theorem wp_command_readAll {World : Type} {source target : Module}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs}
    {flags : Flags pureSigs} {bounds : Bounds pureSigs} {fits : Fits pureSigs}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {pool : Bytes.LiteralPool} {context : List Ty} {limit : Expr pureSigs context .word}
    {env : Env context} {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    {params : List Value} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {h base : Nat} {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (spec : CodeSpec source funs flags bounds fits sourceHost params limit env slots paid live pool)
    (form : Encoding.ProgramForm (limit.code (pool := pool) h slots base live ++
      coerceCode h .word (limit.mode (slots.map Slot.mode)) .owned base))
    (closed : Relocation.programClosed source.funcs.length
      (limit.code (pool := pool) h slots base live ++
        coerceCode h .word (limit.mode (slots.map Slot.mode)) .owned base) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => live i || limit.uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || limit.uses i) heap
      (PureTransport.erase initial) locals)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + max limit.width 6 ≤ h)
    (place : limit.placeArgs = true)
    (prefixFailure : (!(limit.fits funs fits env) || !decide
      (heap.Within (PureTransport.erase initial) source
        (returnCost funs flags bounds limit env slots paid live
          (PureTransport.erase initial) locals))) = true →
      ∀ final : Store (Observed World), final.host = initial.host →
        Q (.Trap final "unreachable"))
    (next : ∀ middleHeap (middle : Store (Observed World)) middleLocals,
      After env slots (fun i => live i || limit.uses i) live base heap initial locals
        (.value .word) (limit.denote funs env) middleHeap middle middleLocals
        [.i64 (limit.denote funs env)] →
      middle.host = initial.host →
      (limit.fits funs fits env = true → middleHeap.top.toNat ≤ heap.top.toNat +
        returnCost funs flags bounds limit env slots paid live
          (PureTransport.erase initial) locals) →
      wp target (readAllCode base) Q middle
        { middleLocals with values := .i64 (limit.denote funs env) :: locals.values }
        targetHost) :
    wp target ((Command.readAll (effectSigs := effectSigs) limit).code
        (pool := pool) source h slots base live) Q initial locals targetHost := by
  layout_instance wp_command_readAll_with
theorem wp_readAll_after_limit_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module} {host : Host World}
    {context : List Ty} {limit : UInt64}
    {env : Env context} {slots : List Slot} {live liveIn : Nat → Bool}
    {heap middleHeap : Heap} {initial middle : Store (Observed World)}
    {locals middleLocals : Locals} {base h : Nat} {aborts : Bool}
    {targetHost : HostEnv (Observed World)} {sourceHost : HostEnv Unit}
    {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (first : After env slots liveIn live base heap initial locals (.value .word) limit
      middleHeap middle middleLocals [.i64 limit])
    (sameWorld : middle.host = initial.host)
    (positions : locals.positions = h) (low : locals.params.length ≤ base)
    (room : base + 6 ≤ h)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hRoom : limit.toNat < 4294963200 → aborts = false →
      middleHeap.Room (PureTransport.erase middle) source (allocSize (limit + 4096)))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable"))
    (hNext : ∀ (finalHeap : Heap) (final : Store (Observed World)) (finalLocals : Locals)
      (root length : UInt64) (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.returned result) final.host →
      After env slots liveIn live base heap initial locals (.value (.pair .word .bytes))
        (result.errno, result.bytes) finalHeap final finalLocals
        [.i64 result.errno, .i64 root, .i64 length] →
      finalHeap.top.toNat ≤ middleHeap.top.toNat + readAllCost limit →
      Q (.Fallthrough final
        { finalLocals with values := .i64 length :: .i64 root :: .i64 result.errno ::
          locals.values }))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.trapped message) final.host →
      Q (.Trap final message)) :
    wp target (readAllCodeWith calls base) Q middle
      { middleLocals with values := .i64 limit :: locals.values } targetHost := by
  have hLowM : middleLocals.params.length ≤ base := by rw [first.frame.params]; exact low
  have hHighM : base + 6 ≤ middleLocals.positions := by
    rw [first.frame.positions, positions]
    exact room
  rw [← List.append_nil (readAllCodeWith calls base)]
  refine wp_readAll_with (s := middleLocals) (values := locals.values) runtime layout profile hImports
    sourceHost hHost first.step.at_ (by rw [first.step.cap source]; exact cap) hLowM hHighM hRoom
    (fun allowed final finalWorld => hResource allowed final (finalWorld.trans sameWorld)) ?_ ?_
  · intro finalHeap final finalLocals root length result trace readExecution readStep rep top
      readFrame
    rw [wp_nil]
    have primitive := readAll_after (errno := result.errno) first.holds
      (first.scratch vars apart selected) readStep readFrame rep
    have after := After.thenWord vars apart first primitive selected (fun _ hLive => hLive)
    exact hNext finalHeap final finalLocals root length result trace
      (by rw [← sameWorld]; exact readExecution) after top
  · intro finalHeap final root message trace readExecution _ _
    exact hTrap final message trace (by rw [← sameWorld]; exact readExecution)

theorem wp_readAll_after_limit {World : Type} {source target : Module} {host : Host World}
    {context : List Ty} {limit : UInt64}
    {env : Env context} {slots : List Slot} {live liveIn : Nat → Bool}
    {heap middleHeap : Heap} {initial middle : Store (Observed World)}
    {locals middleLocals : Locals} {base h : Nat} {aborts : Bool}
    {targetHost : HostEnv (Observed World)} {sourceHost : HostEnv Unit}
    {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (hHost : targetHost.Satisfies target (hostSpec host))
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (first : After env slots liveIn live base heap initial locals (.value .word) limit
      middleHeap middle middleLocals [.i64 limit])
    (sameWorld : middle.host = initial.host)
    (positions : locals.positions = h) (low : locals.params.length ≤ base)
    (room : base + 6 ≤ h)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (hRoom : limit.toNat < 4294963200 → aborts = false →
      middleHeap.Room (PureTransport.erase middle) source (allocSize (limit + 4096)))
    (hResource : aborts = true → ∀ final : Store (Observed World),
      final.host = initial.host → Q (.Trap final "unreachable"))
    (hNext : ∀ (finalHeap : Heap) (final : Store (Observed World)) (finalLocals : Locals)
      (root length : UInt64) (result : LeanExe.Wasi.ReadResult) (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.returned result) final.host →
      After env slots liveIn live base heap initial locals (.value (.pair .word .bytes))
        (result.errno, result.bytes) finalHeap final finalLocals
        [.i64 result.errno, .i64 root, .i64 length] →
      finalHeap.top.toNat ≤ middleHeap.top.toNat + readAllCost limit →
      Q (.Fallthrough final
        { finalLocals with values := .i64 length :: .i64 root :: .i64 result.errno ::
          locals.values }))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) (readAll limit) initial.host trace (.trapped message) final.host →
      Q (.Trap final message)) :
    wp target (readAllCode base) Q middle
      { middleLocals with values := .i64 limit :: locals.values } targetHost := by
  layout_instance wp_readAll_after_limit_with

theorem command_readAll_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    (limit : Expr pureSigs context .word) :
    CommandCodeSpecWith calls source target pure effects pool (.readAll limit) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid _ depthParam positions vars at_ safe scratch cap low room ready covered place
  have fragment := ready _ (List.mem_singleton_self _)
  have spec := limit.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) covered
    (fun _ => depthParam) env slots [] live
  have noCoerce : coerceCode h .word (limit.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  have selected : ∀ i, live i = true → (live i || limit.uses i) = true := by
    intro i hLive
    simp only [hLive, Bool.true_or]
  refine wp_command_readAll_with facts.runtime facts.layout facts.profile spec
    (by simpa only [noCoerce, List.append_nil] using fragment.1)
    (by simpa only [noCoerce, List.append_nil] using fragment.2)
    positions rfl vars at_ safe cap low (by simpa only [Command.width] using room) place
    (fun _ final sameWorld => CommandResult.resource_refl rfl sameWorld) ?_
  intro middleHeap middle middleLocals first sameWorld _
  refine wp_readAll_after_limit_with (sourceHost := sourceHost) facts.runtime facts.layout
    facts.profile facts.imports valid vars scratch selected first sameWorld positions low
    (by simp only [Command.width] at room; omega) cap
    (fun _ impossible => Bool.noConfusion impossible)
    (fun allowed final finalWorld => CommandResult.resource_refl allowed finalWorld) ?_ ?_
  · intro finalHeap final finalLocals root length result trace readExecution after _
    exact CommandResult.returned (result := .value (.pair .word .bytes))
      (result.errno, result.bytes) finalHeap final finalLocals
      [.i64 result.errno, .i64 root, .i64 length] trace (readAll_flat readExecution) after
  · intro final message trace readExecution
    exact CommandResult.terminal final trace (.trapped message) message
      (readAll_flat readExecution) rfl

theorem command_readAll_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFacts source target pure effects pool) (sourceHost : HostEnv Unit)
    (limit : Expr pureSigs context .word) :
    CommandCodeSpec source target pure effects pool (.readAll limit) := by
  layout_instance command_readAll_spec_with

theorem cost_command_readAll_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure (program.funs pure.funs) pool)
    (sourceHost : HostEnv Unit) (limit : Expr pureSigs context .word) :
    CostCommandCodeSpecWith calls source target pure program pool (.readAll limit) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid _ depthParam positions vars at_ safe scratch cap low room ready covered place resource
  have fragment := ready _ (List.mem_singleton_self _)
  have spec := limit.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) covered
    (fun _ => depthParam) env slots [] live
  have noCoerce : coerceCode h .word (limit.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  have selected : ∀ i, live i = true → (live i || limit.uses i) = true := by
    intro index used
    simp only [used, Bool.true_or]
  have allowed : (!(limit.fits pure.funs (pure.callFits depth) env) || !decide
      (heap.Within (PureTransport.erase initial) source
        (returnCost pure.funs pure.flags (pure.callBounds depth) limit env slots [] live
          (PureTransport.erase initial) locals))) = true → aborts = true := by
    intro failure
    cases aborts with
    | true => rfl
    | false =>
      obtain ⟨within, bounded⟩ := resource rfl
      obtain ⟨withinRead, fitsLimit⟩ := bounded.readAll_resources locals within
      have withinLimit := withinRead.mono (Nat.le_add_right _ _)
      simp only [Resource.PureContext.exprFits] at fitsLimit
      simp [fitsLimit, withinLimit] at failure
  refine wp_command_readAll_with facts.runtime facts.layout facts.profile spec
    (by simpa only [noCoerce, List.append_nil] using fragment.1)
    (by simpa only [noCoerce, List.append_nil] using fragment.2)
    positions rfl vars at_ safe cap low (by simpa only [Command.width] using room) place
    (fun failure final sameWorld =>
      .trapped final "unreachable" (CommandResult.resource_refl (allowed failure) sameWorld)) ?_
  intro middleHeap middle middleLocals first sameWorld prefixTop
  refine wp_readAll_after_limit_with (sourceHost := sourceHost) facts.runtime facts.layout
    facts.profile facts.imports valid vars scratch selected first sameWorld positions low
    (by simp only [Command.width] at room; omega) cap ?_
    (fun allowed final finalWorld =>
      .trapped final "unreachable" (CommandResult.resource_refl allowed finalWorld)) ?_ ?_
  · intro small noAbort
    obtain ⟨within, bounded⟩ := resource noAbort
    obtain ⟨withinRead, fitsLimit⟩ := bounded.readAll_resources locals within
    apply readAll_room_of_budget small (by rw [first.step.cap source]; exact cap)
    exact withinRead.shift (prefixTop fitsLimit) le_rfl (first.step.cap source)
  · intro finalHeap final finalLocals root length result trace readExecution after top
    refine CostCommandResult.returned (result := .value (.pair .word .bytes))
      (result.errno, result.bytes) finalHeap final finalLocals
      [.i64 result.errno, .i64 root, .i64 length] trace
      (pure.readAllCost depth (slots.map Slot.mode) live limit env)
      (pure.exprFits depth limit env)
      (.readAll program depth (slots.map Slot.mode) live limit env
        (readAll_flat readExecution)) after ?_
    intro fitsLimit
    have prefixGrowth := prefixTop fitsLimit
    rw [pure.returnWordCost_nil] at prefixGrowth
    change finalHeap.top.toNat ≤ heap.top.toNat +
      (pure.exprCost depth (slots.map Slot.mode) live limit env +
        readAllCost (limit.denote pure.funs env))
    omega
  · intro final message trace readExecution
    exact .trapped final message
      (.terminal final trace (.trapped message) message (readAll_flat readExecution) rfl)

theorem cost_command_readAll_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool)
    (sourceHost : HostEnv Unit) (limit : Expr pureSigs context .word) :
    CostCommandCodeSpec source target pure program pool (.readAll limit) := by
  layout_instance cost_command_readAll_spec_with

end Verified.Wasi
