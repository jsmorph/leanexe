import Verified.Wasi.SysFlat
import Verified.Wasi.SysReported
import Verified.Wasi.SysResult
import Verified.Wasi.CostCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.CostResults
import Verified.Wasi.ResourcePrefix
import Verified.Wasi.ResultRelease
import Verified.Wasi.WriteCommand

/-! The command `sys`: its code from the argument variables to the result words, with its
correctness and its cost.  `SysResult` is the outcome that both specifications need: a returned
value with the state after the command and the heap that the command allocated, or a trap that
`CommandResult` accepts. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

inductive SysResult {World : Type} {context : List Ty} (host : Host World) (env : Env context)
    (slots : List Slot) (liveIn live : Nat → Bool) (base : Nat) (form : SysForm)
    (action : Action form.ty.denote) (cost : List Event → Nat) (heap : Heap)
    (initial : Store (Observed World)) (locals : Locals) (aborts : Bool) :
    Continuation (Observed World) → Prop where
  | returned (value : form.ty.denote) (finalHeap : Heap) (final : Store (Observed World))
      (finalLocals : Locals) (words : List Value) (trace : List Event)
      (execution : Exec (observedHost host) action initial.host trace (.returned value) final.host)
      (after : After env slots liveIn live base heap initial locals (.value form.ty) value
        finalHeap final finalLocals words)
      (top : finalHeap.top.toNat ≤ heap.top.toNat + cost trace) :
      SysResult host env slots liveIn live base form action cost heap initial locals aborts
        (.Fallthrough final { finalLocals with values := words.reverse ++ locals.values })
  | trapped (final : Store (Observed World)) (message : String)
      (result : CommandResult host env slots liveIn live base (.value form.ty) action heap initial
        locals aborts (.Trap final message)) :
      SysResult host env slots liveIn live base form action cost heap initial locals aborts
        (.Trap final message)

/-- The argument variables of a `sys` command hold their words in their locals below `base`. -/
theorem sys_args_held {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    (vars : Holds env slots liveIn base heap store locals) :
    ∀ (args : List (Var context .word)), (∀ arg ∈ args, liveIn arg.index = true) →
    List.Forall₂ (fun place value => locals.get place = some (.i64 value))
      (args.map fun arg => (slots.getD arg.index default).loc) (args.map env.get) ∧
    ∀ place ∈ args.map (fun arg => (slots.getD arg.index default).loc), place < base
  | [], _ => ⟨.nil, fun _ member => by simp at member⟩
  | arg :: args, live => by
    obtain ⟨bound, words, hold, rep⟩ := vars.1 .word arg (live arg (List.mem_cons_self ..))
    rw [Ty.rep_word] at rep
    subst rep
    have head := hold 0 (by simp)
    simp only [slotIndex, Nat.add_zero, List.getD_cons_zero, List.getElem_cons_zero] at head
    obtain ⟨held, below⟩ := sys_args_held vars args fun other member =>
      live other (List.mem_cons_of_mem _ member)
    refine ⟨.cons head held, fun place member => ?_⟩
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with rfl | member
    · simp only [Ty.width, Elem.width_word] at bound
      omega
    · exact below place member


theorem flat_run_bind (call : LeanExe.Wasi.Call) (words : Nat) (bytes : Bool)
    (values : List UInt64) :
    (SysForm.flat words bytes).run call values =
      Action.bind (.sys call (flatArgs call.params values) Action.pure) fun reply =>
        .pure (SysForm.value (.flat words bytes) (reply.errno :: resultWords call.params reply 0)
          (resultBytes call.params reply 0)) := rfl

/-- The code of a flat `sys` command gives a `SysResult`. -/
theorem wp_sys_flat_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {budget : Nat} {operation : LeanExe.Wasi.Call} {args : List (Var context .word)}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf operation]? = some operation)
    (hKinds : operation.params.all Param.flatKind = true)
    (hOutputs : operation.params.count .output ≤ 1)
    (hResults : operation.params.countP Param.isResult ≤ 2)
    (hCount : args.length = operation.argCount)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (used : ∀ arg ∈ args, liveIn arg.index = true)
    (at_ : heap.At (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base) (room : base + 6 ≤ locals.positions)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        ((SysForm.flat (operation.params.countP Param.isResult)
          (operation.params.contains .output)).run operation (args.map env.get))
        initial.host trace residual final →
        sysCost (.flat (operation.params.countP Param.isResult)
          (operation.params.contains .output)) operation (args.map env.get) trace ≤ budget) :
    wp target (sysFlatCodeWith calls operation
        (args.map fun arg => (slots.getD arg.index default).loc) base)
      (SysResult host env slots liveIn live base
        (.flat (operation.params.countP Param.isResult) (operation.params.contains .output))
        ((SysForm.flat (operation.params.countP Param.isResult)
          (operation.params.contains .output)).run operation (args.map env.get))
        (sysCost (.flat (operation.params.countP Param.isResult)
          (operation.params.contains .output)) operation (args.map env.get))
        heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨held, below⟩ := sys_args_held vars args used
  rw [← List.append_nil (sysFlatCodeWith calls operation _ base)]
  refine wp_sys_flat_with (aborts := aborts) runtime layout profile hImports sourceHost hHost hCall hKinds hOutputs
    hResults held (by simpa using hCount) (fun place member => Or.inl (below place member)) at_
    cap low room ?_ ?_ ?_ ?_
  · intro hAbort capacity found small nonzero
    obtain ⟨within, bound⟩ := resources hAbort
    have hCost := bound [] _ _ (Prefix.refl _ initial.host)
    simp only [sysCost, found, readCost_positive small nonzero] at hCost
    exact (within.mono hCost).room cap
  · intro hAbort final sameWorld
    exact .trapped final _ (CommandResult.resource_refl hAbort sameWorld)
  · intro heap' final finalLocals root length trace reply execution step rep top outside
    rw [wp_nil]
    have hLength := resultWords_length reply operation.params 0
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value (.flat (operation.params.countP Param.isResult)
        (operation.params.contains .output)) (reply.errno :: resultWords operation.params reply 0)
        (resultBytes operation.params reply 0))) (Exec.pure final.host _)
    rw [List.append_nil, ← flat_run_bind] at exec
    have frame := outside.frame room
    rcases outputLocal_spec operation.params _ _ hKinds held (by simpa [Call.argCount] using hCount) with
      ⟨none', capacity, contains⟩ | ⟨place, capacity, some', found, get, member, contains⟩
    · rw [none'] at *
      have hStep : Step heap (PureTransport.erase initial)
          (fun region => regionsDisjoint region ABI.scratch) heap' (PureTransport.erase final)
          [] := step.mono (fun _ kept => kept) (fun _ member => nomatch member)
      refine .returned _ heap' final finalLocals
        ((reply.errno :: resultWords operation.params reply 0).map Value.i64 ++
          pushedBytes none root length) trace exec ?_ top
      rw [contains]
      refine sys_after vars apart selected hStep frame ?_ rfl
      simp only [pushedBytes, List.append_nil, SysForm.ty, Ty.Rep]
      exact (wordsElem_values _ _ (by simp [hLength])).symm
    · rw [some'] at *
      refine .returned _ heap' final finalLocals
        ((reply.errno :: resultWords operation.params reply 0).map Value.i64 ++
          pushedBytes (some place) root length) trace exec ?_ top
      rw [contains]
      exact sys_after vars apart selected step frame
        (wordsBytes_rep rep _ _ (by simp [hLength]))
        (wordsBytes_blocks _ root length _ _ _ (by simp [hLength]))
  · intro final message trace execution
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value (.flat (operation.params.countP Param.isResult)
        (operation.params.contains .output)) (reply.errno :: resultWords operation.params reply 0)
        (resultBytes operation.params reply 0))) ⟨rfl, rfl, rfl⟩
    rw [List.append_nil, ← flat_run_bind] at exec
    exact .trapped final message (.terminal final trace (.trapped message) message exec rfl)


/-- The code of a reported `sys` command gives a `SysResult`. -/
theorem wp_sys_reported_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {budget : Nat} {operation : LeanExe.Wasi.Call} {values : List UInt64}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf operation]? = some operation)
    (hReporter : calls[calls.idxOf operation.reporterCall]? = some operation.reporterCall)
    (hParams : operation.params = [.reported 4 4 false, .reported 1 1 true])
    (hName : operation.reporter = some operation.reporterCall.name)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (at_ : heap.At (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base) (room : base + 6 ≤ locals.positions)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host) (SysForm.reported.run operation values)
        initial.host trace residual final → sysCost .reported operation values trace ≤ budget) :
    wp target (sysReportedCodeWith calls operation base)
      (SysResult host env slots liveIn live base .reported
        (SysForm.reported.run operation values) (sysCost .reported operation values)
        heap initial locals aborts)
      initial locals targetHost := by
  rw [← List.append_nil (sysReportedCodeWith calls operation base)]
  have hFits : operation.reporterCall.reject [] = 0 := rfl
  refine wp_sys_reported_with (aborts := aborts) (values := values) runtime layout profile
    hImports sourceHost hHost hCall hReporter hParams hName at_ cap low room ?_ ?_ ?_ ?_
  · intro hAbort after outputs hSys block hBlock
    obtain ⟨within, bound⟩ := resources hAbort
    have hCost := bound _ _ _ (Prefix.sys_return hFits hSys)
    simp only [sysCost, hBlock] at hCost
    exact within.mono hCost
  · intro hAbort after outputs hSys final hWorld
    exact .trapped final _ (.resource final _ _ hAbort (by
      rw [hWorld]; exact Prefix.sys_return hFits hSys))
  · intro heap' final finalLocals errno count size root length output trace execution step rep top
      outside
    rw [wp_nil]
    exact .returned (wordsBytesValue 3 [errno, count, size] output) heap' final finalLocals
      ([errno, count, size].map Value.i64 ++ [Value.i64 root, Value.i64 length]) trace execution
      (sys_after vars apart selected step (outside.frame room)
        (by exact wordsBytes_rep rep 3 [errno, count, size] rfl)
        (by exact wordsBytes_blocks _ root length _ 3 [errno, count, size] rfl)) top
  · intro final message trace execution
    exact .trapped final message (.terminal final trace (.trapped message) message execution rfl)

/-- A call's arguments are its word arguments and its inputs. -/
theorem _root_.LeanExe.Wasi.Call.argCount_eq (call : LeanExe.Wasi.Call) :
    call.argCount = call.wordCount + call.inputCount := by
  unfold LeanExe.Wasi.Call.argCount LeanExe.Wasi.Call.wordCount LeanExe.Wasi.Call.inputCount
  induction call.params with
  | nil => rfl
  | cons param params ih =>
    cases param <;>
      simp only [List.countP_cons, List.count_cons, Param.takesWord, Param.takesArg, ih,
        beq_iff_eq, reduceCtorEq, ite_true, ite_false, Bool.false_eq_true] <;> omega

/-- The input variables of a `sys` command hold each input's root and length in their two locals
below `base`, and represent it with blocks apart from the scratch area. -/
theorem sys_inputs_held {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    (vars : Holds env slots liveIn base heap store locals)
    (apart : Holds.ApartFrom env slots liveIn store locals ABI.scratch) :
    ∀ (inputs : List (Var context .bytes)), (∀ input ∈ inputs, liveIn input.index = true) →
    ∃ items : List (UInt64 × LeanExe.Bytes), items.map Prod.snd = inputs.map env.get ∧
      List.Forall₂ (InputHeld locals)
        (inputs.map fun input => (slots.getD input.index default).loc) items ∧
      (∀ item ∈ items, ∃ length, Bytes.Rep heap store item.1 length item.2 ∧
        ∀ r ∈ Bytes.regions store item.1, regionsDisjoint r ABI.scratch) ∧
      ∀ place ∈ inputs.map (fun input => (slots.getD input.index default).loc), place + 2 ≤ base
  | [], _ => ⟨[], rfl, .nil, nofun, nofun⟩
  | input :: inputs, live => by
    have hLive := live input (List.mem_cons_self ..)
    obtain ⟨bound, words, hold, rep⟩ := vars.1 .bytes input hLive
    obtain ⟨root, length, rfl, bytesRep⟩ := rep
    have hRoot := hold 0 (by simp)
    have hLength := hold 1 (by simp)
    simp only [Ty.types, slotIndex, Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ,
      List.getElem_cons_zero, List.getElem_cons_succ] at hRoot hLength
    obtain ⟨items, itemsEq, held, reps, below⟩ := sys_inputs_held vars apart inputs
      fun other member => live other (List.mem_cons_of_mem _ member)
    refine ⟨(root, env.get input) :: items, by simp [itemsEq],
      .cons ⟨hRoot, by rw [bytesRep.size_eq]; exact hLength, bytesRep.size_lt⟩ held, ?_, ?_⟩
    · intro item member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨length, bytesRep, fun r hr => ?_⟩
        have hRegion : r ∈ Ty.regions (slots.getD input.index default).mode store .bytes
            [.i64 root, .i64 length] (env.get input) := by
          cases (slots.getD input.index default).mode <;>
            simpa [Ty.regions, Ty.blocks, Ty.reads, Bytes.roots_regions] using hr
        exact regionsDisjoint_symm (apart .bytes input hLive _ hold rfl r hRegion)
      · exact reps item member
    · intro place member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · simp only [Ty.width] at bound
        omega
      · exact below place member

theorem flat_run_bind_inputs (call : LeanExe.Wasi.Call) (words : Nat) (bytes : Bool)
    (values : List UInt64) (inputs : List LeanExe.Bytes) :
    (SysForm.flat words bytes).runWith call values inputs =
      Action.bind (.sys call (flatArgsWith call.params values inputs) Action.pure) fun reply =>
        .pure (SysForm.value (.flat words bytes) (reply.errno :: resultWords call.params reply 0)
          (resultBytes call.params reply 0)) := rfl

/-- The code of a flat `sys` command with inputs gives a `SysResult`. -/
theorem wp_sys_flat_result_inputs_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {budget : Nat} {operation : LeanExe.Wasi.Call} {args : List (Var context .word)}
    {inputs : List (Var context .bytes)}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf operation]? = some operation)
    (hKinds : operation.params.all Param.inputKind = true)
    (hOutputs : operation.params.count .output ≤ 1)
    (hResults : operation.params.countP Param.isResult ≤ 2)
    (hCount : args.length = operation.wordCount)
    (hInputCount : inputs.length = operation.inputCount)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (used : ∀ arg ∈ args, liveIn arg.index = true)
    (usedInputs : ∀ input ∈ inputs, liveIn input.index = true)
    (at_ : heap.At (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base) (room : base + 6 ≤ locals.positions)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        ((SysForm.flat (operation.params.countP Param.isResult)
          (operation.params.contains .output)).runWith operation (args.map env.get)
          (inputs.map env.get))
        initial.host trace residual final →
        sysCostWith (.flat (operation.params.countP Param.isResult)
          (operation.params.contains .output)) operation (args.map env.get) (inputs.map env.get)
          trace ≤ budget) :
    wp target (sysFlatInputsCodeWith calls operation
        (args.map fun arg => (slots.getD arg.index default).loc)
        (inputs.map fun input => (slots.getD input.index default).loc) base)
      (SysResult host env slots liveIn live base
        (.flat (operation.params.countP Param.isResult) (operation.params.contains .output))
        ((SysForm.flat (operation.params.countP Param.isResult)
          (operation.params.contains .output)).runWith operation (args.map env.get)
          (inputs.map env.get))
        (sysCostWith (.flat (operation.params.countP Param.isResult)
          (operation.params.contains .output)) operation (args.map env.get) (inputs.map env.get))
        heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨held, below⟩ := sys_args_held vars args used
  obtain ⟨items, itemsEq, heldItems, reps, belowInputs⟩ := sys_inputs_held vars apart inputs
    usedInputs
  rw [← itemsEq]
  have hItemCount : items.length = operation.inputCount := by
    rw [← hInputCount, ← List.length_map (f := Prod.snd), itemsEq, List.length_map]
  rw [← List.append_nil (sysFlatInputsCodeWith calls operation _ _ base)]
  refine wp_sys_flat_inputs_with (aborts := aborts) runtime layout profile hImports sourceHost
    hHost hCall hKinds hOutputs hResults held (by simpa using hCount)
    (fun place member => Or.inl (below place member)) heldItems hItemCount
    (fun place member => Or.inl (belowInputs place member)) reps at_ cap low room ?_ ?_ ?_ ?_
  · intro hAbort capacity found small nonzero
    obtain ⟨within, bound⟩ := resources hAbort
    have hCost := bound [] _ _ (Prefix.refl _ initial.host)
    rw [← itemsEq] at hCost
    simp only [sysCostWith, found, readCost_positive small nonzero] at hCost
    exact (within.mono hCost).room cap
  · intro hAbort final sameWorld
    exact .trapped final _ (CommandResult.resource_refl hAbort sameWorld)
  · intro heap' final finalLocals root length trace reply execution step rep top outside
    rw [wp_nil]
    have hLength := resultWords_length reply operation.params 0
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value (.flat (operation.params.countP Param.isResult)
        (operation.params.contains .output)) (reply.errno :: resultWords operation.params reply 0)
        (resultBytes operation.params reply 0))) (Exec.pure final.host _)
    rw [List.append_nil, ← flat_run_bind_inputs] at exec
    have frame := outside.frame room
    rcases outputLocalInputs_spec operation.params _ _
        (inputs.map fun input => (slots.getD input.index default).loc) (items.map Prod.snd)
        hKinds held (by simpa [LeanExe.Wasi.Call.wordCount] using hCount)
        (heldItems.length_eq.trans hItemCount)
        (by simpa [LeanExe.Wasi.Call.inputCount] using hItemCount) with
      ⟨none', capacity, contains⟩ | ⟨place, capacity, some', found, get, member, contains⟩
    · rw [none'] at *
      have hStep : Step heap (PureTransport.erase initial)
          (fun region => regionsDisjoint region ABI.scratch) heap' (PureTransport.erase final)
          [] := step.mono (fun _ kept => kept) (fun _ member => nomatch member)
      refine .returned _ heap' final finalLocals
        ((reply.errno :: resultWords operation.params reply 0).map Value.i64 ++
          pushedBytes none root length) trace exec ?_ top
      rw [contains]
      refine sys_after vars apart selected hStep frame ?_ rfl
      simp only [pushedBytes, List.append_nil, SysForm.ty, Ty.Rep]
      exact (wordsElem_values _ _ (by simp [hLength])).symm
    · rw [some'] at *
      refine .returned _ heap' final finalLocals
        ((reply.errno :: resultWords operation.params reply 0).map Value.i64 ++
          pushedBytes (some place) root length) trace exec ?_ top
      rw [contains]
      exact sys_after vars apart selected step frame
        (wordsBytes_rep rep _ _ (by simp [hLength]))
        (wordsBytes_blocks _ root length _ _ _ (by simp [hLength]))
  · intro final message trace execution
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value (.flat (operation.params.countP Param.isResult)
        (operation.params.contains .output)) (reply.errno :: resultWords operation.params reply 0)
        (resultBytes operation.params reply 0))) ⟨rfl, rfl, rfl⟩
    rw [List.append_nil, ← flat_run_bind_inputs] at exec
    exact .trapped final message (.terminal final trace (.trapped message) message exec rfl)

/-- What readiness gives about a `sys` command. -/
theorem sys_ready_facts {calls : List LeanExe.Wasi.Call} {operation : LeanExe.Wasi.Call}
    {form : SysForm} {args : List (Var context .word)} {inputs : List (Var context .bytes)}
    (ready : (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs).callsReady calls = true) :
    operation.compiled = true ∧ operation.form = form ∧
      args.length + inputs.length = operation.argCount ∧
      inputs.length = operation.inputCount ∧
      ∀ use ∈ operation.uses, calls[calls.idxOf use]? = some use := by
  simp only [Command.callsReady, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at ready
  obtain ⟨⟨⟨⟨compiled, form'⟩, count⟩, inputCount⟩, uses⟩ := ready
  refine ⟨compiled, form', count, inputCount, fun use member => ?_⟩
  have hMember := uses use member
  exact List.getElem?_eq_some_iff.mpr ⟨List.idxOf_lt_length_of_mem hMember,
    List.getElem_idxOf (List.idxOf_lt_length_of_mem hMember)⟩

/-- The code of a `sys` command gives a `SysResult`, with its input variables live after it. -/
theorem wp_sys_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {budget : Nat} {operation : LeanExe.Wasi.Call} {form : SysForm}
    {args : List (Var context .word)} {inputs : List (Var context .bytes)}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (ready : (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs).callsReady calls = true)
    (vars : Holds env slots (fun i => live i || ((inputs.any fun input => i == input.index) ||
      args.any fun arg => i == arg.index)) base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots (fun i => live i ||
      ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index))
      (PureTransport.erase initial) locals ABI.scratch)
    (at_ : heap.At (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base) (room : base + 6 ≤ locals.positions)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        (form.runWith operation (args.map env.get) (inputs.map env.get))
        initial.host trace residual final →
        sysCostWith form operation (args.map env.get) (inputs.map env.get) trace ≤ budget) :
    wp target (sysInputsCodeWith calls operation form
        (args.map fun arg => (slots.getD arg.index default).loc)
        (inputs.map fun input => (slots.getD input.index default).loc) base)
      (SysResult host env slots (fun i => live i || ((inputs.any fun input => i == input.index) ||
          args.any fun arg => i == arg.index))
        (fun i => (inputs.any fun input => i == input.index) || live i)
        base form (form.runWith operation (args.map env.get) (inputs.map env.get))
        (sysCostWith form operation (args.map env.get) (inputs.map env.get)) heap initial locals
        aborts)
      initial locals targetHost := by
  obtain ⟨compiled, formEq, count, inputCount, uses⟩ := sys_ready_facts ready
  have selected : ∀ i, ((inputs.any fun input => i == input.index) || live i) = true →
      (live i || ((inputs.any fun input => i == input.index) ||
        args.any fun arg => i == arg.index)) = true := by
    intro i h
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with h | h <;> simp [h]
  have used : ∀ arg ∈ args, (live arg.index ||
      ((inputs.any fun input => arg.index == input.index) ||
        args.any fun other => arg.index == other.index)) = true := by
    intro arg member
    have hAny : (args.any fun other => arg.index == other.index) = true :=
      List.any_eq_true.mpr ⟨arg, member, by simp⟩
    simp [hAny]
  have usedInputs : ∀ input ∈ inputs, (live input.index ||
      ((inputs.any fun other => input.index == other.index) ||
        args.any fun arg => input.index == arg.index)) = true := by
    intro input member
    have hAny : (inputs.any fun other => input.index == other.index) = true :=
      List.any_eq_true.mpr ⟨input, member, by simp⟩
    simp [hAny]
  cases hReporter : operation.reporter with
  | none =>
    have hForm : form = .flat (operation.params.countP Param.isResult)
        (operation.params.contains .output) := by
      rw [← formEq, LeanExe.Wasi.Call.form, hReporter]
    subst hForm
    simp only [LeanExe.Wasi.Call.compiled, hReporter, Bool.and_eq_true,
      decide_eq_true_eq] at compiled
    have hCount : args.length = operation.wordCount := by
      have := operation.argCount_eq
      omega
    exact wp_sys_flat_result_inputs_with runtime layout profile hImports sourceHost hHost
      (uses operation (by simp [LeanExe.Wasi.Call.uses, hReporter])) compiled.1.1 compiled.1.2
      compiled.2 hCount inputCount vars apart selected used usedInputs at_ cap low room resources
  | some name =>
    have hForm : form = .reported := by
      rw [← formEq, LeanExe.Wasi.Call.form, hReporter]
    subst hForm
    simp only [LeanExe.Wasi.Call.compiled, hReporter, beq_iff_eq] at compiled
    have hNoInputs : inputs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [inputCount]
      simp [LeanExe.Wasi.Call.inputCount, compiled]
    subst hNoInputs
    exact wp_sys_reported_result_with (values := args.map env.get) runtime layout profile
      hImports sourceHost hHost
      (uses operation (by simp [LeanExe.Wasi.Call.uses, hReporter]))
      (uses operation.reporterCall (by simp [LeanExe.Wasi.Call.uses, hReporter])) compiled
      (by simp [LeanExe.Wasi.Call.reporterCall, hReporter]) vars apart selected at_ cap low room
      resources

/-- A trap's classification does not depend on the variables live after the command. -/
theorem CommandResult.trap_live {World : Type} {context : List Ty} {host : Host World}
    {env : Env context} {slots : List Slot} {liveIn live live' : Nat → Bool} {base : Nat}
    {result : ResultTy} {action : Action result.denote} {heap : Heap}
    {initial final : Store (Observed World)} {locals : Locals} {aborts : Bool} {message : String}
    (h : CommandResult host env slots liveIn live base result action heap initial locals aborts
      (.Trap final message)) :
    CommandResult host env slots liveIn live' base result action heap initial locals aborts
      (.Trap final message) :=
  match h with
  | .terminal _ trace outcome _ execution ending => .terminal _ trace outcome _ execution ending
  | .resource _ trace residual allowed progress => .resource _ trace residual allowed progress

theorem command_sys_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    (operation : LeanExe.Wasi.Call) (form : SysForm) (args : List (Var context .word))
    (inputs : List (Var context .bytes)) :
    CommandCodeSpecWith calls source target pure effects pool
      (.sys operation form args inputs) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid _ _ positions vars at_ _ scratch cap low room ready _ _
  have room' : base + 6 ≤ locals.positions := by
    rw [positions]; simpa [Command.width] using room
  have fragment := ready.1 _ (List.mem_singleton_self _)
  have keptSelected : ∀ i, ((inputs.any fun input => i == input.index) || live i) = true →
      (live i || ((inputs.any fun input => i == input.index) ||
        args.any fun arg => i == arg.index)) = true := by
    intro i hi
    simp only [Bool.or_eq_true] at hi ⊢
    rcases hi with h | h <;> simp [h]
  have liveSelected : ∀ i, live i = true →
      ((inputs.any fun input => i == input.index) || live i) = true := by
    intro i hi
    simp [hi]
  have releaseSelected : ∀ i, ((inputs.any fun input => i == input.index) && !live i) = true →
      ((inputs.any fun input => i == input.index) || live i) = true := by
    intro i hi
    simp only [Bool.and_eq_true] at hi
    simp [hi.1]
  have retained : ∀ i, live i = true →
      (((inputs.any fun input => i == input.index) || live i) &&
        !((inputs.any fun input => i == input.index) && !live i)) = true := by
    intro i hi
    simp [hi]
  change wp target (sysInputsCodeWith calls operation form
      (args.map fun arg => (slots.getD arg.index default).loc)
      (inputs.map fun input => (slots.getD input.index default).loc) base ++
    Relocation.programWith calls (releaseWhere context slots
      (fun i => (inputs.any fun input => i == input.index) && !live i))) _ initial locals
    targetHost
  apply wp_append
  refine wp.conseq (fun continuation result => ?_)
    (wp_sys_result_with (aborts := true) (budget := 0) facts.runtime facts.layout facts.profile
      facts.imports sourceHost valid ready.2 vars scratch at_ cap low room'
      (fun impossible => Bool.noConfusion impossible))
  cases result with
  | returned value finalHeap final finalLocals words trace execution after top =>
    have updated : After env slots _ _ base heap initial locals (.value form.ty) value finalHeap
        final { finalLocals with values := words.reverse ++ locals.values } words :=
      ⟨after.step, after.frame.trans Frame.ofValues, after.holds, after.rep, after.apart⟩
    simp only [Then]
    rw [← List.append_nil (Relocation.programWith calls (releaseWhere context slots
      (fun i => (inputs.any fun input => i == input.index) && !live i)))]
    refine wp_release_context_with (sourceHost := sourceHost) (rest := []) facts.runtime
      facts.layout facts.profile fragment.1 fragment.2 updated.holds updated.step.at_
      releaseSelected ?_
    intro releasedHeap released evolution _ releasedWorld
    have resultAfter := After.release vars scratch updated keptSelected liveSelected
      (evolution.mono retained)
    rw [wp_nil]
    apply CommandResult.returned (result := .value form.ty) value releasedHeap released
      { finalLocals with values := words.reverse ++ locals.values } words trace
    · rw [releasedWorld]
      exact execution
    · exact resultAfter
  | trapped final message result =>
    simp only [Then]
    exact CommandResult.trap_live result

theorem cost_command_sys_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure (program.funs pure.funs) pool)
    (sourceHost : HostEnv Unit)
    (operation : LeanExe.Wasi.Call) (form : SysForm) (args : List (Var context .word))
    (inputs : List (Var context .bytes)) :
    CostCommandCodeSpecWith calls source target pure program pool
      (.sys operation form args inputs) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid _ _ positions vars at_ _ scratch cap low room ready _ _ resources
  have room' : base + 6 ≤ locals.positions := by
    rw [positions]; simpa [Command.width] using room
  have fragment := ready.1 _ (List.mem_singleton_self _)
  have keptSelected : ∀ i, ((inputs.any fun input => i == input.index) || live i) = true →
      (live i || ((inputs.any fun input => i == input.index) ||
        args.any fun arg => i == arg.index)) = true := by
    intro i hi
    simp only [Bool.or_eq_true] at hi ⊢
    rcases hi with h | h <;> simp [h]
  have liveSelected : ∀ i, live i = true →
      ((inputs.any fun input => i == input.index) || live i) = true := by
    intro i hi
    simp [hi]
  have releaseSelected : ∀ i, ((inputs.any fun input => i == input.index) && !live i) = true →
      ((inputs.any fun input => i == input.index) || live i) = true := by
    intro i hi
    simp only [Bool.and_eq_true] at hi
    simp [hi.1]
  have retained : ∀ i, live i = true →
      (((inputs.any fun input => i == input.index) || live i) &&
        !((inputs.any fun input => i == input.index) && !live i)) = true := by
    intro i hi
    simp [hi]
  change wp target (sysInputsCodeWith calls operation form
      (args.map fun arg => (slots.getD arg.index default).loc)
      (inputs.map fun input => (slots.getD input.index default).loc) base ++
    Relocation.programWith calls (releaseWhere context slots
      (fun i => (inputs.any fun input => i == input.index) && !live i))) _ initial locals
    targetHost
  apply wp_append
  refine wp.conseq (fun continuation result => ?_)
    (wp_sys_result_with (aborts := aborts) (budget := budget) facts.runtime facts.layout
      facts.profile facts.imports sourceHost valid ready.2 vars scratch at_ cap low room'
      (fun hAbort => ⟨(resources hAbort).1, fun trace residual final progress =>
        (resources hAbort).2.sys progress⟩))
  cases result with
  | returned value finalHeap final finalLocals words trace execution after top =>
    have updated : After env slots _ _ base heap initial locals (.value form.ty) value finalHeap
        final { finalLocals with values := words.reverse ++ locals.values } words :=
      ⟨after.step, after.frame.trans Frame.ofValues, after.holds, after.rep, after.apart⟩
    simp only [Then]
    rw [← List.append_nil (Relocation.programWith calls (releaseWhere context slots
      (fun i => (inputs.any fun input => i == input.index) && !live i)))]
    refine wp_release_context_with (sourceHost := sourceHost) (rest := []) facts.runtime
      facts.layout facts.profile fragment.1 fragment.2 updated.holds updated.step.at_
      releaseSelected ?_
    intro releasedHeap released evolution topEq releasedWorld
    have resultAfter := After.release vars scratch updated keptSelected liveSelected
      (evolution.mono retained)
    rw [wp_nil]
    exact CostCommandResult.returned (command := .sys operation form args inputs) value
      releasedHeap released { finalLocals with values := words.reverse ++ locals.values } words
      trace _ true (.sys (by rw [releasedWorld]; exact execution)) resultAfter
      (fun _ => by rw [topEq]; exact top)
  | trapped final message result =>
    simp only [Then]
    exact CostCommandResult.trapped final message (CommandResult.trap_live result)

end Verified.Wasi
