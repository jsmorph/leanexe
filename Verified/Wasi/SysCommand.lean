import Verified.Wasi.SysFlat
import Verified.Wasi.SysRecord
import Verified.Wasi.SysIovec
import Verified.Wasi.SysPoll
import Verified.Wasi.SysReported
import Verified.Wasi.SysResult
import Verified.Wasi.CostCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.CostResults
import Verified.Wasi.ResourcePrefix
import Verified.Wasi.ResultRelease
import Verified.Wasi.WriteCommand
import Verified.Wasi.BindContext

/-! The command `sys`: its code from the argument variables to the result words, with its
correctness and its cost.  `ValueResult` is the outcome that both specifications need of a `sys`
command or a read: a returned value with the state after the command and the heap that the command
allocated, or a trap that `CommandResult` accepts.  `wp_take_with` composes the take of a buffer,
which both commands make, with the code that consumes the taken buffer. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

inductive ValueResult {World : Type} {context : List Ty} (host : Host World) (env : Env context)
    (slots : List Slot) (liveIn live : Nat → Bool) (base : Nat) (type : Ty)
    (action : Action type.denote) (cost : List Event → Nat) (heap : Heap)
    (initial : Store (Observed World)) (locals : Locals) (aborts : Bool) :
    Continuation (Observed World) → Prop where
  | returned (value : type.denote) (finalHeap : Heap) (final : Store (Observed World))
      (finalLocals : Locals) (words : List Value) (trace : List Event)
      (execution : Exec (observedHost host) action initial.host trace (.returned value) final.host)
      (after : After env slots liveIn live base heap initial locals (.value type) value
        finalHeap final finalLocals words)
      (top : finalHeap.top.toNat ≤ heap.top.toNat + cost trace) :
      ValueResult host env slots liveIn live base type action cost heap initial locals aborts
        (.Fallthrough final { finalLocals with values := words.reverse ++ locals.values })
  | trapped (final : Store (Observed World)) (message : String)
      (result : CommandResult host env slots liveIn live base (.value type) action heap initial
        locals aborts (.Trap final message)) :
      ValueResult host env slots liveIn live base type action cost heap initial locals aborts
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

/-! ## Arguments of calls without windows -/

theorem argWords_plain : ∀ {params : List Param}, params.all (fun param => !param.isWindow) = true →
    (params.map Param.argWords).sum = (params.map Param.wordCount).sum
  | [], _ => rfl
  | param :: params, plain => by
    simp only [List.all_cons, Bool.and_eq_true] at plain
    simp only [List.map_cons, List.sum_cons, argWords_plain plain.2]
    cases param <;> simp_all [Param.isWindow, Param.argWords, Param.wordCount, Param.takesBytes]

theorem lowerInputs_plain : ∀ (params : List Param) (values : List UInt64)
    (inputs : List LeanExe.Bytes), params.all (fun param => !param.isWindow) = true →
    inputs.length = params.count .input → lowerInputs params values inputs = inputs
  | [], _, inputs, _, count => by
    simp only [List.count_nil, List.length_eq_zero_iff] at count
    subst count
    rfl
  | param :: params, values, inputs, plain, count => by
    simp only [List.all_cons, Bool.and_eq_true] at plain
    cases param with
    | output | iovec => simp [Param.isWindow] at plain
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        simp only [lowerInputs, List.headD_cons, List.tail_cons]
        rw [lowerInputs_plain params values inputs plain.2
          (by simpa [List.count_cons] using count)]
    | word32 | handle | word64 | enum32 | flags32 | flags64 | result32 | result64 | reported
    | record | subscriptions =>
      simp only [lowerInputs]
      exact lowerInputs_plain params _ inputs plain.2 (by simpa [List.count_cons] using count)

/-- The arguments of a call without windows are those of its words and inputs. -/
theorem sysArgs_plain {params : List Param} {values : List UInt64}
    {inputs buffers : List LeanExe.Bytes}
    (plain : params.all (fun param => !param.isWindow) = true)
    (count : values.length = (params.map Param.argWords).sum)
    (inputCount : inputs.length = params.count .input) :
    sysArgs params values inputs buffers = flatArgsWith params values inputs := by
  rw [sysArgs, lowerWords_plain params values buffers plain count,
    lowerInputs_plain params values inputs plain inputCount]

theorem plain_of_inputKind {params : List Param} (kinds : params.all Param.inputKind = true)
    (none : params.count .output = 0) : params.all (fun param => !param.isWindow) = true := by
  rw [List.all_eq_true]
  intro param member
  have := List.all_eq_true.mp kinds param member
  cases param <;> simp_all [Param.isWindow, Param.inputKind, Param.flatKind, List.count_eq_zero]

/-- The code of a reported `sys` command gives a `ValueResult`. -/
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
      ∀ trace residual final, Prefix (observedHost host)
        (SysForm.reported.runWith operation values [] []) initial.host trace residual final →
        sysCost .reported operation trace ≤ budget) :
    wp target (sysReportedCodeWith calls operation base)
      (ValueResult host env slots liveIn live base SysForm.reported.ty
        (SysForm.reported.runWith operation values [] []) (sysCost .reported operation)
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

/-- The input variables of a `sys` command hold each input's root and length in their two locals
below `base`, and represent it with blocks apart from the scratch area and from the regions
`away`, from which the regions of each input variable lie apart. -/
theorem sys_inputs_held {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    (vars : Holds env slots liveIn base heap store locals)
    (apart : Holds.ApartFrom env slots liveIn store locals ABI.scratch)
    (away : List (Nat × Nat)) :
    ∀ (inputs : List (Var context .bytes)), (∀ input ∈ inputs, liveIn input.index = true) →
    (∀ input ∈ inputs, ∀ words,
      LocalsHold locals (slots.getD input.index default).loc Ty.bytes.types words →
      words.length = Ty.bytes.width →
      ∀ c ∈ Ty.regions (slots.getD input.index default).mode store .bytes words (env.get input),
        ∀ b ∈ away, regionsDisjoint c b) →
    ∃ items : List (UInt64 × LeanExe.Bytes), items.map Prod.snd = inputs.map env.get ∧
      List.Forall₂ (InputHeld locals)
        (inputs.map fun input => (slots.getD input.index default).loc) items ∧
      (∀ item ∈ items, ∃ length, Bytes.Rep heap store item.1 length item.2 ∧
        ∀ r ∈ Bytes.regions store item.1,
          regionsDisjoint r ABI.scratch ∧ ∀ b ∈ away, regionsDisjoint r b) ∧
      ∀ place ∈ inputs.map (fun input => (slots.getD input.index default).loc), place + 2 ≤ base
  | [], _, _ => ⟨[], rfl, .nil, nofun, nofun⟩
  | input :: inputs, live, hAway => by
    have hLive := live input (List.mem_cons_self ..)
    obtain ⟨bound, words, hold, rep⟩ := vars.1 .bytes input hLive
    obtain ⟨root, length, rfl, bytesRep⟩ := rep
    have hRoot := hold 0 (by simp)
    have hLength := hold 1 (by simp)
    simp only [Ty.types, slotIndex, Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ,
      List.getElem_cons_zero, List.getElem_cons_succ] at hRoot hLength
    obtain ⟨items, itemsEq, held, reps, below⟩ := sys_inputs_held vars apart away inputs
      (fun other member => live other (List.mem_cons_of_mem _ member))
      (fun other member => hAway other (List.mem_cons_of_mem _ member))
    refine ⟨(root, env.get input) :: items, by simp [itemsEq],
      .cons ⟨hRoot, by rw [bytesRep.size_eq]; exact hLength, bytesRep.size_lt⟩ held, ?_, ?_⟩
    · intro item member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨length, bytesRep, fun r hr => ?_⟩
        have hRegion : r ∈ Ty.regions (slots.getD input.index default).mode store .bytes
            [.i64 root, .i64 length] (env.get input) := by
          cases (slots.getD input.index default).mode <;>
            simpa [Ty.regions, Ty.blocks, Ty.reads, Bytes.roots_regions] using hr
        exact ⟨regionsDisjoint_symm (apart .bytes input hLive _ hold rfl r hRegion),
          hAway input (List.mem_cons_self ..) _ hold rfl r hRegion⟩
      · exact reps item member
    · intro place member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · simp only [Ty.width] at bound
        omega
      · exact below place member

/-- A live owned buffer variable holds its root and size in its two locals below `base`, and the
regions of every other live variable lie apart from its blocks. -/
theorem sys_buffer_held {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    (vars : Holds env slots liveIn base heap store locals) {buffer : Var context .bytes}
    (hLive : liveIn buffer.index = true)
    (hOwned : (slots.getD buffer.index default).mode = .owned) :
    ∃ root size,
      LocalsHold locals (slots.getD buffer.index default).loc Ty.bytes.types
        [.i64 root, .i64 size] ∧
      locals.get (slots.getD buffer.index default).loc = some (.i64 root) ∧
      locals.get ((slots.getD buffer.index default).loc + 1) = some (.i64 size) ∧
      Bytes.Rep heap store root size (env.get buffer) ∧
      (slots.getD buffer.index default).loc + 2 ≤ base ∧
      ∀ (input : Var context .bytes), liveIn input.index = true → input.index ≠ buffer.index →
        ∀ words, LocalsHold locals (slots.getD input.index default).loc Ty.bytes.types words →
          words.length = Ty.bytes.width → ∀ c ∈ Ty.regions (slots.getD input.index default).mode store .bytes words
            (env.get input), ∀ b ∈ Bytes.regions store root, regionsDisjoint c b := by
  obtain ⟨bound, words, hold, rep⟩ := vars.1 .bytes buffer hLive
  rw [hOwned] at rep
  obtain ⟨root, size, rfl, bytesRep⟩ := rep
  have hRoot := hold 0 (by simp)
  have hSize := hold 1 (by simp)
  simp only [Ty.types, slotIndex, Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ,
    List.getElem_cons_zero, List.getElem_cons_succ] at hRoot hSize
  refine ⟨root, size, hold, hRoot, hSize, bytesRep, by simp only [Ty.width] at bound; omega, ?_⟩
  intro input hInput distinct inputWords inputHeld inputLength c hc b hb
  have hBlocks : Ty.bytes.blocks store [.i64 root, .i64 size] (env.get buffer) =
      Bytes.regions store root := wordsBytes_blocks _ root size _ 0 [] rfl
  exact regionsDisjoint_symm (vars.2 .bytes .bytes buffer input hLive hInput distinct.symm hOwned
    [.i64 root, .i64 size] inputWords hold rfl inputHeld inputLength
    b (by rw [hBlocks]; exact hb) c hc)

theorem flat_run_bind_inputs (call : LeanExe.Wasi.Call) (words : Nat) (values : List UInt64)
    (inputs buffers : List LeanExe.Bytes) :
    (SysForm.flat words false).runWith call values inputs buffers =
      Action.bind (.sys call (sysArgs call.params values inputs buffers) Action.pure) fun reply =>
        .pure (SysForm.value (.flat words false) (reply.errno :: resultWords call.params reply 0)
          .empty) := rfl

/-- The code of a flat `sys` command without an output gives a `ValueResult`. -/
theorem wp_sys_flat_result_inputs_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {operation : LeanExe.Wasi.Call} {args : List (Var context .word)}
    {inputs : List (Var context .bytes)} {buffers : List LeanExe.Bytes}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf operation]? = some operation)
    (hKinds : operation.params.all Param.inputKind = true)
    (hOutputs : operation.params.count .output = 0)
    (hResults : operation.params.countP Param.isResult ≤ 2)
    (hCount : args.length = operation.argWords)
    (hInputCount : inputs.length = operation.inputCount)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (used : ∀ arg ∈ args, liveIn arg.index = true)
    (usedInputs : ∀ input ∈ inputs, liveIn input.index = true)
    (at_ : heap.At (PureTransport.erase initial))
    (low : locals.params.length ≤ base) (room : base + 6 ≤ locals.positions) :
    wp target (sysFlatInputsCodeWith calls operation
        (args.map fun arg => (slots.getD arg.index default).loc)
        (inputs.map fun input => (slots.getD input.index default).loc) base)
      (ValueResult host env slots liveIn live base
        (SysForm.flat (operation.params.countP Param.isResult) false).ty
        ((SysForm.flat (operation.params.countP Param.isResult) false).runWith operation
          (args.map env.get) (inputs.map env.get) buffers)
        (sysCost (.flat (operation.params.countP Param.isResult) false) operation)
        heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨held, below⟩ := sys_args_held vars args used
  obtain ⟨items, itemsEq, heldItems, reps, belowInputs⟩ := sys_inputs_held vars apart [] inputs
    usedInputs (fun _ _ _ _ _ _ _ b member => nomatch member)
  have plain := plain_of_inputKind hKinds hOutputs
  have hItemCount : items.length = operation.inputCount := by
    rw [← hInputCount, ← List.length_map (f := Prod.snd), itemsEq, List.length_map]
  have hArgs : sysArgs operation.params (args.map env.get) (inputs.map env.get) buffers =
      flatArgsWith operation.params (args.map env.get) (items.map Prod.snd) := by
    rw [← itemsEq]
    exact sysArgs_plain plain (by rw [List.length_map, hCount]; rfl)
      (by rw [List.length_map, hItemCount, Call.inputCount_of_inputKind hKinds])
  rw [← List.append_nil (sysFlatInputsCodeWith calls operation _ _ base)]
  refine wp_sys_flat_inputs_with hImports hHost hCall hKinds hOutputs hResults held
    (by rw [List.length_map, hCount]; exact argWords_plain plain)
    (fun place member => Or.inl (below place member)) heldItems hItemCount
    (fun place member => Or.inl (belowInputs place member))
    (fun item member => by
      obtain ⟨length, rep, apart⟩ := reps item member
      exact ⟨length, rep, fun r hr => (apart r hr).1⟩) at_ low room ?_ ?_
  · intro final finalLocals trace reply execution step outside
    rw [wp_nil]
    have hLength := resultWords_length reply operation.params 0
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value (.flat (operation.params.countP Param.isResult) false)
        (reply.errno :: resultWords operation.params reply 0) .empty)) (Exec.pure final.host _)
    rw [List.append_nil, ← hArgs, ← flat_run_bind_inputs] at exec
    refine .returned _ heap final finalLocals
      ((reply.errno :: resultWords operation.params reply 0).map Value.i64) trace exec ?_
      (by simp [sysCost])
    refine sys_after vars apart selected step (outside.frame room) ?_ rfl
    simp only [SysForm.ty, SysForm.value, Ty.Rep]
    exact (wordsElem_values _ _ (by simp [hLength])).symm
  · intro final message trace execution
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value (.flat (operation.params.countP Param.isResult) false)
        (reply.errno :: resultWords operation.params reply 0) .empty)) ⟨rfl, rfl, rfl⟩
    rw [List.append_nil, ← hArgs, ← flat_run_bind_inputs] at exec
    exact .trapped final message (.terminal final trace (.trapped message) message exec rfl)

theorem flat_fill_run_bind (call : LeanExe.Wasi.Call) (words : Nat) (values : List UInt64)
    (inputs buffers : List LeanExe.Bytes) :
    (SysForm.flat words true).runWith call values inputs buffers =
      Action.bind (.sys call (sysArgs call.params values inputs buffers) Action.pure) fun reply =>
        .pure (fillValue (flatFill call.params values (buffers.headD .empty) reply)) := rfl

theorem fillValue_rep {heap : Heap} {store : Store Unit} {root size : UInt64}
    {result : FillResult} (rep : Bytes.Rep heap store root size result.buffer) :
    (wordsBytesTy 2).Rep .owned heap store
      ([Value.i64 result.errno, .i64 result.count] ++ [.i64 root, .i64 size])
      (fillValue result) :=
  wordsBytes_rep rep 2 [result.errno, result.count] rfl

theorem fillValue_blocks (store : Store Unit) (root size : UInt64) (result : FillResult) :
    (wordsBytesTy 2).blocks store ([Value.i64 result.errno, .i64 result.count] ++
      [.i64 root, .i64 size]) (fillValue result) = Bytes.regions store root :=
  wordsBytes_blocks store root size result.buffer 2 [result.errno, result.count] rfl

/-- The code of a flat `sys` command that fills a window of its buffer gives a `ValueResult`. -/
theorem wp_sys_flat_fill_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {operation : LeanExe.Wasi.Call} {args : List (Var context .word)}
    {inputs : List (Var context .bytes)} {buffer : Var context .bytes}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf operation]? = some operation)
    (hKinds : operation.params.all Param.inputKind = true)
    (hOutput : operation.params.count .output = 1)
    (hResults : operation.params.countP Param.isResult ≤ 1)
    (hCount : args.length = operation.argWords)
    (hInputCount : inputs.length = operation.inputCount)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (used : ∀ arg ∈ args, liveIn arg.index = true)
    (usedInputs : ∀ input ∈ inputs, liveIn input.index = true)
    (hBufferIn : liveIn buffer.index = true) (hBufferOut : live buffer.index = false)
    (hOwned : (slots.getD buffer.index default).mode = .owned)
    (hDistinct : ∀ input ∈ inputs, input.index ≠ buffer.index)
    (at_ : heap.At (PureTransport.erase initial))
    (low : locals.params.length ≤ base) (room : base + 6 ≤ locals.positions) :
    wp target (sysFlatFillCodeWith calls operation
        (args.map fun arg => (slots.getD arg.index default).loc)
        (inputs.map fun input => (slots.getD input.index default).loc)
        (slots.getD buffer.index default).loc base)
      (ValueResult host env slots liveIn live base
        (SysForm.flat (operation.params.countP Param.isResult) true).ty
        ((SysForm.flat (operation.params.countP Param.isResult) true).runWith operation
          (args.map env.get) (inputs.map env.get) [env.get buffer])
        (sysCost (.flat (operation.params.countP Param.isResult) true) operation)
        heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨held, below⟩ := sys_args_held vars args used
  obtain ⟨root, size, bufferHeld, hRoot, hSize, hRep, bufferBelow, bufferApart⟩ :=
    sys_buffer_held vars hBufferIn hOwned
  obtain ⟨items, itemsEq, heldItems, reps, belowInputs⟩ :=
    sys_inputs_held vars apart (Bytes.regions (PureTransport.erase initial) root) inputs usedInputs
      (fun input member => bufferApart input (usedInputs input member) (hDistinct input member))
  have hItemCount : items.length = operation.inputCount := by
    rw [← hInputCount, ← List.length_map (f := Prod.snd), itemsEq, List.length_map]
  have hItemCount' : items.length = operation.params.count .input := by
    rw [hItemCount, Call.inputCount_of_inputKind hKinds]
  have hArgs : sysArgs operation.params (args.map env.get) (inputs.map env.get)
      [env.get buffer] = flatArgsWith operation.params
        (lowerWords operation.params (args.map env.get) [env.get buffer]) (items.map Prod.snd) := by
    rw [sysArgs, ← itemsEq, lowerInputs_flat operation.params _ _ hKinds
      (by rw [List.length_map]; exact hItemCount')]
  rw [← List.append_nil (sysFlatFillCodeWith calls operation _ _ _ base)]
  refine wp_sys_flat_fill_with hImports hHost hCall hKinds hOutput hResults held
    (by rw [List.length_map, hCount]) below heldItems hItemCount
    belowInputs (fun item member => by
      obtain ⟨length, rep, apart⟩ := reps item member
      exact ⟨length, rep, fun r hr => (apart r hr).1⟩)
    (fun item member b hb => by
      obtain ⟨length, rep, apart⟩ := reps item member
      rcases rep.buffer with ⟨hNull, hEmpty⟩ | hBuffer
      · simp only [LeanExe.Runtime.regionsDisjoint, hEmpty, Nat.add_zero, hNull,
          UInt64.toNat_zero]
        omega
      · have blockApart := (apart (block (PureTransport.erase initial) item.1)
          (by simp [Bytes.regions, hBuffer.nonzero])).2 b hb
        have hBase := hBuffer.object.base
        have hCap := hBuffer.capacity
        simp only [block, LeanExe.Runtime.regionsDisjoint] at blockApart ⊢
        omega)
    hRoot hSize bufferBelow hRep at_ low room ?_ ?_
  · intro final finalLocals trace reply execution step rep outside
    rw [wp_nil]
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (fillValue (flatFill operation.params (args.map env.get) (env.get buffer)
        reply))) (Exec.pure final.host _)
    rw [List.append_nil, ← hArgs] at exec
    have hErrno : (flatFill operation.params (args.map env.get) (env.get buffer) reply).errno =
        reply.errno := fillResult_errno _ _ _ _ _ _
    have after := fill_sys_after (type := wordsBytesTy 2) vars apart selected hBufferIn
      hBufferOut hOwned bufferHeld step (outside.frame room) (fillValue_rep rep)
      (fillValue_blocks _ root size _)
    rw [hErrno] at after
    have exec' : Exec (observedHost host)
        ((SysForm.flat (operation.params.countP Param.isResult) true).runWith operation
          (args.map env.get) (inputs.map env.get) [env.get buffer]) initial.host trace
        (.returned (fillValue (flatFill operation.params (args.map env.get) (env.get buffer)
          reply))) final.host := exec
    exact .returned _ heap final finalLocals _ trace exec' after (by simp [sysCost])
  · intro final message trace execution
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (fillValue (flatFill operation.params (args.map env.get) (env.get buffer)
        reply))) ⟨rfl, rfl, rfl⟩
    rw [List.append_nil, ← hArgs] at exec
    exact .trapped final message (.terminal final trace (.trapped message) message exec rfl)

theorem record_run_bind (call : LeanExe.Wasi.Call) (fields : Nat) (values : List UInt64)
    (inputs buffers : List LeanExe.Bytes) :
    (SysForm.record fields).runWith call values inputs buffers =
      Action.bind (.sys call (sysArgs call.params values inputs buffers) Action.pure) fun reply =>
        .pure (SysForm.value (.record fields) (reply.errno :: recordWords call.params reply)
          .empty) := rfl

theorem plain_of_record {params : List Param} {size align : Nat} {fields : List (Nat × Nat)}
    (hKinds : params.all Param.argKind = true) :
    (params ++ [Param.record size align fields]).all (fun param => !param.isWindow) = true := by
  rw [List.all_eq_true]
  intro param member
  rcases List.mem_append.mp member with member | member
  · have := List.all_eq_true.mp hKinds param member
    cases param <;> simp_all [Param.isWindow, Param.argKind]
  · rw [List.mem_singleton] at member
    subst member
    rfl

/-- The code of a record `sys` command gives a `ValueResult`. -/
theorem wp_sys_record_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {budget : Nat} {operation : LeanExe.Wasi.Call} {args : List (Var context .word)}
    {inputs : List (Var context .bytes)} {buffers : List LeanExe.Bytes} {params : List Param}
    {size align : Nat} {fields : List (Nat × Nat)}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf operation]? = some operation)
    (hParams : operation.params = params ++ [.record size align fields])
    (hKinds : params.all Param.argKind = true) (hFits : recordFits size align fields = true)
    (hCount : args.length = operation.argWords)
    (hInputCount : inputs.length = operation.inputCount)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (used : ∀ arg ∈ args, liveIn arg.index = true)
    (usedInputs : ∀ input ∈ inputs, liveIn input.index = true)
    (at_ : heap.At (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base) (room : base + (fields.length + 3) ≤ locals.positions)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        ((SysForm.record fields.length).runWith operation (args.map env.get) (inputs.map env.get)
          buffers)
        initial.host trace residual final →
        sysCost (.record fields.length) operation trace ≤ budget) :
    wp target (sysRecordCodeWith calls operation
        (args.map fun arg => (slots.getD arg.index default).loc)
        (inputs.map fun input => (slots.getD input.index default).loc) base)
      (ValueResult host env slots liveIn live base (SysForm.record fields.length).ty
        ((SysForm.record fields.length).runWith operation (args.map env.get) (inputs.map env.get)
          buffers)
        (sysCost (.record fields.length) operation) heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨held, below⟩ := sys_args_held vars args used
  obtain ⟨items, itemsEq, heldItems, reps, belowInputs⟩ := sys_inputs_held vars apart [] inputs
    usedInputs (fun _ _ _ _ _ _ _ b member => nomatch member)
  have plain : operation.params.all (fun param => !param.isWindow) = true := by
    rw [hParams]; exact plain_of_record hKinds
  have hItemCount : items.length = operation.inputCount := by
    rw [← hInputCount, ← List.length_map (f := Prod.snd), itemsEq, List.length_map]
  have hArgs : sysArgs operation.params (args.map env.get) (inputs.map env.get) buffers =
      flatArgsWith operation.params (args.map env.get) (items.map Prod.snd) := by
    rw [← itemsEq]
    refine sysArgs_plain plain (by rw [List.length_map, hCount]; rfl) ?_
    rw [List.length_map, hItemCount, Call.inputCount, hParams]
    clear hParams hItemCount
    induction params with
    | nil => rfl
    | cons param params ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hKinds
      simp only [List.cons_append, List.countP_cons, List.count_cons, ih hKinds.2]
      cases param <;> simp_all [Param.argKind, Param.takesBytes]
  have hRecord : recordOf operation.params = some (size, align, fields) := by
    rw [hParams]; exact recordOf_record size align fields hKinds
  have hBlock : recordBlock operation.params = size + align - 1 := by
    simp [recordBlock, hRecord]
  obtain ⟨hSize, hAlign, hBlockBound⟩ := recordFits_bounds hFits
  have hBlockNat : (UInt64.ofNat (size + align - 1)).toNat = size + align - 1 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  rw [← List.append_nil (sysRecordCodeWith calls operation _ _ base)]
  refine wp_sys_record_with (aborts := aborts) runtime layout profile hImports sourceHost hHost
    hCall hParams hKinds hFits held
    (by rw [List.length_map, hCount, Call.argWords, argWords_plain plain]; rfl)
    (fun place member => Or.inl (below place member)) heldItems hItemCount
    (fun place member => Or.inl (belowInputs place member))
    (fun item member => by
      obtain ⟨length, rep, apart⟩ := reps item member
      exact ⟨length, rep, fun r hr => (apart r hr).1⟩) at_ cap low (by omega) ?_ ?_ ?_ ?_
  · intro hAbort
    obtain ⟨within, bound⟩ := resources hAbort
    have hCost := bound [] _ _ (Prefix.refl _ initial.host)
    simp only [sysCost, hBlock] at hCost
    have hCostEq := Verified.Bytes.allocationCost_eq (count := UInt64.ofNat (size + align - 1))
      (by rw [hBlockNat]; omega) (by rw [hBlockNat]; omega)
    rw [hBlockNat] at hCostEq
    rw [hCostEq] at hCost
    exact (within.mono hCost).room cap
  · intro hAbort final sameWorld
    exact .trapped final _ (CommandResult.resource_refl hAbort sameWorld)
  · intro heap' final finalLocals trace reply execution step top outside
    rw [wp_nil]
    have hLength := recordWords_length hRecord reply
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value (.record fields.length)
        (reply.errno :: recordWords operation.params reply) .empty)) (Exec.pure final.host _)
    rw [List.append_nil, ← hArgs, ← record_run_bind] at exec
    refine .returned _ heap' final finalLocals
      ((reply.errno :: recordWords operation.params reply).map Value.i64) trace exec ?_ ?_
    · refine sys_after vars apart selected step (outside.frame (by omega)) ?_ rfl
      simp only [SysForm.ty, SysForm.value, Ty.Rep]
      exact (wordsElem_values _ _ (by simp [hLength])).symm
    · simp only [sysCost, hBlock]
      exact top
  · intro final message trace execution
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value (.record fields.length)
        (reply.errno :: recordWords operation.params reply) .empty)) ⟨rfl, rfl, rfl⟩
    rw [List.append_nil, ← hArgs, ← record_run_bind] at exec
    exact .trapped final message (.terminal final trace (.trapped message) message exec rfl)

theorem iovec_fill_run_bind (call : LeanExe.Wasi.Call) (values : List UInt64)
    (inputs buffers : List LeanExe.Bytes) :
    SysForm.iovecRead.runWith call values inputs buffers =
      Action.bind (.sys call (sysArgs call.params values inputs buffers) Action.pure) fun reply =>
        .pure (fillValue (readFill call.params values (buffers.headD .empty) reply)) := rfl

theorem iovec_write_run_bind (call : LeanExe.Wasi.Call) (values : List UInt64)
    (inputs buffers : List LeanExe.Bytes) :
    SysForm.iovecWrite.runWith call values inputs buffers =
      Action.bind (.sys call (sysArgs call.params values inputs buffers) Action.pure) fun reply =>
        .pure (SysForm.value .iovecWrite [reply.errno, reply.word 0] .empty) := rfl

theorem poll_run_bind (call : LeanExe.Wasi.Call) (values : List UInt64)
    (inputs buffers : List LeanExe.Bytes) :
    SysForm.poll.runWith call values inputs buffers =
      Action.bind (.sys call (sysArgs call.params values inputs buffers) Action.pure) fun reply =>
        .pure (SysForm.value .poll (reply.errno :: pollWords reply) .empty) := rfl

/-- The code of a read `sys` command that fills a window of its buffer gives a `ValueResult`. -/
theorem wp_sys_iovec_fill_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {operation : LeanExe.Wasi.Call} {args : List (Var context .word)}
    {buffer : Var context .bytes} {offset : Bool}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf operation]? = some operation)
    (hParams : operation.params = iovecParams false offset)
    (hCount : args.length = operation.argWords)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (used : ∀ arg ∈ args, liveIn arg.index = true)
    (hBufferIn : liveIn buffer.index = true) (hBufferOut : live buffer.index = false)
    (hOwned : (slots.getD buffer.index default).mode = .owned)
    (at_ : heap.At (PureTransport.erase initial))
    (low : locals.params.length ≤ base) (room : base + 6 ≤ locals.positions) :
    wp target (sysIovecReadCodeWith calls operation
        (args.map fun arg => (slots.getD arg.index default).loc)
        (slots.getD buffer.index default).loc base)
      (ValueResult host env slots liveIn live base SysForm.iovecRead.ty
        (SysForm.iovecRead.runWith operation (args.map env.get) [] [env.get buffer])
        (sysCost .iovecRead operation) heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨held, below⟩ := sys_args_held vars args used
  obtain ⟨root, size, bufferHeld, hRoot, hSize, hRep, bufferBelow, _⟩ :=
    sys_buffer_held vars hBufferIn hOwned
  have hArgs : sysArgs operation.params (args.map env.get) [] [env.get buffer] =
      flatArgsWith operation.params
        (lowerWords operation.params (args.map env.get) [env.get buffer]) [] := by
    have hInputs : lowerInputs operation.params (args.map env.get) [] = [] := by
      rw [hParams]
      cases offset <;> rfl
    rw [sysArgs, hInputs]
  rw [← List.append_nil (sysIovecReadCodeWith calls operation _ _ base)]
  refine wp_sys_iovec_fill_with hImports hHost hCall hParams held
    (by rw [List.length_map, hCount]) below hRoot hSize bufferBelow hRep at_ low room ?_ ?_
  · intro final finalLocals trace reply execution step rep outside
    rw [wp_nil]
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (fillValue (readFill operation.params (args.map env.get) (env.get buffer)
        reply))) (Exec.pure final.host _)
    rw [List.append_nil, ← hArgs] at exec
    have hErrno : (readFill operation.params (args.map env.get) (env.get buffer) reply).errno =
        reply.errno := fillResult_errno _ _ _ _ _ _
    have after := fill_sys_after (type := wordsBytesTy 2) vars apart selected hBufferIn
      hBufferOut hOwned bufferHeld step (outside.frame room) (fillValue_rep rep)
      (fillValue_blocks _ root size _)
    rw [hErrno] at after
    have exec' : Exec (observedHost host)
        (SysForm.iovecRead.runWith operation (args.map env.get) [] [env.get buffer]) initial.host
        trace (.returned (fillValue (readFill operation.params (args.map env.get) (env.get buffer)
          reply))) final.host := exec
    exact .returned _ heap final finalLocals _ trace exec' after (by simp [sysCost])
  · intro final message trace execution
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (fillValue (readFill operation.params (args.map env.get) (env.get buffer)
        reply))) ⟨rfl, rfl, rfl⟩
    rw [List.append_nil, ← hArgs] at exec
    exact .trapped final message (.terminal final trace (.trapped message) message exec rfl)

/-- The code of a write `sys` command of a window of its input gives a `ValueResult`. -/
theorem wp_sys_iovec_window_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {target : Module} {host : Host World} (hImports : target.imports = ABI.importsWith calls)
    {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {operation : LeanExe.Wasi.Call} {args : List (Var context .word)}
    {input : Var context .bytes} {offset : Bool}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf operation]? = some operation)
    (hParams : operation.params = iovecParams true offset)
    (hCount : args.length = operation.argWords)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (used : ∀ arg ∈ args, liveIn arg.index = true)
    (usedInput : liveIn input.index = true)
    (at_ : heap.At (PureTransport.erase initial))
    (low : locals.params.length ≤ base) (room : base + 8 ≤ locals.positions) :
    wp target (sysIovecWindowCodeWith calls operation
        (args.map fun arg => (slots.getD arg.index default).loc)
        (slots.getD input.index default).loc base)
      (ValueResult host env slots liveIn live base SysForm.iovecWrite.ty
        (SysForm.iovecWrite.runWith operation (args.map env.get) [env.get input] [])
        (sysCost .iovecWrite operation) heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨held, below⟩ := sys_args_held vars args used
  obtain ⟨items, itemsEq, heldItems, reps, belowInputs⟩ := sys_inputs_held vars apart [] [input]
    (fun other member => by rw [List.mem_singleton] at member; subst member; exact usedInput)
    (fun _ _ _ _ _ _ _ b member => nomatch member)
  have hLen : items.length = 1 := by simpa using congrArg List.length itemsEq
  obtain ⟨item, rfl⟩ := List.length_eq_one_iff.mp hLen
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at itemsEq
  obtain ⟨root, bytes⟩ := item
  simp only at itemsEq
  subst itemsEq
  obtain ⟨⟨hRoot, hSize, _⟩, _⟩ := List.forall₂_cons.mp heldItems
  obtain ⟨length, rep, _⟩ := reps _ (List.mem_singleton_self _)
  have hSizeEq : length = LeanExe.Bytes.size (env.get input) := rep.size_eq.symm
  subst hSizeEq
  rw [← List.append_nil (sysIovecWindowCodeWith calls operation _ _ base)]
  refine wp_sys_iovec_window_with hImports hHost hCall hParams held
    (by rw [List.length_map, hCount]) below hRoot hSize
    (belowInputs _ (List.mem_singleton_self _)) rep at_ low room ?_ ?_
  · intro final finalLocals trace reply execution step outside
    rw [wp_nil]
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value .iovecWrite [reply.errno, reply.word 0] .empty))
      (Exec.pure final.host _)
    rw [List.append_nil, ← iovec_write_run_bind] at exec
    refine .returned _ heap final finalLocals ([reply.errno, reply.word 0].map Value.i64) trace
      exec ?_ (by simp [sysCost])
    refine sys_after vars apart selected step (outside.frame room) ?_ rfl
    simp only [SysForm.ty, SysForm.value, Ty.Rep]
    exact (wordsElem_values _ _ rfl).symm
  · intro final message trace execution
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value .iovecWrite [reply.errno, reply.word 0] .empty)) ⟨rfl, rfl, rfl⟩
    rw [List.append_nil, ← iovec_write_run_bind] at exec
    exact .trapped final message (.terminal final trace (.trapped message) message exec rfl)

/-- The code of a `poll` command gives a `ValueResult`. -/
theorem wp_sys_poll_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {budget : Nat} {operation : LeanExe.Wasi.Call} {args : List (Var context .word)}
    {buffers : List LeanExe.Bytes} {records : List (List Field)}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (hCall : calls[calls.idxOf operation]? = some operation)
    (hParams : operation.params = [.subscriptions records, .result32])
    (hFit : subscriptionsFit records = true)
    (hCount : args.length = operation.argWords)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (used : ∀ arg ∈ args, liveIn arg.index = true)
    (at_ : heap.At (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base) (room : base + 9 ≤ locals.positions)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        (SysForm.poll.runWith operation (args.map env.get) [] buffers) initial.host trace
        residual final →
        sysCost .poll operation trace ≤ budget) :
    wp target (sysPollCodeWith calls operation
        (args.map fun arg => (slots.getD arg.index default).loc) base)
      (ValueResult host env slots liveIn live base SysForm.poll.ty
        (SysForm.poll.runWith operation (args.map env.get) [] buffers)
        (sysCost .poll operation) heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨held, below⟩ := sys_args_held vars args used
  have plain : operation.params.all (fun param => !param.isWindow) = true := by
    rw [hParams]; rfl
  have hArgs : sysArgs operation.params (args.map env.get) [] buffers =
      flatArgsWith operation.params (args.map env.get) [] :=
    sysArgs_plain plain (by rw [List.length_map, hCount]; rfl) (by rw [hParams]; rfl)
  have hBlock : pollBlock operation.params = 80 * records.length + 7 := by
    rw [hParams]; rfl
  obtain ⟨_, _, _, hBlockBound⟩ := subscriptionsFit_facts hFit
  have hBlockNat : (UInt64.ofNat (80 * records.length + 7)).toNat = 80 * records.length + 7 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  rw [← List.append_nil (sysPollCodeWith calls operation _ base)]
  refine wp_sys_poll_with (aborts := aborts) runtime layout profile hImports sourceHost hHost
    hCall hParams hFit held
    (by rw [List.length_map, hCount, Call.argWords, argWords_plain plain]; rfl)
    below at_ cap low room ?_ ?_ ?_ ?_
  · intro hAbort
    obtain ⟨within, bound⟩ := resources hAbort
    have hCost := bound [] _ _ (Prefix.refl _ initial.host)
    simp only [sysCost, hBlock] at hCost
    have hCostEq := Verified.Bytes.allocationCost_eq
      (count := UInt64.ofNat (80 * records.length + 7)) (by rw [hBlockNat]; omega)
      (by rw [hBlockNat]; omega)
    rw [hBlockNat] at hCostEq
    rw [hCostEq] at hCost
    exact (within.mono hCost).room cap
  · intro hAbort final sameWorld
    exact .trapped final _ (CommandResult.resource_refl hAbort sameWorld)
  · intro heap' final finalLocals trace reply execution step top outside
    rw [wp_nil]
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value .poll (reply.errno :: pollWords reply) .empty))
      (Exec.pure final.host _)
    rw [List.append_nil, ← hArgs, ← poll_run_bind] at exec
    refine .returned _ heap' final finalLocals ((reply.errno :: pollWords reply).map Value.i64)
      trace exec ?_ ?_
    · refine sys_after vars apart selected step (outside.frame (by omega)) ?_ rfl
      simp only [SysForm.ty, SysForm.value, Ty.Rep]
      exact (wordsElem_values _ _ rfl).symm
    · simp only [sysCost, hBlock]
      exact top
  · intro final message trace execution
    have exec := execution.bind (rest := []) (next := fun reply =>
      Action.pure (SysForm.value .poll (reply.errno :: pollWords reply) .empty)) ⟨rfl, rfl, rfl⟩
    rw [List.append_nil, ← hArgs, ← poll_run_bind] at exec
    exact .trapped final message (.terminal final trace (.trapped message) message exec rfl)

/-- What readiness gives about a `sys` command. -/
theorem sys_ready_facts {calls : List LeanExe.Wasi.Call} {operation : LeanExe.Wasi.Call}
    {form : SysForm} {args : List (Var context .word)} {inputs buffers : List (Var context .bytes)}
    (ready : (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs buffers).callsReady calls = true) :
    operation.compiled = true ∧ operation.form = form ∧ args.length = operation.argWords ∧
      inputs.length = operation.inputCount ∧ buffers.length = operation.bufferCount ∧
      ∀ use ∈ operation.uses, calls[calls.idxOf use]? = some use := by
  simp only [Command.callsReady, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at ready
  obtain ⟨⟨⟨⟨⟨compiled, form'⟩, count⟩, inputCount⟩, bufferCount⟩, uses⟩ := ready
  refine ⟨compiled, form', count, inputCount, bufferCount, fun use member => ?_⟩
  have hMember := uses use member
  exact List.getElem?_eq_some_iff.mpr ⟨List.idxOf_lt_length_of_mem hMember,
    List.getElem_idxOf (List.idxOf_lt_length_of_mem hMember)⟩

theorem bufferCount_flat {params : List Param} (kinds : params.all Param.inputKind = true) :
    params.countP Param.takesBuffer = params.count .output := by
  induction params with
  | nil => rfl
  | cons param params ih =>
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    rw [List.countP_cons, List.count_cons, ih kinds.2]
    cases param <;> simp_all [Param.inputKind, Param.flatKind, Param.takesBuffer]

theorem bufferCount_record {params : List Param} {size align : Nat} {fields : List (Nat × Nat)}
    (kinds : params.all Param.argKind = true) :
    (params ++ [Param.record size align fields]).countP Param.takesBuffer = 0 := by
  rw [List.countP_eq_zero]
  intro param member
  rcases List.mem_append.mp member with member | member
  · have := List.all_eq_true.mp kinds param member
    cases param <;> simp_all [Param.argKind, Param.takesBuffer]
  · rw [List.mem_singleton] at member
    subst member
    simp [Param.takesBuffer]

/-- The code of a `sys` command gives a `ValueResult`, with its input variables live after it.  The
command consumes each buffer variable, which is owned, dies at the command, and is none of its
inputs. -/
theorem wp_sys_result_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {budget : Nat} {operation : LeanExe.Wasi.Call} {form : SysForm}
    {args : List (Var context .word)} {inputs buffers : List (Var context .bytes)}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (ready : (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs buffers).callsReady calls = true)
    (vars : Holds env slots (fun i => live i || ((buffers.any fun buffer => i == buffer.index) ||
      ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index)))
      base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots (fun i => live i ||
      ((buffers.any fun buffer => i == buffer.index) ||
        ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index)))
      (PureTransport.erase initial) locals ABI.scratch)
    (owned : ∀ buffer ∈ buffers, (slots.getD buffer.index default).mode = .owned ∧
      live buffer.index = false ∧ ∀ input ∈ inputs, input.index ≠ buffer.index)
    (at_ : heap.At (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base) (room : base + form.width ≤ locals.positions)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        (form.runWith operation (args.map env.get) (inputs.map env.get) (buffers.map env.get))
        initial.host trace residual final →
        sysCost form operation trace ≤ budget) :
    wp target (sysInputsCodeWith calls operation form
        (args.map fun arg => (slots.getD arg.index default).loc)
        (inputs.map fun input => (slots.getD input.index default).loc)
        (buffers.map fun buffer => (slots.getD buffer.index default).loc) base)
      (ValueResult host env slots (fun i => live i ||
          ((buffers.any fun buffer => i == buffer.index) ||
            ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index)))
        (fun i => (inputs.any fun input => i == input.index) || live i)
        base form.ty (form.runWith operation (args.map env.get) (inputs.map env.get)
          (buffers.map env.get))
        (sysCost form operation) heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨compiled, formEq, hCount, inputCount, bufferCount, uses⟩ := sys_ready_facts ready
  have selected : ∀ i, ((inputs.any fun input => i == input.index) || live i) = true →
      (live i || ((buffers.any fun buffer => i == buffer.index) ||
        ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index))) =
        true := by
    intro i h
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with h | h <;> simp [h]
  have used : ∀ arg ∈ args, (live arg.index ||
      ((buffers.any fun buffer => arg.index == buffer.index) ||
        ((inputs.any fun input => arg.index == input.index) ||
          args.any fun other => arg.index == other.index))) = true := by
    intro arg member
    have hAny : (args.any fun other => arg.index == other.index) = true :=
      List.any_eq_true.mpr ⟨arg, member, by simp⟩
    simp [hAny]
  have usedInputs : ∀ input ∈ inputs, (live input.index ||
      ((buffers.any fun buffer => input.index == buffer.index) ||
        ((inputs.any fun other => input.index == other.index) ||
          args.any fun arg => input.index == arg.index))) = true := by
    intro input member
    have hAny : (inputs.any fun other => input.index == other.index) = true :=
      List.any_eq_true.mpr ⟨input, member, by simp⟩
    simp [hAny]
  have usedBuffers : ∀ buffer ∈ buffers, (live buffer.index ||
      ((buffers.any fun other => buffer.index == other.index) ||
        ((inputs.any fun input => buffer.index == input.index) ||
          args.any fun arg => buffer.index == arg.index))) = true := by
    intro buffer member
    have hAny : (buffers.any fun other => buffer.index == other.index) = true :=
      List.any_eq_true.mpr ⟨buffer, member, by simp⟩
    simp [hAny]
  have dying : ∀ buffer ∈ buffers,
      ((inputs.any fun input => buffer.index == input.index) || live buffer.index) = false := by
    intro buffer member
    obtain ⟨_, notLive, distinct⟩ := owned buffer member
    simp only [Bool.or_eq_false_iff, notLive, and_true, List.any_eq_false, beq_iff_eq]
    exact fun input inputMember same => distinct input inputMember same.symm
  cases hReporter : operation.reporter with
  | none =>
    cases hRecord : recordOf operation.params with
    | none =>
      have hCall := uses operation (by simp [LeanExe.Wasi.Call.uses, hReporter])
      by_cases hRead : operation.params.contains (.iovec false) = true
      · have hForm : form = .iovecRead := by
          rw [← formEq]
          simp only [LeanExe.Wasi.Call.form, hReporter, hRecord, hRead, ite_true]
        subst hForm
        simp only [LeanExe.Wasi.Call.compiled, hReporter, hRecord, hRead, ite_true,
          Bool.or_eq_true, beq_iff_eq] at compiled
        obtain ⟨offset, hParams⟩ : ∃ offset, operation.params = iovecParams false offset := by
          rcases compiled with h | h
          · exact ⟨false, h⟩
          · exact ⟨true, h⟩
        have hNoInputs : inputs = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [inputCount, iovec_inputCount hParams]
          rfl
        subst hNoInputs
        obtain ⟨buffer, rfl⟩ : ∃ buffer, buffers = [buffer] := by
          have hOne : buffers.length = 1 := by
            rw [bufferCount, LeanExe.Wasi.Call.bufferCount, hParams]
            cases offset <;> rfl
          exact List.length_eq_one_iff.mp hOne
        obtain ⟨hOwned, _, _⟩ := owned buffer (List.mem_singleton_self _)
        exact wp_sys_iovec_fill_result_with hImports hHost hCall hParams hCount vars apart
          selected used (usedBuffers buffer (List.mem_singleton_self _))
          (dying buffer (List.mem_singleton_self _)) hOwned at_ low room
      · by_cases hWrite : operation.params.contains (.iovec true) = true
        · have hForm : form = .iovecWrite := by
            rw [← formEq]
            simp only [LeanExe.Wasi.Call.form, hReporter, hRecord, hRead, hWrite, ite_true,
              Bool.false_eq_true, ite_false]
          subst hForm
          simp only [LeanExe.Wasi.Call.compiled, hReporter, hRecord, hRead, hWrite, ite_true,
            Bool.false_eq_true, ite_false, Bool.or_eq_true, beq_iff_eq] at compiled
          obtain ⟨offset, hParams⟩ : ∃ offset, operation.params = iovecParams true offset := by
            rcases compiled with h | h
            · exact ⟨false, h⟩
            · exact ⟨true, h⟩
          have hNoBuffers : buffers = [] := by
            apply List.eq_nil_of_length_eq_zero
            rw [bufferCount, LeanExe.Wasi.Call.bufferCount, hParams]
            cases offset <;> rfl
          subst hNoBuffers
          obtain ⟨input, rfl⟩ : ∃ input, inputs = [input] := by
            have hOne : inputs.length = 1 := by rw [inputCount, iovec_inputCount hParams]; rfl
            exact List.length_eq_one_iff.mp hOne
          exact wp_sys_iovec_window_result_with hImports hHost hCall hParams hCount vars apart
            selected used (usedInputs input (List.mem_singleton_self _)) at_ low room
        · cases hSubscriptions : subscriptionsOf operation.params with
          | some records =>
            simp only [LeanExe.Wasi.Call.compiled, hReporter, hRecord, hRead, hWrite,
              hSubscriptions, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq]
              at compiled
            obtain ⟨hParams, hFit⟩ := compiled
            have hAny : operation.params.any Param.isSubscriptions = true := by
              rw [hParams]; rfl
            have hForm : form = .poll := by
              rw [← formEq]
              simp only [LeanExe.Wasi.Call.form, hReporter, hRecord, hRead, hWrite, hAny,
                Bool.false_eq_true, ite_false, ite_true]
            subst hForm
            have hNoInputs : inputs = [] := by
              apply List.eq_nil_of_length_eq_zero
              rw [inputCount, poll_inputCount hParams]
            subst hNoInputs
            exact wp_sys_poll_result_with runtime layout profile hImports sourceHost hHost hCall
              hParams hFit hCount vars apart selected used at_ cap low room resources
          | none =>
            simp only [LeanExe.Wasi.Call.compiled, hReporter, hRecord, hRead, hWrite,
              hSubscriptions, Bool.false_eq_true, ite_false, Bool.and_eq_true,
              decide_eq_true_eq] at compiled
            have hNoSubscriptions : operation.params.any Param.isSubscriptions = false := by
              apply Bool.eq_false_iff.mpr
              intro hAny
              obtain ⟨param, member, isSubscriptions⟩ := List.any_eq_true.mp hAny
              have := List.all_eq_true.mp compiled.1.1 param member
              cases param <;> simp_all [Param.isSubscriptions, Param.inputKind, Param.flatKind]
            have hForm : form = .flat (operation.params.countP Param.isResult)
                (operation.params.contains .output) := by
              rw [← formEq]
              simp only [LeanExe.Wasi.Call.form, hReporter, hRecord, hRead, hWrite,
                hNoSubscriptions, Bool.false_eq_true, ite_false]
            have hBuffers : buffers.length = operation.params.count .output := by
              rw [bufferCount, LeanExe.Wasi.Call.bufferCount, bufferCount_flat compiled.1.1]
            by_cases hOutput : operation.params.contains .output = true
            · rw [hOutput] at hForm
              subst hForm
              have hOne : operation.params.count .output = 1 := by
                have := List.count_pos_iff.mpr (List.contains_iff_mem.mp hOutput)
                omega
              obtain ⟨buffer, rfl⟩ := List.length_eq_one_iff.mp (hBuffers.trans hOne)
              obtain ⟨hOwned, _, distinct⟩ := owned buffer (List.mem_singleton_self _)
              have hResults : operation.params.countP Param.isResult ≤ 1 := by
                have := compiled.2
                simp only [hOutput, ite_true] at this
                exact this
              exact wp_sys_flat_fill_result_with hImports hHost hCall compiled.1.1 hOne hResults
                hCount inputCount vars apart selected used usedInputs
                (usedBuffers buffer (List.mem_singleton_self _))
                (dying buffer (List.mem_singleton_self _)) hOwned distinct at_ low room
            · have hZero : operation.params.count .output = 0 := by
                simpa [List.contains_iff_mem, List.count_eq_zero] using hOutput
              obtain rfl := List.eq_nil_of_length_eq_zero (hBuffers.trans hZero)
              simp only [Bool.not_eq_true] at hOutput
              rw [hOutput] at hForm
              subst hForm
              exact wp_sys_flat_result_inputs_with hImports hHost hCall compiled.1.1 hZero
                (by have := compiled.2; simp only [hOutput] at this; exact this) hCount
                inputCount vars apart selected used usedInputs at_ low room
    | some record =>
      obtain ⟨size, align, fields⟩ := record
      have hForm : form = .record fields.length := by
        rw [← formEq]
        simp only [LeanExe.Wasi.Call.form, hReporter, hRecord]
      subst hForm
      obtain ⟨hParams, hKinds, hFits⟩ := record_params compiled hReporter hRecord
      have hNoBuffers : buffers = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [bufferCount, LeanExe.Wasi.Call.bufferCount, hParams]
        exact bufferCount_record hKinds
      subst hNoBuffers
      exact wp_sys_record_result_with runtime layout profile hImports sourceHost hHost
        (uses operation (by simp [LeanExe.Wasi.Call.uses, hReporter])) hParams hKinds hFits
        hCount inputCount vars apart selected used usedInputs at_ cap low room resources
  | some name =>
    have hForm : form = .reported := by
      rw [← formEq, LeanExe.Wasi.Call.form, hReporter]
    subst hForm
    simp only [LeanExe.Wasi.Call.compiled, hReporter, beq_iff_eq] at compiled
    have hNoInputs : inputs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [inputCount]
      simp [LeanExe.Wasi.Call.inputCount, compiled, Param.takesBytes]
    have hNoBuffers : buffers = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [bufferCount]
      simp [LeanExe.Wasi.Call.bufferCount, compiled, Param.takesBuffer]
    subst hNoInputs hNoBuffers
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

/-- The code of a `sys` command without the take of a buffer and the release of its input
variables that die give a `ValueResult` for the variables live after the command. -/
theorem wp_sys_released_with {calls : List LeanExe.Wasi.Call} {World : Type}
    {source target : Module} {host : Host World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv (Observed World)} {context : List Ty}
    {env : Env context} {slots : List Slot} {live : Nat → Bool} {base : Nat}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals} {aborts : Bool}
    {budget : Nat} {operation : LeanExe.Wasi.Call} {form : SysForm}
    {args : List (Var context .word)} {inputs buffers : List (Var context .bytes)}
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (ready : (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs buffers).callsReady calls = true)
    (vars : Holds env slots (fun i => live i || ((buffers.any fun buffer => i == buffer.index) ||
      ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index)))
      base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots (fun i => live i ||
      ((buffers.any fun buffer => i == buffer.index) ||
        ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index)))
      (PureTransport.erase initial) locals ABI.scratch)
    (owned : ∀ buffer ∈ buffers, (slots.getD buffer.index default).mode = .owned ∧
      live buffer.index = false ∧ ∀ input ∈ inputs, input.index ≠ buffer.index)
    (at_ : heap.At (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base) (room : base + form.width ≤ locals.positions)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        (form.runWith operation (args.map env.get) (inputs.map env.get) (buffers.map env.get))
        initial.host trace residual final →
        sysCost form operation trace ≤ budget)
    (releaseForm : Encoding.ProgramForm (releaseWhere context slots
      (fun i => (inputs.any fun input => i == input.index) && !live i)))
    (releaseClosed : Relocation.programClosed source.funcs.length (releaseWhere context slots
      (fun i => (inputs.any fun input => i == input.index) && !live i)) = true) :
    wp target (sysInputsCodeWith calls operation form
        (args.map fun arg => (slots.getD arg.index default).loc)
        (inputs.map fun input => (slots.getD input.index default).loc)
        (buffers.map fun buffer => (slots.getD buffer.index default).loc) base ++
      Relocation.programWith calls (releaseWhere context slots
        (fun i => (inputs.any fun input => i == input.index) && !live i)))
      (ValueResult host env slots (fun i => live i ||
          ((buffers.any fun buffer => i == buffer.index) ||
            ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index)))
        live base form.ty (form.runWith operation (args.map env.get) (inputs.map env.get)
          (buffers.map env.get))
        (sysCost form operation) heap initial locals aborts)
      initial locals targetHost := by
  have keptSelected : ∀ i, ((inputs.any fun input => i == input.index) || live i) = true →
      (live i || ((buffers.any fun buffer => i == buffer.index) ||
        ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index))) =
        true := by
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
  apply wp_append
  refine wp.conseq (fun continuation result => ?_)
    (wp_sys_result_with runtime layout profile hImports sourceHost hHost ready vars apart owned
      at_ cap low room resources)
  cases result with
  | returned value finalHeap final finalLocals words trace execution after top =>
    have updated : After env slots _ _ base heap initial locals (.value form.ty) value finalHeap
        final { finalLocals with values := words.reverse ++ locals.values } words :=
      ⟨after.step, after.frame.trans Frame.ofValues, after.holds, after.rep, after.apart⟩
    simp only [Then]
    rw [← List.append_nil (Relocation.programWith calls (releaseWhere context slots
      (fun i => (inputs.any fun input => i == input.index) && !live i)))]
    refine wp_release_context_with (sourceHost := sourceHost) (rest := []) runtime layout profile
      releaseForm releaseClosed updated.holds updated.step.at_ releaseSelected ?_
    intro releasedHeap released evolution topEq releasedWorld
    have resultAfter := After.release vars apart updated keptSelected liveSelected
      (evolution.mono retained)
    rw [wp_nil]
    exact ValueResult.returned value releasedHeap released
      { finalLocals with values := words.reverse ++ locals.values } words trace
      (by rw [releasedWorld]; exact execution) resultAfter (by rw [topEq]; exact top)
  | trapped final message result =>
    simp only [Then]
    exact ValueResult.trapped final message (CommandResult.trap_live result)

theorem bufferCount_le_one {call : LeanExe.Wasi.Call} (compiled : call.compiled = true) :
    call.bufferCount ≤ 1 := by
  unfold LeanExe.Wasi.Call.compiled at compiled
  unfold LeanExe.Wasi.Call.bufferCount
  split at compiled
  · rename_i hReporter
    simp only [beq_iff_eq] at compiled
    rw [compiled]
    decide
  · split at compiled
    · rename_i size align fields hRecord
      simp only [Bool.and_eq_true, beq_iff_eq] at compiled
      obtain ⟨⟨hLast, hKinds⟩, _⟩ := compiled
      obtain ⟨prefix', hPrefix⟩ := List.getLast?_eq_some_iff.mp hLast
      rw [hPrefix, List.dropLast_concat] at hKinds
      rw [hPrefix, bufferCount_record hKinds]
      omega
    · split at compiled
      · simp only [Bool.or_eq_true, beq_iff_eq] at compiled
        rcases compiled with h | h <;> rw [h] <;> decide
      · split at compiled
        · simp only [Bool.or_eq_true, beq_iff_eq] at compiled
          rcases compiled with h | h <;> rw [h] <;> decide
        · split at compiled
          · rename_i records _
            simp only [Bool.and_eq_true, beq_iff_eq] at compiled
            rw [compiled.1]
            simp [Param.takesBuffer]
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at compiled
            rw [bufferCount_flat compiled.1.1]
            exact compiled.1.2

/-- The code of a `sys` command without a buffer, the call and the release of the input variables
that die, gives a `ValueResult`. -/
theorem wp_sys_plain_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    {World : Type} {host : Host World} {targetHost : HostEnv (Observed World)} {depth : UInt64}
    {env : Env context} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {aborts : Bool} {budget : Nat}
    {operation : LeanExe.Wasi.Call} {form : SysForm} {args : List (Var context .word)}
    {inputs : List (Var context .bytes)}
    (valid : targetHost.Satisfies target (hostSpecWith host calls))
    (depthParam : locals.params.head? = some (.i64 depth))
    (positions : locals.positions = h)
    (vars : Holds env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
      (effectSigs := effectSigs) operation form args inputs []).uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
      (effectSigs := effectSigs) operation form args inputs []).uses i) heap
      (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
      (effectSigs := effectSigs) operation form args inputs []).uses i)
      (PureTransport.erase initial) locals ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs []).width ≤ h)
    (ready : (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs []).ReadyWith calls source h slots base live pool)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        (form.runWith operation (args.map env.get) (inputs.map env.get) [])
        initial.host trace residual final →
        sysCost form operation trace +
          pure.sysTakeCost depth (slots.map Slot.mode) live args inputs [] env ≤ budget) :
    wp target ((Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
        args inputs []).codeWith calls (pool := pool) source h slots base live)
      (ValueResult host env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
          (effectSigs := effectSigs) operation form args inputs []).uses i) live base form.ty
        (form.runWith operation (args.map env.get) (inputs.map env.get) [])
        (fun trace => sysCost form operation trace +
          pure.sysTakeCost depth (slots.map Slot.mode) live args inputs [] env)
        heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨fragments, callsOk⟩ := ready
  have fragment := fragments _ (List.mem_singleton_self _)
  have hRoom : base + form.width ≤ locals.positions := by
    rw [positions]
    simpa [Command.width] using room
  have hTake : pure.sysTakeCost depth (slots.map Slot.mode) live args inputs [] env = 0 := rfl
  simp only [hTake, Nat.add_zero] at resources ⊢
  simp only [Command.codeWith, Command.uses] at vars scratch ⊢
  exact wp_sys_released_with (operation := operation) (form := form) (args := args)
    (inputs := inputs) (buffers := []) (env := env) (slots := slots) (live := live) (base := base)
    (heap := heap) (initial := initial) (locals := locals) (aborts := aborts) (budget := budget)
    facts.runtime facts.layout facts.profile facts.imports sourceHost valid callsOk vars scratch
    (fun _ member => nomatch member) at_ cap low hRoom resources fragment.1 fragment.2

/-- The take of the buffer variable `buffer` into the two locals from `base`, as a `ret` of the
variable takes it, which moves an owned buffer that dies there and copies it otherwise, followed by
`inner`, the code that consumes the taken buffer as variable 0 of the extended context, gives the
outcome of `inner` with a charge that adds the take's.  `takeLive` holds the variables live after
the take, among them those that `inner` reads, and `bodyIn` the variables that `inner` reads or
keeps in the extended context. -/
theorem wp_take_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    {World : Type} {host : Host World} {targetHost : HostEnv (Observed World)} {depth : UInt64}
    {env : Env context} {slots : List Slot} {live takeLive bodyIn : Nat → Bool}
    {h base width : Nat} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {aborts : Bool} {budget : Nat} {type : Ty} {action : Action type.denote}
    {cost : List Event → Nat} {buffer : Var context .bytes} {inner : Program}
    (selected : ∀ i, live i = true → takeLive i = true)
    (tailSelected : ∀ i, bodyIn (i + 1) = true → takeLive i = true)
    (outputSelected : ∀ i, shift 1 live i = true → bodyIn i = true)
    (depthParam : locals.params.head? = some (.i64 depth))
    (positions : locals.positions = h)
    (vars : Holds env slots (fun i => takeLive i || (Expr.var (S := pureSigs) buffer).uses i)
      base heap (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => takeLive i || (Expr.var (S := pureSigs) buffer).uses i)
      heap (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots
      (fun i => takeLive i || (Expr.var (S := pureSigs) buffer).uses i)
      (PureTransport.erase initial) locals ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + (Ty.bytes.width + max (max (Expr.var (S := pureSigs) buffer).width
      (copyWidth .bytes)) width) ≤ h)
    (takeForm : Encoding.ProgramForm ((Expr.var (S := pureSigs) buffer).code (pool := pool) h
      slots (base + Ty.bytes.width) takeLive ++
      coerceCode h .bytes ((Expr.var (S := pureSigs) buffer).mode (slots.map Slot.mode)) .owned
        (base + Ty.bytes.width)))
    (takeClosed : Relocation.programClosed source.funcs.length
      ((Expr.var (S := pureSigs) buffer).code (pool := pool) h slots (base + Ty.bytes.width)
        takeLive ++
      coerceCode h .bytes ((Expr.var (S := pureSigs) buffer).mode (slots.map Slot.mode)) .owned
        (base + Ty.bytes.width)) = true)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host) action initial.host trace residual final →
        cost trace + pure.ownedCost depth (slots.map Slot.mode) takeLive
          (Expr.var (S := pureSigs) buffer) env ≤ budget)
    (hInner : ∀ (takeHeap : Heap) (takeStore : Store (Observed World)) (boundLocals : Locals)
        (innerBudget : Nat),
      Holds (.cons (env.get buffer) env) (⟨base, .owned⟩ :: slots) bodyIn
        (base + Ty.bytes.width) takeHeap (PureTransport.erase takeStore) boundLocals →
      Holds.ApartFrom (.cons (env.get buffer) env) (⟨base, .owned⟩ :: slots) bodyIn
        (PureTransport.erase takeStore) boundLocals ABI.scratch →
      takeHeap.At (PureTransport.erase takeStore) →
      (PureTransport.erase takeStore).memoryCap source 0 ≤ 65535 →
      boundLocals.params.length ≤ base + Ty.bytes.width →
      base + Ty.bytes.width + width ≤ boundLocals.positions →
      takeStore.host = initial.host →
      (aborts = false → takeHeap.Within (PureTransport.erase takeStore) source innerBudget ∧
        ∀ trace residual final, Prefix (observedHost host) action takeStore.host trace residual
          final → cost trace ≤ innerBudget) →
      wp target inner
        (ValueResult host (.cons (env.get buffer) env) (⟨base, .owned⟩ :: slots) bodyIn
          (shift 1 live) (base + Ty.bytes.width) type action cost takeHeap takeStore boundLocals
          aborts)
        takeStore boundLocals targetHost) :
    wp target (Relocation.programWith calls ((Expr.var (S := pureSigs) buffer).code (pool := pool)
        h slots (base + Ty.bytes.width) takeLive ++
        coerceCode h .bytes ((Expr.var (S := pureSigs) buffer).mode (slots.map Slot.mode)) .owned
          (base + Ty.bytes.width)) ++
        (storeCode h base Ty.bytes.types ++ inner))
      (ValueResult host env slots (fun i => takeLive i || (Expr.var (S := pureSigs) buffer).uses i)
        live base type action
        (fun trace => cost trace + pure.ownedCost depth (slots.map Slot.mode) takeLive
          (Expr.var (S := pureSigs) buffer) env)
        heap initial locals aborts)
      initial locals targetHost := by
  have midSelected : ∀ i, takeLive i = true →
      (takeLive i || (Expr.var (S := pureSigs) buffer).uses i) = true := by
    intro i hi
    simp [hi]
  simp only [Ty.width] at room
  have spec := (Expr.var (S := pureSigs) buffer).code_spec source pure.funs pure.flags
    (pure.callBounds depth) (pure.callFits depth) sourceHost facts.runtime
    (Calls.at facts.calls depth) (List.nil_subset _) (fun _ => depthParam) env slots [] takeLive
  have hTakeCost : returnCost pure.funs pure.flags (pure.callBounds depth)
      (Expr.var (S := pureSigs) buffer) env slots [] takeLive (PureTransport.erase initial)
      locals = pure.ownedCost depth (slots.map Slot.mode) takeLive
        (Expr.var (S := pureSigs) buffer) env :=
    pure.returnCost_nil depth _ env slots _ _ locals
  refine wp_return_with facts.runtime facts.layout facts.profile spec takeForm takeClosed positions
    rfl (vars.mono (by simp only [Ty.width]; omega)) at_ safe cap
    (by simp only [Ty.width]; omega) (by simp only [Ty.width]; omega) rfl ?_ ?_
  · intro failure final sameWorld
    cases aborts with
    | true => exact ValueResult.trapped final _ (CommandResult.resource_refl rfl sameWorld)
    | false =>
      obtain ⟨within, bound⟩ := resources rfl
      have hCost := bound [] _ _ (Prefix.refl _ initial.host)
      have hWithin : heap.Within (PureTransport.erase initial) source
          (returnCost pure.funs pure.flags (pure.callBounds depth)
            (Expr.var (S := pureSigs) buffer) env slots [] takeLive
            (PureTransport.erase initial) locals) := by
        rw [hTakeCost]
        exact within.mono (by omega)
      have fitsVar : (Expr.var (S := pureSigs) buffer).fits pure.funs (pure.callFits depth)
          env = true := rfl
      simp [fitsVar, hWithin] at failure
  · intro takeHeap takeStore takeLocals words takeAfter sameHost takeTop
    have firstAfter := takeAfter.lower vars midSelected (by simp only [Ty.width]; omega)
    have rep : Ty.bytes.Rep .owned takeHeap (PureTransport.erase takeStore) words
        (env.get buffer) := firstAfter.rep
    refine wp_storeCode words h base Ty.bytes.types takeLocals locals.values rep.typed
      (firstAfter.frame.positions.trans positions)
      (by rw [firstAfter.frame.params]; exact low)
      (by rw [Ty.types_length, firstAfter.frame.positions, positions]; simp [Ty.width]; omega)
      ?_
    intro boundLocals frame held _
    have frame' : Frame base takeLocals { boundLocals with values := locals.values } :=
      ⟨frame.params, frame.length, frame.below, frame.below32⟩
    have boundVars := bind_context_holds (bodyIn := bodyIn) firstAfter frame' held tailSelected
    have boundScratch := bind_context_scratch (bodyIn := bodyIn) firstAfter vars scratch frame'
      held midSelected tailSelected
    have grows := takeTop rfl
    rw [hTakeCost] at grows
    have core := hInner takeHeap takeStore { boundLocals with values := locals.values }
      (budget - pure.ownedCost depth (slots.map Slot.mode) takeLive
        (Expr.var (S := pureSigs) buffer) env)
      boundVars boundScratch takeAfter.step.at_ (by rw [takeAfter.step.cap source]; exact cap)
      (by rw [frame'.params, firstAfter.frame.params]; simp [Ty.width]; omega)
      (by rw [frame'.positions, firstAfter.frame.positions, positions]; simp [Ty.width]; omega)
      sameHost
      (fun noAbort => by
        obtain ⟨within, bound⟩ := resources noAbort
        have hTake := bound [] _ _ (Prefix.refl _ initial.host)
        refine ⟨within.shift grows (by omega) (takeAfter.step.cap source), ?_⟩
        intro trace residual final progress
        have := bound trace residual final (by rw [← sameHost]; exact progress)
        omega)
    refine wp.conseq (fun continuation result => ?_) core
    cases result with
    | returned value finalHeap final finalLocals finalWords trace execution after top =>
      have combined := After.bind_value vars scratch firstAfter frame' held after tailSelected
        midSelected selected
      refine ValueResult.returned value finalHeap final finalLocals finalWords trace ?_ combined
        ?_
      · rw [← sameHost]
        exact execution
      · omega
    | trapped final message classification =>
      refine ValueResult.trapped final message ?_
      cases classification with
      | terminal final trace outcome message execution terminal =>
        refine CommandResult.terminal final trace outcome message ?_ terminal
        rw [← sameHost]
        exact execution
      | resource final trace residual allowed progress =>
        refine CommandResult.resource final trace residual allowed ?_
        rw [← sameHost]
        exact progress

/-- The code of a `sys` command with a buffer, the take of the buffer, the call, and the release of
the input variables that die, gives a `ValueResult` whose charge adds the take's. -/
theorem wp_sys_take_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    {World : Type} {host : Host World} {targetHost : HostEnv (Observed World)} {depth : UInt64}
    {env : Env context} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {aborts : Bool} {budget : Nat}
    {operation : LeanExe.Wasi.Call} {form : SysForm} {args : List (Var context .word)}
    {inputs : List (Var context .bytes)} {buffer : Var context .bytes}
    (valid : targetHost.Satisfies target (hostSpecWith host calls))
    (depthParam : locals.params.head? = some (.i64 depth))
    (positions : locals.positions = h)
    (vars : Holds env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
      (effectSigs := effectSigs) operation form args inputs [buffer]).uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
      (effectSigs := effectSigs) operation form args inputs [buffer]).uses i) heap
      (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
      (effectSigs := effectSigs) operation form args inputs [buffer]).uses i)
      (PureTransport.erase initial) locals ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs [buffer]).width ≤ h)
    (ready : (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs [buffer]).ReadyWith calls source h slots base live pool)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        (form.runWith operation (args.map env.get) (inputs.map env.get) [env.get buffer])
        initial.host trace residual final →
        sysCost form operation trace +
          pure.sysTakeCost depth (slots.map Slot.mode) live args inputs [buffer] env ≤ budget) :
    wp target ((Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
        args inputs [buffer]).codeWith calls (pool := pool) source h slots base live)
      (ValueResult host env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
          (effectSigs := effectSigs) operation form args inputs [buffer]).uses i) live base form.ty
        (form.runWith operation (args.map env.get) (inputs.map env.get) [env.get buffer])
        (fun trace => sysCost form operation trace +
          pure.sysTakeCost depth (slots.map Slot.mode) live args inputs [buffer] env)
        heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨fragments, callsOk⟩ := ready
  have takeFragment := fragments _ List.mem_cons_self
  have releaseFragment := fragments _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have takeEq : (fun i => sysTakeLive live args inputs i ||
      (Expr.var (S := pureSigs) buffer).uses i) =
      (fun i => live i || (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs)
        operation form args inputs [buffer]).uses i) := by
    funext i
    simp only [sysTakeLive, Expr.uses, Command.uses, List.any_cons, List.any_nil,
      Bool.or_false]
    cases live i <;> cases (i == buffer.index) <;> simp
  have selected : ∀ i, live i = true → sysTakeLive live args inputs i = true := by
    intro i hi
    simp [sysTakeLive, hi]
  let bodyIn : Nat → Bool := fun i => shift 1 live i ||
    ((([.here] : List (Var (.bytes :: context) .bytes)).any fun b => i == b.index) ||
      (((inputs.map (Var.there (s := .bytes))).any fun input => i == input.index) ||
        (args.map (Var.there (s := .bytes))).any fun arg => i == arg.index))
  have tailSelected : ∀ i, bodyIn (i + 1) = true → sysTakeLive live args inputs i = true := by
    intro i hi
    simp only [bodyIn, shift_add, List.any_cons, List.any_nil, Bool.or_false, List.any_map,
      Function.comp_def, Var.index] at hi
    simp only [sysTakeLive]
    simpa using hi
  have outputSelected : ∀ i, shift 1 live i = true → bodyIn i = true := by
    intro i hi
    simp [bodyIn, hi]
  have selEq : (fun i => ((inputs.map (Var.there (s := .bytes))).any fun input =>
      i == input.index) && !shift 1 live i) =
      (fun i => (inputs.any fun input => i == input.index + 1) && !shift 1 live i) := by
    funext i
    simp [List.any_map, Function.comp_def, Var.index]
  have codeEq : sysInputsCodeWith calls operation form
      ((args.map (Var.there (s := .bytes))).map fun arg =>
        ((⟨base, .owned⟩ :: slots : List Slot).getD arg.index default).loc)
      ((inputs.map (Var.there (s := .bytes))).map fun input =>
        ((⟨base, .owned⟩ :: slots : List Slot).getD input.index default).loc)
      (([.here] : List (Var (.bytes :: context) .bytes)).map fun buffer =>
        ((⟨base, .owned⟩ :: slots : List Slot).getD buffer.index default).loc)
      (base + Ty.bytes.width) ++
      Relocation.programWith calls (releaseWhere (.bytes :: context) (⟨base, .owned⟩ :: slots)
        (fun i => ((inputs.map (Var.there (s := .bytes))).any fun input => i == input.index) &&
          !shift 1 live i)) =
      sysInputsCodeWith calls operation form
        (args.map fun arg => (slots.getD arg.index default).loc)
        (inputs.map fun input => (slots.getD input.index default).loc) [base]
        (base + Ty.bytes.width) ++
      Relocation.programWith calls (releaseWhere (.bytes :: context) (⟨base, .owned⟩ :: slots)
        (fun i => (inputs.any fun input => i == input.index + 1) && !shift 1 live i)) := by
    rw [selEq]
    simp [List.map_map, Function.comp_def, Var.index]
  have argsEq : (args.map (Var.there (s := .bytes))).map
      (Env.get (.cons (env.get buffer) env)) = args.map env.get := by
    simp only [List.map_map, Function.comp_def, Env.get]
  have inputsEq : (inputs.map (Var.there (s := .bytes))).map
      (Env.get (.cons (env.get buffer) env)) = inputs.map env.get := by
    simp only [List.map_map, Function.comp_def, Env.get]
  have buffersEq : ([.here] : List (Var (.bytes :: context) .bytes)).map
      (Env.get (.cons (env.get buffer) env)) = [env.get buffer] := rfl
  have readyExt : (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      (args.map (Var.there (s := .bytes))) (inputs.map (Var.there (s := .bytes)))
      ([.here] : List (Var (.bytes :: context) .bytes))).callsReady calls = true := by
    simpa only [Command.callsReady, List.length_map, List.length_cons, List.length_nil]
      using callsOk
  rw [← takeEq] at vars safe scratch ⊢
  simp only [Command.codeWith, List.append_assoc]
  refine wp_take_with facts sourceHost (bodyIn := bodyIn) (width := form.width) selected
    tailSelected outputSelected depthParam positions vars at_ safe scratch cap low room
    takeFragment.1 takeFragment.2 resources ?_
  intro takeHeap takeStore boundLocals innerBudget boundVars boundScratch takeAt takeCap boundLow
    boundRoom _ innerResources
  have core := wp_sys_released_with (budget := innerBudget)
    facts.runtime facts.layout facts.profile facts.imports sourceHost valid readyExt
    boundVars boundScratch
    (fun b member => by
      rw [List.mem_singleton] at member
      subst member
      refine ⟨rfl, by simp [shift, Var.index], fun input member => ?_⟩
      obtain ⟨other, _, rfl⟩ := List.mem_map.mp member
      simp [Var.index])
    takeAt takeCap boundLow boundRoom
    (fun noAbort => by
      rw [argsEq, inputsEq, buffersEq]
      exact innerResources noAbort)
    (by rw [selEq]; exact releaseFragment.1) (by rw [selEq]; exact releaseFragment.2)
  rw [codeEq, argsEq, inputsEq, buffersEq] at core
  exact core

/-- The code of a `sys` command, the take of its buffer when it has one, the call, and the release
of the input variables that die, gives a `ValueResult` whose charge adds the take's. -/
theorem wp_sys_command_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    {World : Type} {host : Host World} {targetHost : HostEnv (Observed World)} {depth : UInt64}
    {env : Env context} {slots : List Slot} {live : Nat → Bool} {h base : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {aborts : Bool} {budget : Nat}
    {operation : LeanExe.Wasi.Call} {form : SysForm} {args : List (Var context .word)}
    {inputs buffers : List (Var context .bytes)}
    (valid : targetHost.Satisfies target (hostSpecWith host calls))
    (depthParam : locals.params.head? = some (.i64 depth))
    (positions : locals.positions = h)
    (vars : Holds env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
      (effectSigs := effectSigs) operation form args inputs buffers).uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
      (effectSigs := effectSigs) operation form args inputs buffers).uses i) heap
      (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
      (effectSigs := effectSigs) operation form args inputs buffers).uses i)
      (PureTransport.erase initial) locals ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs buffers).width ≤ h)
    (ready : (Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
      args inputs buffers).ReadyWith calls source h slots base live pool)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      ∀ trace residual final, Prefix (observedHost host)
        (form.runWith operation (args.map env.get) (inputs.map env.get) (buffers.map env.get))
        initial.host trace residual final →
        sysCost form operation trace +
          pure.sysTakeCost depth (slots.map Slot.mode) live args inputs buffers env ≤ budget) :
    wp target ((Command.sys (pureSigs := pureSigs) (effectSigs := effectSigs) operation form
        args inputs buffers).codeWith calls (pool := pool) source h slots base live)
      (ValueResult host env slots (fun i => live i || (Command.sys (pureSigs := pureSigs)
          (effectSigs := effectSigs) operation form args inputs buffers).uses i) live base form.ty
        (form.runWith operation (args.map env.get) (inputs.map env.get) (buffers.map env.get))
        (fun trace => sysCost form operation trace +
          pure.sysTakeCost depth (slots.map Slot.mode) live args inputs buffers env)
        heap initial locals aborts)
      initial locals targetHost := by
  obtain ⟨fragments, callsOk⟩ := ready
  obtain ⟨compiled, _, _, _, bufferCount, _⟩ := sys_ready_facts callsOk
  cases buffers with
  | nil =>
    exact wp_sys_plain_with facts sourceHost valid depthParam positions vars at_ safe scratch cap
      low room ⟨fragments, callsOk⟩ resources
  | cons buffer rest =>
    cases rest with
    | cons second more =>
      have le := bufferCount_le_one compiled
      rw [← bufferCount] at le
      simp only [List.length_cons] at le
      omega
    | nil =>
      exact wp_sys_take_with facts sourceHost valid depthParam positions vars at_ safe scratch cap
        low room ⟨fragments, callsOk⟩ resources

theorem command_sys_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure effects pool) (sourceHost : HostEnv Unit)
    (operation : LeanExe.Wasi.Call) (form : SysForm) (args : List (Var context .word))
    (inputs buffers : List (Var context .bytes)) :
    CommandCodeSpecWith calls source target pure effects pool
      (.sys operation form args inputs buffers) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid _ depthParam positions vars at_ safe scratch cap low room ready _ _
  refine wp.conseq (fun continuation result => ?_)
    (wp_sys_command_with (aborts := true) (budget := 0) facts sourceHost valid depthParam
      positions vars at_ safe scratch cap low room ready
      (fun impossible => Bool.noConfusion impossible))
  cases result with
  | returned value finalHeap final finalLocals words trace execution after top =>
    exact CommandResult.returned (result := .value form.ty) value finalHeap final finalLocals
      words trace execution after
  | trapped final message result => exact result

theorem cost_command_sys_spec_with {calls : List LeanExe.Wasi.Call}
    {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty}
    (facts : CompilerFactsWith calls source target pure (program.funs pure.funs) pool)
    (sourceHost : HostEnv Unit)
    (operation : LeanExe.Wasi.Call) (form : SysForm) (args : List (Var context .word))
    (inputs buffers : List (Var context .bytes)) :
    CostCommandCodeSpecWith calls source target pure program pool
      (.sys operation form args inputs buffers) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid _ depthParam positions vars at_ safe scratch cap low room ready _ _ resources
  refine wp.conseq (fun continuation result => ?_)
    (wp_sys_command_with (aborts := aborts) (budget := budget) facts sourceHost valid depthParam
      positions vars at_ safe scratch cap low room ready
      (fun hAbort => ⟨(resources hAbort).1, fun trace residual final progress =>
        (resources hAbort).2.sys progress⟩))
  cases result with
  | returned value finalHeap final finalLocals words trace execution after top =>
    exact CostCommandResult.returned (command := .sys operation form args inputs buffers) value
      finalHeap final finalLocals words trace _ true (.sys execution) after (fun _ => top)
  | trapped final message result =>
    exact CostCommandResult.trapped final message result

end Verified.Wasi
