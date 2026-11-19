import Verified.Wasi.WriteHelper
import Verified.Wasi.AfterScratch
import Verified.Wasi.CommandSpec
import Verified.Wasi.PurePrefix
import Verified.AlignedControl

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem wp_release_context_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {live sel : Nat → Bool} {base : Nat}
    {source target : Module} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {heap : Heap} {initial : Store World} {locals : Locals}
    {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (releaseWhere context slots sel))
    (closed : Relocation.programClosed source.funcs.length (releaseWhere context slots sel) = true)
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (selected : ∀ i, sel i = true → live i = true)
    (next : ∀ finalHeap final,
      Evolves env slots live (fun i => live i && !sel i) base heap
        (PureTransport.erase initial) locals finalHeap (PureTransport.erase final) locals →
      finalHeap.top = heap.top → final.host = initial.host → wp target rest Q final locals targetHost) :
    wp target (Relocation.programWith calls (releaseWhere context slots sel) ++ rest)
      Q initial locals targetHost := by
  let P : Assertion Unit := fun continuation =>
    match continuation with
    | .Fallthrough final finalLocals =>
        ∃ finalHeap, Evolves env slots live (fun i => live i && !sel i) base heap
          (PureTransport.erase initial) locals finalHeap final locals ∧
          finalLocals = locals ∧ finalHeap.top = heap.top
    | _ => False
  have pureCode : wp source (releaseWhere context slots sel) P
      (PureTransport.erase initial) locals sourceHost := by
    have execution := wp_releaseWhere (host := sourceHost) runtime vars at_ selected (rest := []) (Q := P)
      (fun finalHeap final evolution top => by
        simp only [wp_nil, P]
        exact ⟨finalHeap, evolution, True.intro, top⟩)
    simpa only [List.append_nil] using execution
  have transported := PureTransport.wp_prefix_with (calls := calls) layout profile form closed initial.host pureCode
    (rest := rest) (Q := Q) (targetHost := targetHost) (fun continuation post => by
      cases continuation with
      | Fallthrough final finalLocals =>
          obtain ⟨finalHeap, evolution, rfl, top⟩ := post
          apply next finalHeap (PureTransport.restore initial.host final)
          · simpa only [PureTransport.erase_restore] using evolution
          · exact top
          · rfl
      | _ => exact False.elim post)
  simpa only [PureTransport.restore_erase] using transported

theorem wp_release_context {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {live sel : Nat → Bool} {base : Nat}
    {source target : Module} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {heap : Heap} {initial : Store World} {locals : Locals}
    {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (releaseWhere context slots sel))
    (closed : Relocation.programClosed source.funcs.length (releaseWhere context slots sel) = true)
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (selected : ∀ i, sel i = true → live i = true)
    (next : ∀ finalHeap final,
      Evolves env slots live (fun i => live i && !sel i) base heap
        (PureTransport.erase initial) locals finalHeap (PureTransport.erase final) locals →
      finalHeap.top = heap.top → final.host = initial.host → wp target rest Q final locals targetHost) :
    wp target (Relocation.program (releaseWhere context slots sel) ++ rest)
      Q initial locals targetHost := by
  layout_instance wp_release_context_with


/-- The state after a write: the scratch frame of the call, then the release of the variables that
die there, with the window's address and length left in the locals at `base`. -/
theorem write_after_release {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap finalHeap : Heap}
    {initial middle final : Store World} {locals finalLocals : Locals} {errno count : UInt64}
    (at_ : heap.At (PureTransport.erase initial))
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.low)
    (frame : GuestFrame initial middle [ABI.scratch])
    (localFrame : Frame base locals finalLocals)
    (evolution : Evolves env slots liveIn live base heap (PureTransport.erase middle) finalLocals
      finalHeap (PureTransport.erase final) finalLocals) :
    After env slots liveIn live base heap initial locals (.value (.elem (.prod .word .word)))
      (errno, count) finalHeap final finalLocals [.i64 errno, .i64 count] := by
  have scratch := frame.scratchStep at_
  refine ⟨scratch.trans evolution.step ?_, localFrame, evolution.holds,
    rfl, Holds.Apart.ofScalar rfl⟩
  intro region kept
  refine ⟨kept.2, fun _ => ?_⟩
  refine Holds.KeepDying.transfer_kept vars scratch localFrame
    (fun _ hIn _ => hIn) ?_ kept.1
  intro type x hIn _ words held width block member
  exact regionsDisjoint_symm (apart type x hIn words held width block member)

/-- The buffer variable of a write and its window's start and count hold their words in locals
below `base`. -/
theorem write_args_held {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {locals : Locals}
    (vars : Holds env slots liveIn base heap store locals) {buffer : Var context .bytes}
    {start count : Var context .word} (bufferLive : liveIn buffer.index = true)
    (startLive : liveIn start.index = true) (countLive : liveIn count.index = true) :
    ∃ root size,
      locals.get (slots.getD buffer.index default).loc = some (.i64 root) ∧
      locals.get ((slots.getD buffer.index default).loc + 1) = some (.i64 size) ∧
      Bytes.Rep heap store root size (env.get buffer) ∧
      (slots.getD buffer.index default).loc + 2 ≤ base ∧
      locals.get (slots.getD start.index default).loc = some (.i64 (env.get start)) ∧
      (slots.getD start.index default).loc < base ∧
      locals.get (slots.getD count.index default).loc = some (.i64 (env.get count)) ∧
      (slots.getD count.index default).loc < base := by
  obtain ⟨bufferBound, bufferWords, bufferHold, represented⟩ := vars.1 .bytes buffer bufferLive
  obtain ⟨root, size, rfl, rep⟩ := represented
  have hRoot := bufferHold 0 (by simp)
  have hSize := bufferHold 1 (by simp)
  simp only [Ty.types, slotIndex, Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ,
    List.getElem_cons_zero, List.getElem_cons_succ] at hRoot hSize
  obtain ⟨startBound, startWords, startHold, startRep⟩ := vars.1 .word start startLive
  rw [Ty.rep_word] at startRep
  subst startRep
  have hStart := startHold 0 (by simp)
  simp only [slotIndex, Nat.add_zero, List.getD_cons_zero, List.getElem_cons_zero] at hStart
  obtain ⟨countBound, countWords, countHold, countRep⟩ := vars.1 .word count countLive
  rw [Ty.rep_word] at countRep
  subst countRep
  have hCount := countHold 0 (by simp)
  simp only [slotIndex, Nat.add_zero, List.getD_cons_zero, List.getElem_cons_zero] at hCount
  simp only [Ty.width, Elem.width_word] at bufferBound startBound countBound
  exact ⟨root, size, hRoot, hSize, rep, by omega, hStart, by omega, hCount, by omega⟩

/-- The code of a write computes the window of its buffer, calls the write wrapper with the
window's address and length, and releases the variables that die there.  A run that returns
leaves the errno and the count over the locals' operand stack, with the state that `After` states
and the heap's top unchanged, and a run that traps does so in the write. -/
theorem wp_write_command_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs} {effectFuns : EffectFuns effectSigs}
    {context : List Ty} {env : Env context} {slots : List Slot} {live : Nat → Bool}
    {base h : Nat} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {buffer : Var context .bytes} {start count : Var context .word} {output : Output}
    {typeIdx : Nat} {pool : Bytes.LiteralPool}
    {targetHost : HostEnv (Observed World)} {sourceHost : HostEnv Unit}
    {Q : Assertion (Observed World)}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (hFunction : target.funcs[Wrappers.outputPosition source output]? =
      some (writeFunction output typeIdx))
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (at_ : heap.At (PureTransport.erase initial))
    (positions : locals.positions = h)
    (low : locals.params.length ≤ base) (room : base + 2 ≤ h)
    (vars : Holds env slots (fun i => live i ||
        (i == buffer.index || (i == start.index || i == count.index))) base heap
      (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots (fun i => live i ||
        (i == buffer.index || (i == start.index || i == count.index)))
      (PureTransport.erase initial) locals ABI.low)
    (cleanupForm : Encoding.ProgramForm (releaseWhere context slots (fun i =>
      (i == buffer.index || (i == start.index || i == count.index)) && !live i)))
    (cleanupClosed : Relocation.programClosed source.funcs.length (releaseWhere context slots
      (fun i => (i == buffer.index || (i == start.index || i == count.index)) && !live i)) =
        true)
    (hReturned : ∀ (result : LeanExe.Wasi.WriteResult) (finalHeap : Heap)
      (final : Store (Observed World)) (finalLocals : Locals) (trace : List Event),
      Exec (observedHost host) ((Command.write (pureSigs := pureSigs) (effectSigs := effectSigs)
          output buffer start count).denote funs effectFuns env)
        initial.host trace (.returned (result.errno, result.count)) final.host →
      After env slots (fun i => live i ||
          (i == buffer.index || (i == start.index || i == count.index))) live base heap initial
        locals (.value (.elem (.prod .word .word))) (result.errno, result.count) finalHeap final
        finalLocals [.i64 result.errno, .i64 result.count] →
      finalHeap.top = heap.top →
      Q (.Fallthrough final
        { finalLocals with values := .i64 result.count :: .i64 result.errno :: locals.values }))
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (trace : List Event),
      Exec (observedHost host) ((Command.write (pureSigs := pureSigs) (effectSigs := effectSigs)
          output buffer start count).denote funs effectFuns env)
        initial.host trace (.trapped message) final.host →
      Q (.Trap final message)) :
    wp target ((Command.write (pureSigs := pureSigs) (effectSigs := effectSigs) output buffer start
        count).codeWith calls (pool := pool) source h slots base live) Q initial locals
      targetHost := by
  let used := fun i => i == buffer.index || (i == start.index || i == count.index)
  let all := fun i => live i || used i
  let selected := fun i => used i && !live i
  let index := Wrappers.outputPosition source output
  let bytes := (env.get buffer).range (env.get start) (env.get count)
  let action : Action (UInt64 × UInt64) :=
    Action.bind (.write output bytes .pure) fun result => .pure (result.errno, result.count)
  have actionEq : (Command.write (pureSigs := pureSigs) (effectSigs := effectSigs) output buffer
      start count).denote funs effectFuns env = action := by
    cases output <;> rfl
  rw [actionEq] at hReturned hTrap
  obtain ⟨root, size, hRoot, hSize, rep, bufferBelow, hStart, startBelow, hCount, countBelow⟩ :=
    write_args_held (buffer := buffer) (start := start) (count := count) vars (by simp) (by simp)
      (by simp)
  have selectLive : ∀ i, selected i = true → all i = true := by
    intro i member
    simp only [selected, Bool.and_eq_true] at member
    simp only [all, member.1, Bool.or_true]
  have liveEq : (fun i => all i && !selected i) = live := by
    funext i
    dsimp only [all, selected]
    cases live i <;> cases used i <;> rfl
  suffices execution : wp target (windowCode (slots.getD buffer.index default).loc
      (slots.getD start.index default).loc (slots.getD count.index default).loc base ++
      ([.localGet base, .localGet (base + 1), .call (3 + calls.length + index)] ++
        Relocation.programWith calls (releaseWhere context slots selected))) Q initial locals
      targetHost by
    cases output <;>
      simpa only [Command.codeWith, index, selected, used, Wrappers.outputPosition,
        Wrappers.stdoutIndexWith, Wrappers.stderrIndexWith,
        Module.extraIndexWith, List.append_assoc, Nat.add_assoc] using execution
  have hPositions : base + 1 < locals.params.length + locals.locals.length := by
    have := positions
    simp only [Locals.positions] at this
    omega
  refine wp_window_code hRoot hSize hStart hCount (by omega) countBelow low hPositions ?_
  intro s1 outside1 values1 getAddress getLength
  have localFrame : Frame base locals s1 := outside1.frame (by rw [positions]; exact room)
  have hWindow := window_at rep at_ (env.get start) (env.get count)
  refine wp_localGet_get getAddress ?_
  refine wp_localGet_get (by rw [Locals.get_values]; exact getLength) ?_
  refine wp_write_helper_at_with
    (s := { s1 with values := .i64 (root + windowFirstWord size (env.get start)) :: s1.values })
    (values := s1.values) hImports hFunction hHost at_ rep hWindow ?_ ?_
  · intro middle result trace execution frame _ _
    have middleVars := frame.scratchHolds at_ vars apart localFrame
    let current : Locals :=
      { s1 with values := .i64 result.count :: .i64 result.errno :: s1.values }
    have currentVars : Holds env slots all base heap (PureTransport.erase middle) current :=
      middleVars.agree Frame.ofValues
    rw [← List.append_nil (Relocation.programWith calls (releaseWhere context slots selected))]
    refine wp_release_context_with (sourceHost := sourceHost) (rest := [])
      runtime layout profile cleanupForm cleanupClosed
      currentVars (frame.scratchHeap at_) selectLive ?_
    intro finalHeap final evolution topEq sameWorld
    rw [wp_nil]
    have evolved : Evolves env slots all live base heap (PureTransport.erase middle) s1
        finalHeap (PureTransport.erase final) s1 := by
      have original : Evolves env slots all (fun i => all i && !selected i) base heap
          (PureTransport.erase middle) s1 finalHeap (PureTransport.erase final) current :=
        ⟨evolution.step, ⟨evolution.frame.params, evolution.frame.length, evolution.frame.below,
          evolution.frame.below32⟩, evolution.holds⟩
      simpa only [current, liveEq] using original.values s1.values
    have returned : Exec (observedHost host) (.write output bytes .pure)
        initial.host trace (.returned result) final.host := by
      rw [sameWorld]
      exact execution
    have flat : Exec (observedHost host) action initial.host trace
        (.returned (result.errno, result.count)) final.host := by
      simpa only [List.append_nil] using
        returned.bind (next := fun result => .pure (result.errno, result.count))
          (rest := []) (.pure final.host (result.errno, result.count))
    have done := hReturned result finalHeap final s1 trace flat
      (write_after_release at_ vars apart frame localFrame evolved) topEq
    rw [← values1] at done
    exact done
  · intro final message trace execution _ _ _
    have flat : Exec (observedHost host) action initial.host trace (.trapped message)
        final.host := by
      simpa only [List.append_nil] using
        execution.bind (next := fun result => .pure (result.errno, result.count))
          (rest := []) ⟨rfl, rfl, rfl⟩
    exact hTrap final message trace flat

theorem wp_command_write_with {calls : List LeanExe.Wasi.Call}
    {World : Type} {source target : Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs} {effectFuns : EffectFuns effectSigs}
    {context : List Ty} {env : Env context} {slots : List Slot} {live : Nat → Bool}
    {base h : Nat} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {buffer : Var context .bytes} {start count : Var context .word} {output : Output}
    {typeIdx : Nat} {pool : Bytes.LiteralPool}
    {aborts : Bool} {targetHost : HostEnv (Observed World)} {sourceHost : HostEnv Unit}
    (runtime : Runtime source) (layout : Relocation.LayoutWith calls source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.importsWith calls)
    (hFunction : target.funcs[Wrappers.outputPosition source output]? =
      some (writeFunction output typeIdx))
    (hHost : targetHost.Satisfies target (hostSpecWith host calls))
    (at_ : heap.At (PureTransport.erase initial))
    (positions : locals.positions = h)
    (low : locals.params.length ≤ base) (room : base + 2 ≤ h)
    (vars : Holds env slots (fun i => live i ||
        (i == buffer.index || (i == start.index || i == count.index))) base heap
      (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots (fun i => live i ||
        (i == buffer.index || (i == start.index || i == count.index)))
      (PureTransport.erase initial) locals ABI.low)
    (cleanupForm : Encoding.ProgramForm (releaseWhere context slots (fun i =>
      (i == buffer.index || (i == start.index || i == count.index)) && !live i)))
    (cleanupClosed : Relocation.programClosed source.funcs.length (releaseWhere context slots
      (fun i => (i == buffer.index || (i == start.index || i == count.index)) && !live i)) =
        true) :
    wp target ((Command.write (pureSigs := pureSigs) (effectSigs := effectSigs) output buffer start
        count).codeWith calls (pool := pool) source h slots base live)
      (CommandResult host env slots (fun i => live i ||
          (i == buffer.index || (i == start.index || i == count.index))) live base
        (.value (.elem (.prod .word .word)))
        ((Command.write output buffer start count).denote funs effectFuns env)
        heap initial locals aborts) initial locals targetHost :=
  wp_write_command_with (sourceHost := sourceHost) runtime layout profile hImports hFunction hHost
    at_ positions low room vars apart cleanupForm cleanupClosed
    (fun result finalHeap final finalLocals trace execution after _ =>
      CommandResult.returned (result := .value (.elem (.prod .word .word)))
        (result.errno, result.count) finalHeap final finalLocals
        [.i64 result.errno, .i64 result.count] trace execution after)
    (fun final message trace execution =>
      CommandResult.terminal final trace (.trapped message) message execution rfl)

theorem wp_command_write {World : Type} {source target : Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs} {effectFuns : EffectFuns effectSigs}
    {context : List Ty} {env : Env context} {slots : List Slot} {live : Nat → Bool}
    {base h : Nat} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {buffer : Var context .bytes} {start count : Var context .word} {output : Output}
    {typeIdx : Nat} {pool : Bytes.LiteralPool}
    {aborts : Bool} {targetHost : HostEnv (Observed World)} {sourceHost : HostEnv Unit}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (hFunction : target.funcs[match output with
      | .stdout => source.funcs.length + 1
      | .stderr => source.funcs.length + 2]? = some (writeFunction output typeIdx))
    (hHost : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (positions : locals.positions = h)
    (low : locals.params.length ≤ base) (room : base + 2 ≤ h)
    (vars : Holds env slots (fun i => live i ||
        (i == buffer.index || (i == start.index || i == count.index))) base heap
      (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots (fun i => live i ||
        (i == buffer.index || (i == start.index || i == count.index)))
      (PureTransport.erase initial) locals ABI.low)
    (cleanupForm : Encoding.ProgramForm (releaseWhere context slots (fun i =>
      (i == buffer.index || (i == start.index || i == count.index)) && !live i)))
    (cleanupClosed : Relocation.programClosed source.funcs.length (releaseWhere context slots
      (fun i => (i == buffer.index || (i == start.index || i == count.index)) && !live i)) =
        true) :
    wp target ((Command.write (pureSigs := pureSigs) (effectSigs := effectSigs) output buffer start
        count).code (pool := pool) source h slots base live)
      (CommandResult host env slots (fun i => live i ||
          (i == buffer.index || (i == start.index || i == count.index))) live base
        (.value (.elem (.prod .word .word)))
        ((Command.write output buffer start count).denote funs effectFuns env)
        heap initial locals aborts) initial locals targetHost := by
  layout_instance wp_command_write_with

end Verified.Wasi
