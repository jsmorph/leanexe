import Verified.Wasi.WriteHelper
import Verified.Wasi.AfterScratch
import Verified.Wasi.CommandSpec
import Verified.Wasi.PurePrefix
import Verified.AlignedControl

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem write_after {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {live : Nat → Bool} {base : Nat} {heap : Heap}
    {initial final : Store World} {locals : Locals} {errno count : UInt64}
    (at_ : heap.At (PureTransport.erase initial))
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots live (PureTransport.erase initial) locals ABI.scratch)
    (frame : GuestFrame initial final [ABI.scratch]) :
    After env slots live live base heap initial locals (.value (.elem (.prod .word .word)))
      (errno, count) heap final locals [.i64 errno, .i64 count] :=
  ⟨(frame.scratchStep at_).mono (fun _ kept => kept.2) (fun _ member => member),
    Frame.refl base locals, frame.scratchHolds at_ vars apart (Frame.refl base locals),
    rfl, Holds.Apart.ofScalar rfl⟩

theorem wp_write_command_call {World : Type} {source target : Module} {host : Host World}
    {context : List Ty} {env : Env context} {slots : List Slot} {live : Nat → Bool}
    {base : Nat} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {root length : UInt64} {bytes : LeanExe.Bytes} {output : Output} {typeIdx : Nat}
    {aborts : Bool} {targetHost : HostEnv (Observed World)}
    (hImports : target.imports = ABI.imports)
    (hFunction : target.funcs[match output with
      | .stdout => source.funcs.length + 1
      | .stderr => source.funcs.length + 2]? = some (writeFunction output typeIdx))
    (hHost : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (vars : Holds env slots live base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots live (PureTransport.erase initial) locals ABI.scratch)
    (rep : Bytes.Rep heap (PureTransport.erase initial) root length bytes) :
    wp target [.call (match output with
      | .stdout => Wrappers.stdoutIndex source
      | .stderr => Wrappers.stderrIndex source)]
      (CommandResult host env slots live live base (.value (.elem (.prod .word .word)))
        (Action.bind (.write output bytes .pure) fun result => .pure (result.errno, result.count))
        heap initial locals aborts)
      initial { locals with values := .i64 length :: .i64 root :: locals.values } targetHost := by
  let index := match output with
    | .stdout => source.funcs.length + 1
    | .stderr => source.funcs.length + 2
  suffices execution : wp target [.call (3 + index)]
      (CommandResult host env slots live live base (.value (.elem (.prod .word .word)))
        (Action.bind (.write output bytes .pure) fun result => .pure (result.errno, result.count))
        heap initial locals aborts)
      initial { locals with values := .i64 length :: .i64 root :: locals.values } targetHost by
    cases output <;>
      simpa only [index, Wrappers.stdoutIndex, Wrappers.stderrIndex, Module.extraIndex,
        Nat.add_assoc] using execution
  refine wp_write_helper_at hImports hFunction hHost at_ rep ?_ ?_
  · intro final result trace execution frame _ _
    rw [wp_nil]
    have flat : Exec (observedHost host)
        (Action.bind (.write output bytes .pure) fun result => .pure (result.errno, result.count))
        initial.host trace (.returned (result.errno, result.count)) final.host := by
      simpa only [List.append_nil] using
        execution.bind (next := fun result => .pure (result.errno, result.count))
          (rest := []) (.pure final.host (result.errno, result.count))
    exact CommandResult.returned (result := .value (.elem (.prod .word .word)))
      (result.errno, result.count) heap final locals [.i64 result.errno, .i64 result.count]
      trace flat (write_after at_ vars apart frame)
  · intro final message trace execution _ _ _
    have flat : Exec (observedHost host)
        (Action.bind (.write output bytes .pure) fun result => .pure (result.errno, result.count))
        initial.host trace (.trapped message) final.host := by
      simpa only [List.append_nil] using
        execution.bind (next := fun result => .pure (result.errno, result.count))
          (rest := []) ⟨rfl, rfl, rfl⟩
    exact CommandResult.terminal final trace (.trapped message) message flat rfl

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
  have transported := PureTransport.wp_prefix layout profile form closed initial.host pureCode
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

theorem write_after_release {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap finalHeap : Heap}
    {initial middle final : Store World} {locals : Locals} {errno count : UInt64}
    (at_ : heap.At (PureTransport.erase initial))
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (frame : GuestFrame initial middle [ABI.scratch])
    (evolution : Evolves env slots liveIn live base heap (PureTransport.erase middle) locals
      finalHeap (PureTransport.erase final) locals) :
    After env slots liveIn live base heap initial locals (.value (.elem (.prod .word .word)))
      (errno, count) finalHeap final locals [.i64 errno, .i64 count] := by
  have scratch := frame.scratchStep at_
  refine ⟨scratch.trans evolution.step ?_, Frame.refl base locals, evolution.holds,
    rfl, Holds.Apart.ofScalar rfl⟩
  intro region kept
  refine ⟨kept.2, fun _ => ?_⟩
  refine Holds.KeepDying.transfer_kept vars scratch (Frame.refl base locals)
    (fun _ hIn _ => hIn) ?_ kept.1
  intro type x hIn _ words held width block member
  exact regionsDisjoint_symm (apart type x hIn words held width block member)

theorem wp_command_write {World : Type} {source target : Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs} {effectFuns : EffectFuns effectSigs}
    {context : List Ty} {env : Env context} {slots : List Slot} {live : Nat → Bool}
    {base h : Nat} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {bytes : Var context .bytes} {output : Output} {typeIdx : Nat} {pool : Bytes.LiteralPool}
    {aborts : Bool} {targetHost : HostEnv (Observed World)} {sourceHost : HostEnv Unit}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (hFunction : target.funcs[match output with
      | .stdout => source.funcs.length + 1
      | .stderr => source.funcs.length + 2]? = some (writeFunction output typeIdx))
    (hHost : targetHost.Satisfies target (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (positions : locals.positions = h)
    (vars : Holds env slots (fun i => live i || i == bytes.index) base heap
      (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots (fun i => live i || i == bytes.index)
      (PureTransport.erase initial) locals ABI.scratch)
    (cleanupForm : Encoding.ProgramForm
      (releaseWhere context slots (fun i => i == bytes.index && !live i)))
    (cleanupClosed : Relocation.programClosed source.funcs.length
      (releaseWhere context slots (fun i => i == bytes.index && !live i)) = true) :
    wp target ((Command.write (pureSigs := pureSigs) (effectSigs := effectSigs) output bytes).code
        (pool := pool) source h slots base live)
      (CommandResult host env slots (fun i => live i || i == bytes.index) live base
        (.value (.elem (.prod .word .word)))
        ((Command.write output bytes).denote funs effectFuns env)
        heap initial locals aborts) initial locals targetHost := by
  let all := fun i => live i || i == bytes.index
  let selected := fun i => i == bytes.index && !live i
  let index := match output with
    | .stdout => source.funcs.length + 1
    | .stderr => source.funcs.length + 2
  let action : Action (UInt64 × UInt64) :=
    Action.bind (.write output (env.get bytes) .pure) fun result => .pure (result.errno, result.count)
  have actionEq : (Command.write output bytes).denote funs effectFuns env = action := by
    cases output <;> rfl
  rw [actionEq]
  have hBytes : all bytes.index = true := by simp only [all, beq_self_eq_true, Bool.or_true]
  obtain ⟨_, words, held, represented⟩ := vars.get bytes hBytes
  obtain ⟨root, length, rfl, rep⟩ := represented
  have selectLive : ∀ i, selected i = true → all i = true := by
    intro i member
    simp only [selected, Bool.and_eq_true] at member
    simp only [all, member.1, Bool.or_true]
  have liveEq : (fun i => all i && !selected i) = live := by
    funext i
    dsimp only [all, selected]
    cases live i <;> cases (i == bytes.index) <;> rfl
  suffices execution : wp target (loadCode h (slots.getD bytes.index default).loc Ty.bytes.types ++
      ([.call (3 + index)] ++
        Relocation.program (releaseWhere context slots selected)))
    (CommandResult host env slots all live base (.value (.elem (.prod .word .word)))
      action heap initial locals aborts) initial locals targetHost by
    cases output <;>
      simpa only [Command.code, index, selected, Wrappers.stdoutIndex, Wrappers.stderrIndex,
        Module.extraIndex, List.append_assoc, Nat.add_assoc] using execution
  refine wp_loadCode [.i64 root, .i64 length] rfl positions held ?_
  refine wp_write_helper_at hImports hFunction hHost at_ rep ?_ ?_
  · intro middle result trace execution frame _ _
    have middleVars := frame.scratchHolds at_ vars apart (Frame.refl base locals)
    let current : Locals :=
      { locals with values := .i64 result.count :: .i64 result.errno :: locals.values }
    have currentVars : Holds env slots all base heap (PureTransport.erase middle) current :=
      middleVars.agree Frame.ofValues
    rw [← List.append_nil (Relocation.program (releaseWhere context slots selected))]
    refine wp_release_context (sourceHost := sourceHost) (rest := [])
      runtime layout profile cleanupForm cleanupClosed
      currentVars (frame.scratchHeap at_) selectLive ?_
    intro finalHeap final evolution _ sameWorld
    rw [wp_nil]
    have evolved : Evolves env slots all live base heap (PureTransport.erase middle) locals
        finalHeap (PureTransport.erase final) locals := by
      have originalInitial : Evolves env slots all (fun i => all i && !selected i) base heap
          (PureTransport.erase middle) locals finalHeap (PureTransport.erase final) current :=
        ⟨evolution.step, evolution.frame.values, evolution.holds⟩
      simpa only [current, liveEq] using originalInitial.values locals.values
    have returned : Exec (observedHost host) (.write output (env.get bytes) .pure)
        initial.host trace (.returned result) final.host := by
      rw [sameWorld]
      exact execution
    have flat : Exec (observedHost host) action initial.host trace
        (.returned (result.errno, result.count)) final.host := by
      simpa only [List.append_nil] using
        returned.bind (next := fun result => .pure (result.errno, result.count))
          (rest := []) (.pure final.host (result.errno, result.count))
    exact CommandResult.returned (result := .value (.elem (.prod .word .word)))
      (result.errno, result.count) finalHeap final locals [.i64 result.errno, .i64 result.count]
      trace flat (write_after_release at_ vars apart frame evolved)
  · intro final message trace execution _ _ _
    have flat : Exec (observedHost host) action initial.host trace (.trapped message) final.host := by
      simpa only [List.append_nil] using
        execution.bind (next := fun result => .pure (result.errno, result.count))
          (rest := []) ⟨rfl, rfl, rfl⟩
    exact CommandResult.terminal final trace (.trapped message) message flat rfl

end Verified.Wasi
