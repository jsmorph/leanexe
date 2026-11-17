import Verified.Shim.Satisfies
import Verified.Wasi.CommandTotal

/-!
The footprint theorem at the specification level.  A run of `Exec` or `Prefix` under
`linuxHost F L I replies` extends the world's layer events by images of its WASI events, which
hold their replies and write within the guest's address space or into the timespec, and a trapped
`Exec` run traps with `shimTrap` or `exitRejected`.  `footprint_of_result` carries the WASI
command theorem's classification of a run of `_start` to `Footprint`, and `shim_footprint`
composes `compiled_native_start_run_with`, unchanged, with `linuxEnv_satisfies`: for every reply
sequence, every Talos run of `_start` of a command whose flat calls the shim implements, under
`linuxEnv F L I replies calls` with enough fuel, traps with a final world whose events extend the
initial ones by images of a WASI trace of the command's action.
-/

namespace Verified.Shim

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi

theorem Images.append {F : OpenFlags} {L : ShimLayout} {I : Launch} {events es ls es' ls'}
    (first : Images F L I events es ls) (second : Images F L I (events ++ ls) es' ls') :
    Images F L I events (es ++ es') (ls ++ ls') := by
  revert second
  induction first with
  | nil =>
    intro second
    simpa using second
  | cons image _ rest =>
    intro second
    rw [List.cons_append, List.append_assoc]
    exact .cons image (rest (by simpa only [List.append_assoc] using second))

theorem Carried.append {replies : Linux.Replies} :
    ∀ {k : Nat} {l l' : List Linux.Event}, Carried replies k l →
      Carried replies (k + l.length) l' → Carried replies k (l ++ l')
  | _, [], _, _, rest => by simpa using rest
  | k, e :: l, l', ⟨carries, first⟩, rest =>
    ⟨carries, Carried.append first (by
      simp only [List.length_cons] at rest
      rwa [show k + 1 + l.length = k + (l.length + 1) by omega])⟩

/-- The world `w'` extends the layer events of `w` by images of the WASI events `trace`, which
hold their replies of `replies`, counted from the events of `w`, and write within the guest's
address space or into the timespec. -/
def Appended (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    (w w' : LinuxWorld) (trace : List Wasi.Event) : Prop :=
  ∃ ls, w'.events = w.events ++ ls ∧ Images F L I w.events trace ls ∧
    Carried replies w.events.length ls ∧
    ∀ e ∈ ls, WritesWithin L (2 ^ 32) e

section Appended

variable {F : OpenFlags} {L : ShimLayout} {I : Launch} {replies : Linux.Replies}

theorem Appended.refl (w : LinuxWorld) : Appended F L I replies w w [] :=
  ⟨[], by simp, .nil, trivial, by simp⟩

theorem Appended.trans {w w' w'' : LinuxWorld} {first rest : List Wasi.Event}
    (h : Appended F L I replies w w' first) (h' : Appended F L I replies w' w'' rest) :
    Appended F L I replies w w'' (first ++ rest) := by
  obtain ⟨ls, grown, images, carried, within⟩ := h
  obtain ⟨ls', grown', images', carried', within'⟩ := h'
  refine ⟨ls ++ ls', by rw [grown', grown, List.append_assoc],
    images.append (by rwa [grown] at images'),
    carried.append (by rwa [grown, List.length_append] at carried'), ?_⟩
  intro e member
  rcases List.mem_append.mp member with left | right
  · exact within e left
  · exact within' e right

theorem ShimStep.appended {w w' : LinuxWorld} {e : Wasi.Event}
    (h : ShimStep F L I replies w e w') : Appended F L I replies w w' [e] := by
  obtain ⟨l, image, carried, within, rfl⟩ := h
  exact ⟨l, rfl, by simpa using Images.cons image .nil, carried, within⟩

theorem Appended.unchanged {w w' : LinuxWorld} {e : Wasi.Event}
    (image : Image F L I w.events e [])
    (same : w'.events = w.events) : Appended F L I replies w w' [e] :=
  ⟨[], by simp [same], by simpa using Images.cons image .nil, trivial, by simp⟩

end Appended

theorem readReply_trapped {count ret : UInt64} {output : List UInt8} {message : String}
    {committed : Bytes} (h : readReply count ret output = .trapped message committed) :
    message = shimTrap := by
  unfold readReply at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with same
      exact same.symm

theorem writeReply_trapped {count ret committed : UInt64} {message : String}
    (h : writeReply count ret = .trapped message committed) : message = shimTrap := by
  unfold writeReply at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with same
      exact same.symm

theorem randomCalls_trapped {a : UInt64} {length : Nat} {message : String}
    {outputs : List Bytes} :
    ∀ {done : Nat} {filled : List UInt8} {l : List Linux.Event},
      RandomCalls a length done filled l (.trapped message outputs) → message = shimTrap
  | _, _, [], ⟨_, same⟩ => by cases same
  | _, _, _ :: _, ⟨_, _, _, _, _, rest⟩ => by
    split at rest
    · exact randomCalls_trapped rest
    · obtain ⟨_, same⟩ := rest
      unfold randomLast at same
      split_ifs at same
      cases same
      rfl

theorem openCalls_trapped {L : ShimLayout} {dir : UInt64} {path how : List UInt8}
    {message : String} {outputs : List Bytes} :
    ∀ {calls : Nat} {l : List Linux.Event},
      OpenCalls L dir path how calls l (.trapped message outputs) → message = shimTrap
  | _, [], h => h.elim
  | _, _ :: _, ⟨_, _, rest⟩ => by
    split at rest
    · exact openCalls_trapped rest
    · obtain ⟨_, same⟩ := rest
      unfold openReply at same
      split_ifs at same
      cases same
      rfl

/-- The shim traps a flat call only with `shimTrap`. -/
theorem sysImage_trapped {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {call : Call} {args : List Arg} {message : String}
    {outputs : List Bytes} {l : List Linux.Event}
    (image : SysImage F L I events call args (.trapped message outputs) l) :
    message = shimTrap := by
  have member := sysImage_mem image
  simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [sysImage_clock] at image
    unfold ClockImage at image
    split at image
    · split at image
      · obtain ⟨_, _, _, same⟩ := image
        simp only [clockReply] at same
        split_ifs at same <;> cases same <;> rfl
      · obtain ⟨_, same⟩ := image
        cases same
    · exact image.elim
  · rw [sysImage_random] at image
    unfold RandomImage at image
    split at image
    · obtain ⟨_, image⟩ := image
      exact randomCalls_trapped image
    · exact image.elim
  · rw [sysImage_argsSizes] at image
    obtain ⟨_, _, same⟩ := image
    unfold sizesReply at same
    split_ifs at same
  · rw [sysImage_args] at image
    obtain ⟨_, _, same⟩ := image
    unfold stringsReply at same
    split_ifs at same
    cases same
    rfl
  · rw [sysImage_environSizes] at image
    obtain ⟨_, _, same⟩ := image
    unfold sizesReply at same
    split_ifs at same
  · rw [sysImage_environ] at image
    obtain ⟨_, _, same⟩ := image
    unfold stringsReply at same
    split_ifs at same
    cases same
    rfl
  · rw [sysImage_open] at image
    unfold OpenImage at image
    split at image
    · split at image
      · exact openCalls_trapped image
      · obtain ⟨_, same⟩ := image
        cases same
    · exact image.elim
  · rw [sysImage_close] at image
    unfold CloseImage at image
    split at image
    · split at image
      · obtain ⟨_, _, same⟩ := image
        unfold closeReply at same
        split_ifs at same
        cases same
        rfl
      · obtain ⟨_, same⟩ := image
        cases same
    · exact image.elim
  · rw [sysImage_read] at image
    unfold HandleReadImage at image
    split at image
    · split at image
      · obtain ⟨_, _, _, _, _, same⟩ := image
        unfold handleReadReply at same
        split_ifs at same
        cases same
        rfl
      · obtain ⟨_, same⟩ := image
        cases same
    · exact image.elim
  · rw [sysImage_write] at image
    unfold HandleWriteImage at image
    split at image
    · split at image
      · obtain ⟨_, _, _, same⟩ := image
        unfold handleWriteReply at same
        split_ifs at same
        cases same
        rfl
      · obtain ⟨_, same⟩ := image
        cases same
    · exact image.elim
  · rw [sysImage_prestat] at image
    unfold PrestatImage at image
    split at image
    · obtain ⟨_, same⟩ := image
      unfold prestatReply at same
      split_ifs at same
    · exact image.elim
  · rw [sysImage_dirName] at image
    unfold DirNameImage at image
    split at image
    · obtain ⟨_, named⟩ := image
      unfold DirNameReply at named
      split_ifs at named
      · obtain ⟨_, _, same⟩ := named
        cases same
    · exact image.elim

/-- A run of `Exec` under the shim's host appends images of its WASI events, and a trapped run
traps with `shimTrap` or `exitRejected`. -/
theorem exec_appended {α : Type} {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {replies : Linux.Replies} {action : Action α} {w w' : LinuxWorld} {trace : List Wasi.Event}
    {outcome : Outcome α} (h : Exec (linuxHost F L I replies) action w trace outcome w') :
    Appended F L I replies w w' trace ∧
      ∀ message, outcome = .trapped message →
        message = shimTrap ∨ message = exitRejected := by
  refine Exec.rec
    (motive_1 := fun {α} _ w trace outcome w' _ =>
      Appended F L I replies w w' trace ∧
        ∀ message, outcome = .trapped message → message = shimTrap ∨ message = exitRejected)
    (motive_2 := fun {α σ} _ _ _ _ _ _ w trace outcome w' _ =>
      Appended F L I replies w w' trace ∧
        ∀ message, outcome = .trapped message → message = shimTrap ∨ message = exitRejected)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro α w value
    exact ⟨Appended.refl w, fun _ impossible => by cases impossible⟩
  · intro α capacity next w final trace outcome _ _ ih
    exact ih
  · intro α capacity next w after final trace outcome errno committed _ host _ ih
    exact ⟨(ShimStep.appended host).trans ih.1, ih.2⟩
  · intro α capacity next w after message committed _ host
    refine ⟨ShimStep.appended host, fun cause same => ?_⟩
    cases same
    obtain ⟨_, ⟨e, a, rfl, _, _, _, reply⟩, _⟩ := host
    exact Or.inl (readReply_trapped reply.symm)
  · intro α output bytes next w after final trace outcome errno committed host _ ih
    exact ⟨(ShimStep.appended host).trans ih.1, ih.2⟩
  · intro α output bytes next w after message committed host
    refine ⟨ShimStep.appended host, fun cause same => ?_⟩
    cases same
    obtain ⟨_, ⟨e, a, rfl, _, _, _, _, _, reply⟩, _⟩ := host
    exact Or.inl (writeReply_trapped reply.symm)
  · intro α code w final host
    obtain ⟨_, rfl⟩ := host
    exact ⟨Appended.unchanged rfl rfl, fun _ impossible => by cases impossible⟩
  · intro α code w final message host
    obtain ⟨_, rfl, rfl⟩ := host
    exact ⟨Appended.unchanged rfl rfl, fun cause same => by cases same; exact Or.inr rfl⟩
  · intro σ α count init test step next w final trace outcome _ ih
    exact ih
  · intro α call args next w final trace outcome _ _ ih
    exact ih
  · intro α call args next w after final trace outcome errno committed _ host _ ih
    exact ⟨(ShimStep.appended host).trans ih.1, ih.2⟩
  · intro α call args next w after message committed _ host
    refine ⟨ShimStep.appended host, fun cause same => ?_⟩
    cases same
    obtain ⟨_, ⟨_, image⟩, _⟩ := host
    exact Or.inl (sysImage_trapped image)
  · intro σ α index state test step next w final trace outcome _ ih
    exact ih
  · intro σ α remaining index state test step next w final trace outcome _ _ ih
    exact ih
  · intro σ α remaining index state state' test step next w after final first rest outcome
      _ _ _ ihStep ihRest
    exact ⟨ihStep.1.trans ihRest.1, ihRest.2⟩
  · intro σ α remaining index state test step next w final trace code _ _ ih
    exact ⟨ih.1, fun _ impossible => by cases impossible⟩
  · intro σ α remaining index state test step next w final trace message _ _ ih
    exact ⟨ih.1, fun cause same => by cases same; exact ih.2 _ rfl⟩

/-- A run of `Prefix` under the shim's host appends images of its WASI events. -/
theorem prefix_appended {α : Type} {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {replies : Linux.Replies} {action residual : Action α} {w w' : LinuxWorld}
    {trace : List Wasi.Event}
    (h : Prefix (linuxHost F L I replies) action w trace residual w') :
    Appended F L I replies w w' trace := by
  induction h with
  | refl => exact Appended.refl _
  | read_reject => exact Appended.refl _
  | read_return _ host => exact ShimStep.appended host
  | write_return host => exact ShimStep.appended host
  | loop => exact Appended.refl _
  | bind _ ih => exact ih
  | trans _ _ first rest => exact first.trans rest
  | sys_reject => exact Appended.refl _
  | sys_return _ host => exact ShimStep.appended host

theorem prefix_observed {α World : Type} {host : Host World} {action residual : Action α}
    {initial final : Observed World} {trace : List Wasi.Event}
    (h : Prefix (observedHost host) action initial trace residual final) :
    Prefix host action initial.world trace residual final.world ∧
      final.events = initial.events ++ trace := by
  induction h with
  | refl => exact ⟨.refl _ _, by simp⟩
  | read_reject capacity => exact ⟨.read_reject capacity, by simp⟩
  | read_return capacity reply => exact ⟨.read_return capacity reply.1, reply.2⟩
  | write_return reply => exact ⟨.write_return reply.1, reply.2⟩
  | loop => exact ⟨.loop, by simp⟩
  | bind _ ih => exact ⟨.bind ih.1, ih.2⟩
  | trans _ _ first rest =>
    exact ⟨.trans first.1 rest.1, by rw [rest.2, first.2, List.append_assoc]⟩
  | sys_reject fits => exact ⟨.sys_reject fits, by simp⟩
  | sys_return fits reply => exact ⟨.sys_return fits reply.1, reply.2⟩

/-- The footprint of a result of a run of `_start`, whose action is `action`, from the observed
world `initial` under the shim: the run trapped, with a final world whose layer events extend
those of `initial` by images `ls` of a WASI trace `trace`, which hold the replies from the reply to
call `initial.world.events.length` on and write within the guest's address space or into the
timespec, and with `trace` appended to the observed events.  The trace is that of an accepted exit,
of a rejected exit, or of a trap of the shim, or, when `aborts` holds, a prefix of the action
after which the guest trapped at `unreachable`. -/
def Footprint (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    (action : Action Unit) (initial : Observed LinuxWorld) (aborts : Bool) :
    Result (Observed LinuxWorld) → Prop
  | .Trap final message => ∃ trace ls,
      final.host.world.events = initial.world.events ++ ls ∧
      Images F L I initial.world.events trace ls ∧
      Carried replies initial.world.events.length ls ∧
      (∀ e ∈ ls, WritesWithin L (2 ^ 32) e) ∧
      final.host.events = initial.events ++ trace ∧
      ((∃ code, message = exitTrap ∧ Exec (linuxHost F L I replies) action initial.world trace
          (.exited code) final.host.world) ∨
        (message = exitRejected ∧ Exec (linuxHost F L I replies) action initial.world trace
          (.trapped exitRejected) final.host.world) ∨
        (message = shimTrap ∧ Exec (linuxHost F L I replies) action initial.world trace
          (.trapped shimTrap) final.host.world) ∨
        (aborts = true ∧ message = "unreachable" ∧ ∃ residual,
          Prefix (linuxHost F L I replies) action initial.world trace residual final.host.world))
  | _ => False

/-- The command theorem's classification of a run of `_start` under the shim's host gives the
run's footprint. -/
theorem footprint_of_result (F : OpenFlags) (L : ShimLayout) (I : Launch)
    (replies : Linux.Replies) {native : Action UInt64} {heap : Heap}
    {initial : Store (Observed LinuxWorld)} {aborts : Bool} {result : Result (Observed LinuxWorld)}
    (h : NativeFunctionResult (linuxHost F L I replies) startSignature
      (Action.bind native fun status => Action.exit (α := Unit) status) (fun value : Unit => value)
      .nil [] heap initial aborts result) :
    Footprint F L I replies (Action.bind native fun status => Action.exit status) initial.host
      aborts result := by
  cases h with
  | returned value finalHeap final words trace execution step rep =>
    exact (bind_exit_not_returned (exec_observed execution).1).elim
  | terminal final trace outcome message execution terminal =>
    obtain ⟨run, events⟩ := exec_observed execution
    obtain ⟨⟨ls, grown, images, carried, within⟩, trapped⟩ := exec_appended run
    refine ⟨trace, ls, grown, images, carried, within, events, ?_⟩
    cases outcome with
    | returned value => exact terminal.elim
    | exited code => exact Or.inl ⟨code, terminal, run⟩
    | trapped cause =>
      change message = cause at terminal
      subst terminal
      rcases trapped message rfl with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, run⟩))
      · exact Or.inr (Or.inl ⟨rfl, run⟩)
  | resource final trace residual allowed progress =>
    obtain ⟨run, events⟩ := prefix_observed progress
    obtain ⟨ls, grown, images, carried, within⟩ := prefix_appended run
    exact ⟨trace, ls, grown, images, carried, within, events,
      Or.inr (Or.inr (Or.inr ⟨allowed, rfl, residual, run⟩))⟩

/-- The footprint theorem at the specification level: for every reply sequence, every Talos run
of `_start` of a compiled command whose flat calls the shim implements, under the shim's
environment, with at least the bound's fuel, from a store that meets the command theorem's
premises, has the footprint of `Footprint F L I replies`. -/
theorem shim_footprint (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    {calls : List Call} (supported : ∀ call ∈ calls, call ∈ shimCalls) {pureSigs : List Sig}
    {effectSigs : List EffectSig} {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entries : List (EffectEntry effectSigs))
    (main : EffectMain effectSigs) (pool : Bytes.LiteralPool)
    (effectCalls : CostEffectCallsWith calls source
      (compileCalls calls source program entries (some main) pool) pure program pool)
    {initial : Store (Observed LinuxWorld)} {heap : Heap} {args : Env main.signature.params}
    {budget : Nat} {aborts : Bool} (native : Action UInt64)
    (related : Action.Rel (fun native flat : UInt64 => flat = native) native
      ((program.funs pure.funs).get main.callee args))
    (at_ : heap.At (PureTransport.erase initial))
    (rep : Env.Rep main.signature.mode heap (PureTransport.erase initial)
      (main.tables.map Value.i64) args)
    (separate : Separate (PureTransport.erase initial)
      (Env.moves (PureTransport.erase initial) main.signature.mode (main.tables.map Value.i64)
        args)
      (Env.reads (PureTransport.erase initial) main.signature.mode (main.tables.map Value.i64)
        args))
    (input : @Bytes.LiteralPool.Input (Env main.signature.params)
      (Env.represent main.signature.params main.signature.modes) pool heap
      (PureTransport.erase initial) (main.tables.map Value.i64) args)
    (scratch : ∀ region ∈ Env.reads (PureTransport.erase initial) main.signature.mode
      (main.tables.map Value.i64) args, LeanExe.Runtime.regionsDisjoint ABI.scratch region)
    (cap : (PureTransport.erase initial).memoryCap
      (compileCalls calls source program entries (some main) pool) 0 ≤ 65535)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      Resource.CallPrefixBound (observedHost (linuxHost F L I replies)) pure program main.callee 0
        args initial.host budget) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I replies (Action.bind native fun status => Action.exit status) initial.host
        aborts
        (Wasm.run fuel (compileCalls calls source program entries (some main) pool)
          (Wrappers.effectIndexWith calls source effectSigs.length) initial []
          (linuxEnv F L I replies calls)) := by
  obtain ⟨bound, results⟩ := compiled_native_start_run_with program entries main pool effectCalls
    native related (linuxEnv_satisfies F L I replies calls supported _
      (by rw [compile_imports_with, ABI.importsWith_length])) at_ rep separate input scratch cap
    resources
  exact ⟨bound, fun fuel enough => footprint_of_result F L I replies (results fuel enough)⟩

end Verified.Shim
