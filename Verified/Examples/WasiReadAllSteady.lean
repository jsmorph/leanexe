module

public import Verified.Examples.WasiReadAllMessage
public import Verified.Wasi.BudgetTactics
public import Verified.Wasi.FunctionEntry
public import Verified.FieldsArgs
public import Verified.TailExpand

@[expose] public section

/-!
readAll's message corollary for a class of reply sequences.  `Steady F L I R` holds when `R`
answers every call that a run of `main` and its exit makes under `linuxHost F L I R`: a read with
a result of at most its capacity, and a write of `n` bytes with a result of at most `n` and at
least 1.  A read of a regular file or a pipe returns at most its count, and a write of `n` bytes,
`n` at least 1, to a regular file or to a pipe returns from 1 to `n` unless it reports an error
(read(2), write(2), pipe(7)), so the class holds Linux's replies to a run whose standard input is a
regular file or a pipe and whose standard output is a regular file or a pipe, when no call reports
an error.  It excludes every reply that reports an error, such as `EAGAIN`, `EINTR`, `EIO`,
`ENOSPC`, `EFBIG`, or `EPIPE`, every result outside the request's range, and every write that
returns 0.

`budget_bounded` bounds the resource model's charge of every prefix of `main` under every host by
`budget`, the 1,004,144 bytes that the block of `readAll`'s buffer of 1,004,096 bytes charges.  The
reflector splits the result of `readAll` into its errno and its bytes where `main` binds it, so no
later use copies the input.  `writeAll` charges nothing (`writeAll_bounded`): it computes the
window of the input in words, and each of its passes writes a window of the input, which it
borrows, in place.  The budget fits the 65,535 pages of the module and the 4,096 pages of the
native executable.

`linux_steady` is the corollary for the class: every run of `_start` from the command's initial
store with enough fuel ends at the accepted exit with status `statusOf` of the bytes that the reads
of descriptor 0 returned, and its layer events meet `Copies`.
-/

namespace Verified.Examples.WasiReadAll

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim
  Verified.Wasi.Resource

/-! ## The class of reply sequences -/

/-- The reply `reply` answers the next request of `action`: a read whose result is at most its
capacity, or a write of `n` bytes whose result is at most `n` and at least 1. -/
def Answers (reply : Linux.Reply) : Action α → Prop
  | .read capacity _ => reply.ret.toNat ≤ capacity.toNat
  | .write _ bytes _ => 0 < reply.ret.toNat ∧ reply.ret.toNat ≤ bytes.data.size
  | _ => True

/-- The reply sequences `R` that answer every call that a prefix of `main` and its exit makes under
`linuxHost F L I R` from a world with no layer events, the call after `k` events with `R k`. -/
def Steady (F : OpenFlags) (L : ShimLayout) (I : Launch) (R : Linux.Replies) : Prop :=
  (linuxHost F L I R).Along (fun residual world => Answers (R world.events.length) residual)
    (main.bind fun status => Action.exit (α := Unit) status) linuxStart.world

/-- The host answers the next request of `action` from `world` with errno 0: a read with any bytes,
and a write with a count of at least 1. -/
def SteadyAt {World : Type} (host : Host World) : Action α → World → Prop
  | .read capacity _, world => ∀ {reply after}, host.read world capacity reply after →
      ∃ committed, reply = .returned 0 committed
  | .write output bytes _, world => ∀ {reply after}, host.write world output bytes reply after →
      ∃ count : UInt64, reply = .returned 0 count ∧ 0 < count.toNat
  | _, _ => True

/-- The host answers every request that a prefix of `action` from `world` makes as `SteadyAt`
states. -/
abbrev SteadyAlong {World : Type} (host : Host World) (action : Action α) (world : World) : Prop :=
  host.Along (SteadyAt host) action world

section Along

variable {World : Type} {host : Host World}

theorem SteadyAt.of_bind {action : Action α} {next : α → Action β} {world : World}
    (safe : SteadyAt host (Action.bind action next) world) : SteadyAt host action world := by
  cases action with
  | read => exact safe
  | write => exact safe
  | pure => trivial
  | exit => trivial
  | loop => trivial
  | sys => trivial

/-- The WASI events of a run whose requests the host answers as `SteadyAt` states meet
`Succeeded`. -/
theorem succeeded_of_steady {action : Action α} {world trace outcome final}
    (execution : Exec host action world trace outcome final) :
    SteadyAlong host action world → ∀ e ∈ trace, Succeeded e := by
  refine Exec.rec
    (motive_1 := fun {α} action world trace outcome final _ =>
      SteadyAlong host action world → ∀ e ∈ trace, Succeeded e)
    (motive_2 := fun {α σ} remaining index (state : σ) test step next world trace outcome final _ =>
      SteadyAlong host (resumeLoop test step next remaining index state) world →
        ∀ e ∈ trace, Succeeded e)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ execution
  · intro α world value safe e member
    cases member
  · intro α capacity next world final trace outcome hCapacity run ih safe
    exact ih (safe.after (.read_reject hCapacity))
  · intro α capacity next world after final trace outcome errno committed range hCapacity reply
      size first run ih safe e member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨_, same⟩ := safe _ _ _ (.refl _ _) reply
      cases same
      rfl
    · exact ih (safe.after (.read_return hCapacity reply size first)) e member
  · intro α capacity next world after message committed hCapacity reply safe
    obtain ⟨_, same⟩ := safe _ _ _ (.refl _ _) reply
    cases same
  · intro α output bytes next world after final trace outcome errno committed reply run ih safe e
      member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨count, same, positive⟩ := safe _ _ _ (.refl _ _) reply
      cases same
      refine ⟨rfl, fun zero => ?_⟩
      subst zero
      exact absurd positive (by decide)
    · exact ih (safe.after (.write_return reply)) e member
  · intro α output bytes next world after message committed reply safe
    obtain ⟨_, same, _⟩ := safe _ _ _ (.refl _ _) reply
    cases same
  · intro α code world final accepted safe e member
    rcases List.mem_singleton.mp member with rfl
    trivial
  · intro α code world final message rejected safe e member
    rcases List.mem_singleton.mp member with rfl
    trivial
  · intro σ α count init test step next world final trace outcome run ih safe
    exact ih (safe.after .loop)
  · intro α call args next world final trace outcome hFits run ih safe
    exact ih (safe.after (.sys_reject hFits))
  · intro α call args next world after final trace outcome errno committed hFits reply run ih safe
      e member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · exact ih (safe.after (.sys_return hFits reply)) e member
  · intro α call args next world after message committed hFits reply safe e member
    rcases List.mem_singleton.mp member with rfl
    trivial
  · intro σ α index state test step next world final trace outcome run ih safe
    exact ih safe
  · intro σ α remaining index state test step next world final trace outcome chosen run ih safe
    apply ih
    exact safe.congr (by simp only [resumeLoop, chosen, Bool.false_eq_true, ite_false])
  · intro σ α remaining index state nextState test step next world after final first rest outcome
      chosen stepRun restRun stepIH restIH safe e member
    have current : SteadyAlong host
        (Action.bind (step (UInt64.ofNat index) state)
          (resumeLoop test step next remaining (index + 1))) world :=
      safe.congr (by simp only [resumeLoop, chosen, ite_true])
    rcases List.mem_append.mp member with member | member
    · exact stepIH (current.bind_left SteadyAt.of_bind) e member
    · exact restIH (current.bind_right stepRun) e member
  · intro σ α remaining index state test step next world final trace code chosen stepRun ih safe
    have current : SteadyAlong host
        (Action.bind (step (UInt64.ofNat index) state)
          (resumeLoop test step next remaining (index + 1))) world :=
      safe.congr (by simp only [resumeLoop, chosen, ite_true])
    exact ih (current.bind_left SteadyAt.of_bind)
  · intro σ α remaining index state test step next world final trace message chosen stepRun ih safe
    have current : SteadyAlong host
        (Action.bind (step (UInt64.ofNat index) state)
          (resumeLoop test step next remaining (index + 1))) world :=
      safe.congr (by simp only [resumeLoop, chosen, ite_true])
    exact ih (current.bind_left SteadyAt.of_bind)

end Along

/-- Under `linuxHost`, a reply sequence of the class answers the requests of `main` and its exit as
`SteadyAt` states. -/
theorem Steady.along {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    (steady : Steady F L I R) :
    SteadyAlong (linuxHost F L I R) (main.bind fun status => Action.exit (α := Unit) status)
      linuxStart.world := by
  intro trace residual after progress
  have answers := steady _ _ _ progress
  cases residual with
  | read capacity next =>
    intro reply final step
    obtain ⟨l, ⟨e, a, rfl, _, _, _, rfl⟩, ⟨carries, _⟩, _, _⟩ := step
    change (R after.events.length).ret.toNat ≤ capacity.toNat at answers
    rw [← carries.1] at answers
    refine ⟨bytesOfList (e.output.take e.ret.toNat), ?_⟩
    simp only [Shim.readReply, answers, ↓reduceIte]
  | write output bytes next =>
    intro reply final step
    obtain ⟨l, ⟨e, a, rfl, _, _, _, _, small, rfl⟩, ⟨carries, _⟩, _, _⟩ := step
    obtain ⟨positive, most⟩ := answers
    rw [← carries.1] at positive most
    have wide : (UInt64.ofNat bytes.data.size).toNat = bytes.data.size :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    refine ⟨e.ret, ?_, positive⟩
    simp only [writeReply, wide, most, ↓reduceIte]
  | pure => trivial
  | exit => trivial
  | loop => trivial
  | sys => trivial

/-! ## The budget of `main` -/

/-- The budget of `main`: the 1,004,144 bytes that the block of `readAll`'s buffer of 1,004,096
bytes charges. -/
def budget : Nat := 1004144

/-- `writeAll` charges nothing: it computes the window of its buffer in words, and each of its
passes binds the window of the bytes that remain and writes it from the borrowed buffer. -/
theorem writeAll_bounded {World : Type} {host : Host World} {depth : UInt64}
    (env : Env [Ty.bytes, Ty.word, Ty.word]) :
    Bounded host (.ofProg command.pure.program command.pure.funs) .nil depth
      (entryModes command.writeAll.func.params command.writeAll.func.modes) (fun _ => false)
      command.writeAll.func.body env 0 := by
  rule_bind 0 0
  · rule_ret
  intro _ _
  rule_bind 0 0
  · rule_ret
  intro _ _
  apply bounded_of_rule
  intro _ _ rule
  refine rule 0 (by rule_charge) ?_ ?_
  · simp only [PureContext.loopInitFits, Bool.and_eq_true]
    exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
      Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
  refine LoopBounded.mono (loop_bounded (type := .word) (t := 0) (s := 0)
    (fun _ : UInt64 => True) ?_ ?_ ?_ ?_ _ _ _ trivial) ?_
  · intro index written _
    rule_charge
  · intro index written _
    exact Expr.fits_of_depthCalls _ _ _ (by decide) _
  · intro index written _
    rule_bind 0 0
    · rule_bind 0 0
      · rule_ret
      · intro _ _
        rule_bind 0 0
        · rule_ret
        · intro _ _
          rule_write
    · intro _ _
      rule_ite 0
      · rule_ret
      · rule_ret
  · intro _ _ _ _ _
    trivial
  · simp

/-- Every run and every prefix of `main`'s body charges at most `budget` under every host. -/
theorem body_bounded {World : Type} {host : Host World} :
    Bounded host (.ofProg command.pure.program command.pure.funs)
      (.cons command.writeAll.func .nil) 0 [] (fun _ => false) command.main.func.body .nil
      budget := by
  unfold budget
  rule_bind 1004144 0
  · apply bounded_of_rule
    intro _ _ rule
    exact rule (by decide) (by rule_fits)
  intro _ _
  letPair_free
  rule_ite 0
  · rule_ret
  rule_bind 0 0
  · apply bounded_of_rule
    intro _ _ rule
    exact rule 0 (by rule_charge) rfl (callBounded_here (by decide) (writeAll_bounded _))
  · intro _ _
    rule_ite 0
    · rule_ret
    · rule_ret

/-- Every prefix of a call of `main` under every host charges at most `budget` and has enough
frames. -/
theorem budget_bounded {World : Type} {host : Host World} {world : World} :
    CallPrefixBound host (.ofProg command.pure.program command.pure.funs) command.program .here 0
      .nil world budget := by
  intro trace residual final spent fits progress
  exact call_prefix_rule budget progress rfl (body_bounded.2 world)

/-! ## The corollary for the class -/

/-- A footprint without a guest trap from `linuxStart` under a reply sequence of the class is the
accepted exit with `statusOf` of the bytes that the reads of descriptor 0 returned, and its layer
events meet `Copies`. -/
theorem footprint_steady {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    (steady : Steady F L I R) {result : Result (Observed LinuxWorld)}
    (footprint : Footprint F L I R (main.bind fun status => Action.exit status) linuxStart false
      result) :
    ∃ final, result = .Trap final exitTrap ∧
      final.host.world.exited = some (statusOf (Linux.readData 0 final.host.world.events)) ∧
      Copies final.host.world.events := by
  cases result with
  | Trap final message =>
    obtain ⟨trace, ls, grown, images, _, _, _, classified⟩ := footprint
    change final.host.world.events = [] ++ ls at grown
    rw [List.nil_append] at grown
    have safe : SteadyAlong _ _ _ := steady.along
    rcases classified with ⟨code, rfl, execution⟩ | ⟨_, execution⟩ | ⟨_, execution⟩ |
      ⟨impossible, _⟩
    · obtain ⟨exited, copies⟩ :=
        linux_exec_succeeded execution images (succeeded_of_steady execution safe)
      obtain rfl := Outcome.exited.inj exited
      refine ⟨final, rfl, ?_, by rw [grown]; exact copies⟩
      rw [grown]
      exact execution.exited_marker
    · cases (linux_exec_succeeded execution images (succeeded_of_steady execution safe)).1
    · cases (linux_exec_succeeded execution images (succeeded_of_steady execution safe)).1
    · cases impossible
  | _ => exact footprint.elim

/-- readAll's message corollary for the class.  For all open flags `F`, layouts `L`, launches `I`,
and reply sequences `R` of `Steady F L I R`, which answer every read with a result of at most its
capacity and every write of `n` bytes with a result of at most `n` and at least 1, every Talos run
of `_start` from the command's initial store with enough fuel ends at the accepted exit with status
`statusOf (Linux.readData 0 events)` of its final layer events, 0 when the reads of descriptor 0
returned at most `limit` bytes and 1 otherwise, and the events meet `Copies`.  The module's
docstring states what the class excludes. -/
theorem linux_steady (F : OpenFlags) (L : ShimLayout) (I : Launch) (R : Linux.Replies)
    (steady : Steady F L I R) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel command.module (Wrappers.effectIndex command.pure.module 2) linuxInitial []
          (linuxEnv F L I R []) = .Trap final exitTrap ∧
        final.host.world.exited = some (statusOf (Linux.readData 0 final.host.world.events)) ∧
        Copies final.host.world.events := by
  obtain ⟨bound, footprints⟩ :=
    linux_footprint_bounded F L I R (by unfold budget; omega) budget_bounded
  exact ⟨bound, fun fuel enough => footprint_steady steady (footprints fuel enough)⟩

end Verified.Examples.WasiReadAll

#print axioms Verified.Examples.WasiReadAll.budget_bounded
#print axioms Verified.Examples.WasiReadAll.footprint_steady
#print axioms Verified.Examples.WasiReadAll.linux_steady
