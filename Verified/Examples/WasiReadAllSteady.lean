import Verified.Examples.WasiReadAllMessage
import Verified.Wasi.ResourceRulesAt
import Verified.Wasi.FunctionEntry
import Verified.FieldsArgs
import Verified.TailExpand

/-!
readAll's message corollary for a class of reply sequences.  `Steady F L I M R` holds when `R`
answers every call that a run of `main` and its exit makes under `linuxHost F L I R`: a read with
a result of at most its capacity, and a write of `n` bytes with a result of at most `n`, at least
1, and at least `min M n`.  A read of a regular file or a pipe returns at most its count, and a
write of `n` bytes to a regular file or to a pipe in blocking mode takes all `n` bytes unless an
error or a signal interrupts it (read(2), write(2), pipe(7)), so the class holds Linux's replies
to a run whose standard input is a regular file or a pipe and whose standard output is a regular
file or a blocking pipe, when no call fails or is interrupted.  It also holds a run whose writes
each take at least `M` bytes, or all of them when fewer remain.  It excludes every reply that
reports an error, such as `EAGAIN`, `EINTR`, `EIO`, `ENOSPC`, `EFBIG`, or `EPIPE`, every result
outside the request's range, and every write that takes fewer than `min M n` bytes: a write to a
descriptor in nonblocking mode, which may take from 1 to `n` bytes, a write to a regular file at a
full disk or at `RLIMIT_FSIZE`, and a write that a signal interrupts after some bytes.

`budget_bounded` bounds the resource model's charge of `main` under the replies of the class with
`M` at 4,096 by `budget`, 247 times the 1,004,144 bytes that a block of 1,004,096 bytes charges:
the buffer of `readAll` and the suffix that `writeAll` allocates at each pass.  The reflector
splits the result of `readAll` into its errno and its bytes where `main` binds it, so no later use
copies the input.  Each write of the class takes at least 4,096 bytes or the rest, so `writeAll`
makes at most 246 passes for the at most 1,004,096 bytes that `readAll` returns.  The proof's
bound of one block for each pass needs a minimum of 3,775 bytes at the native cap of 4,096 pages,
and the class takes 4,096.  The charge depends on the replies, so
the bound follows from the worlds that the runs reach (`Verified/Wasi/ResourceRulesAt.lean`), with
the class carried along the run as `SteadyAlong`.  The budget fits the 65,535 pages of the module
and the 4,096 pages of the native executable.

`linux_steady` is the corollary for the class: every run of `_start` from the command's initial
store with enough fuel ends at the accepted exit with status `statusOf` of the bytes that the reads
of descriptor 0 returned, and its layer events meet `Copies`.
-/

namespace Verified.Examples.WasiReadAll

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim
  Verified.Wasi.Resource

/-! ## The class of reply sequences -/

/-- The reply `reply` answers the next request of `action`: a read whose result is at most its
capacity, or a write of `n` bytes whose result is at most `n`, at least 1, and at least
`min M n`. -/
def Answers (M : Nat) (reply : Linux.Reply) : Action α → Prop
  | .read capacity _ => reply.ret.toNat ≤ capacity.toNat
  | .write _ bytes _ => 0 < reply.ret.toNat ∧ min M bytes.data.size ≤ reply.ret.toNat ∧
      reply.ret.toNat ≤ bytes.data.size
  | _ => True

/-- The reply sequences `R` that answer every call that a prefix of `main` and its exit makes under
`linuxHost F L I R` from a world with no layer events, the call after `k` events with `R k`. -/
def Steady (F : OpenFlags) (L : ShimLayout) (I : Launch) (M : Nat) (R : Linux.Replies) : Prop :=
  ∀ {trace residual world},
    Prefix (linuxHost F L I R) (main.bind fun status => Action.exit (α := Unit) status)
      linuxStart.world trace residual world → Answers M (R world.events.length) residual

/-- The host answers the next request of `action` from `world` with errno 0: a read with any bytes,
and a write of `bytes` with a count of at least 1 and at least `min M bytes.data.size`. -/
def SteadyAt {World : Type} (host : Host World) (M : Nat) : Action α → World → Prop
  | .read capacity _, world => ∀ {reply after}, host.read world capacity reply after →
      ∃ committed, reply = .returned 0 committed
  | .write output bytes _, world => ∀ {reply after}, host.write world output bytes reply after →
      ∃ count : UInt64, reply = .returned 0 count ∧ 0 < count.toNat ∧
        min M bytes.data.size ≤ count.toNat
  | _, _ => True

/-- The host answers every request that a prefix of `action` from `world` makes as `SteadyAt`
states. -/
def SteadyAlong {World : Type} (host : Host World) (M : Nat) (action : Action α) (world : World) :
    Prop :=
  ∀ trace residual after, Prefix host action world trace residual after →
    SteadyAt host M residual after

section Along

variable {World : Type} {host : Host World} {M : Nat}

theorem SteadyAlong.after {action residual : Action α} {world trace after : _}
    (safe : SteadyAlong host M action world)
    (progress : Prefix host action world trace residual after) :
    SteadyAlong host M residual after :=
  fun _ _ _ tail => safe _ _ _ (progress.trans tail)

theorem SteadyAlong.congr {action other : Action α} {world : World}
    (safe : SteadyAlong host M action world) (same : action = other) :
    SteadyAlong host M other world :=
  same ▸ safe

theorem SteadyAt.of_bind {action : Action α} {next : α → Action β} {world : World}
    (safe : SteadyAt host M (Action.bind action next) world) : SteadyAt host M action world := by
  cases action with
  | read => exact safe
  | write => exact safe
  | pure => trivial
  | exit => trivial
  | loop => trivial
  | sys => trivial

theorem SteadyAlong.bind_left {action : Action α} {next : α → Action β} {world : World}
    (safe : SteadyAlong host M (Action.bind action next) world) :
    SteadyAlong host M action world :=
  fun _ _ _ progress => (safe _ _ _ progress.bind).of_bind

theorem SteadyAlong.bind_right {action : Action α} {next : α → Action β}
    {world first value after : _}
    (safe : SteadyAlong host M (Action.bind action next) world)
    (execution : Exec host action world first (.returned value) after) :
    SteadyAlong host M (next value) after :=
  fun _ _ _ progress => safe _ _ _ (Prefix.bind_after execution progress)

theorem SteadyAt.rel {relation : α → β → Prop} {left : Action α} {right : Action β}
    {world : World} (related : Action.Rel relation left right) (safe : SteadyAt host M left world) :
    SteadyAt host M right world := by
  cases related with
  | read => exact safe
  | write => exact safe
  | pure => trivial
  | exit => trivial
  | loop => trivial
  | sys => trivial

/-- The class carries from an action to a related one, such as the flat action of a compiled
function. -/
theorem SteadyAlong.rel {relation : α → β → Prop} {left : Action α} {right : Action β}
    {world : World} (related : Action.Rel relation left right)
    (safe : SteadyAlong host M left world) : SteadyAlong host M right world := by
  intro trace residual after progress
  obtain ⟨source, progress, related⟩ := related.transportPrefixBack progress
  exact (safe _ _ _ progress).rel related

theorem SteadyAt.observed {action : Action α} {world : Observed World}
    (safe : SteadyAt host M action world.world) : SteadyAt (observedHost host) M action world := by
  cases action with
  | read => exact fun step => safe step.1
  | write => exact fun step => safe step.1
  | pure => trivial
  | exit => trivial
  | loop => trivial
  | sys => trivial

theorem SteadyAlong.observed {action : Action α} {world : Observed World}
    (safe : SteadyAlong host M action world.world) :
    SteadyAlong (observedHost host) M action world :=
  fun _ _ _ progress => (safe _ _ _ (prefix_observed progress).1).observed

/-- The WASI events of a run whose requests the host answers as `SteadyAt` states meet
`Succeeded`. -/
theorem succeeded_of_steady {action : Action α} {world trace outcome final}
    (execution : Exec host action world trace outcome final) :
    SteadyAlong host M action world → ∀ e ∈ trace, Succeeded e := by
  refine Exec.rec
    (motive_1 := fun {α} action world trace outcome final _ =>
      SteadyAlong host M action world → ∀ e ∈ trace, Succeeded e)
    (motive_2 := fun {α σ} remaining index (state : σ) test step next world trace outcome final _ =>
      SteadyAlong host M (resumeLoop test step next remaining index state) world →
        ∀ e ∈ trace, Succeeded e)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ execution
  · intro α world value safe e member
    cases member
  · intro α capacity next world final trace outcome hCapacity run ih safe
    exact ih (safe.after (.read_reject hCapacity))
  · intro α capacity next world after final trace outcome errno committed hCapacity reply run ih
      safe e member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨_, same⟩ := safe _ _ _ (.refl _ _) reply
      cases same
      rfl
    · exact ih (safe.after (.read_return hCapacity reply)) e member
  · intro α capacity next world after message committed hCapacity reply safe
    obtain ⟨_, same⟩ := safe _ _ _ (.refl _ _) reply
    cases same
  · intro α output bytes next world after final trace outcome errno committed reply run ih safe e
      member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨count, same, positive, _⟩ := safe _ _ _ (.refl _ _) reply
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
    have current : SteadyAlong host M
        (Action.bind (step (UInt64.ofNat index) state)
          (resumeLoop test step next remaining (index + 1))) world :=
      safe.congr (by simp only [resumeLoop, chosen, ite_true])
    rcases List.mem_append.mp member with member | member
    · exact stepIH current.bind_left e member
    · exact restIH (current.bind_right stepRun) e member
  · intro σ α remaining index state test step next world final trace code chosen stepRun ih safe
    have current : SteadyAlong host M
        (Action.bind (step (UInt64.ofNat index) state)
          (resumeLoop test step next remaining (index + 1))) world :=
      safe.congr (by simp only [resumeLoop, chosen, ite_true])
    exact ih current.bind_left
  · intro σ α remaining index state test step next world final trace message chosen stepRun ih safe
    have current : SteadyAlong host M
        (Action.bind (step (UInt64.ofNat index) state)
          (resumeLoop test step next remaining (index + 1))) world :=
      safe.congr (by simp only [resumeLoop, chosen, ite_true])
    exact ih current.bind_left

/-! The class along the commands of a reflected effect function. -/

section Commands

variable {pureFuns : Funs pureSigs} {effectFuns : EffectFuns effectSigs}

theorem SteadyAlong.bind_first {first : Command pureSigs effectSigs context intermediate}
    {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
    {world : World}
    (safe : SteadyAlong host M ((Command.bind first next).denote pureFuns effectFuns env) world) :
    SteadyAlong host M (first.denote pureFuns effectFuns env) world :=
  SteadyAlong.bind_left
    (next := fun value => next.denote pureFuns effectFuns (intermediate.bindEnv value env)) safe

theorem SteadyAlong.bind_next {first : Command pureSigs effectSigs context intermediate}
    {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
    {world after : World} {trace : List Wasi.Event} {value : intermediate.denote}
    (safe : SteadyAlong host M ((Command.bind first next).denote pureFuns effectFuns env) world)
    (run : Exec host (first.denote pureFuns effectFuns env) world trace (.returned value) after) :
    SteadyAlong host M (next.denote pureFuns effectFuns (intermediate.bindEnv value env)) after :=
  SteadyAlong.bind_right
    (next := fun value => next.denote pureFuns effectFuns (intermediate.bindEnv value env)) safe run

theorem SteadyAlong.ite_no {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result} {env : Env context} {world : World}
    (safe : SteadyAlong host M ((Command.ite condition yes no).denote pureFuns effectFuns env)
      world)
    (chosen : condition.denote pureFuns env = false) :
    SteadyAlong host M (no.denote pureFuns effectFuns env) world :=
  safe.congr (by rw [Command.denote, chosen]; rfl)

theorem SteadyAlong.call_here {function : EffectFunc pureSigs effectSigs}
    {rest : EffectProg pureSigs effectSigs}
    {args : (i : Fin function.sig.params.length) →
      Expr pureSigs context (function.sig.params.get i)}
    {env : Env context} {world : World}
    (safe : SteadyAlong host M ((Command.call .here args).denote pureFuns
      ((EffectProg.cons function rest).funs pureFuns) env) world) :
    SteadyAlong host M (function.body.denote pureFuns (rest.funs pureFuns)
      (Env.ofFn fun i => (args i).denote pureFuns env)) world :=
  safe

theorem SteadyAlong.loop_command {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {count : Expr pureSigs context .word}
    {initial : Expr pureSigs context type} {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {env : Env context} {world : World}
    (safe : SteadyAlong host M ((Command.loop count initial test step).denote pure.funs
      (program.funs pure.funs) env) world) :
    SteadyAlong host M (loopResume pure program test step env (count.denote pure.funs env).toNat 0
      (initial.denote pure.funs env)) world :=
  safe.after Prefix.loop

end Commands

end Along

/-- Under `linuxHost`, a reply sequence of the class answers the requests of `main` and its exit as
`SteadyAt` states. -/
theorem Steady.along {F : OpenFlags} {L : ShimLayout} {I : Launch} {M : Nat} {R : Linux.Replies}
    (steady : Steady F L I M R) :
    SteadyAlong (linuxHost F L I R) M (main.bind fun status => Action.exit (α := Unit) status)
      linuxStart.world := by
  intro trace residual after progress
  have answers := steady progress
  cases residual with
  | read capacity next =>
    intro reply final step
    obtain ⟨l, ⟨e, a, rfl, _, _, _, rfl⟩, ⟨carries, _⟩, _, _⟩ := step
    change (R after.events.length).ret.toNat ≤ capacity.toNat at answers
    rw [← carries.1] at answers
    refine ⟨bytesOfList (e.output.take e.ret.toNat), ?_⟩
    simp only [readReply, answers, ↓reduceIte]
  | write output bytes next =>
    intro reply final step
    obtain ⟨l, ⟨e, a, rfl, _, _, _, _, small, rfl⟩, ⟨carries, _⟩, _, _⟩ := step
    obtain ⟨positive, least, most⟩ := answers
    rw [← carries.1] at positive least most
    have wide : (UInt64.ofNat bytes.data.size).toNat = bytes.data.size :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    refine ⟨e.ret, ?_, positive, least⟩
    simp only [writeReply, wide, most, ↓reduceIte]
  | pure => trivial
  | exit => trivial
  | loop => trivial
  | sys => trivial

/-! ## The charge of `writeAll`'s loop -/

/-- A bound on the charge of `writeAll`'s passes over `m` bytes not yet written when each write
takes at least 4,096 bytes or the rest: a block of at most 1,004,144 bytes for each pass. -/
def passesCharge (m : Nat) : Nat := (m + 4095) / 4096 * 1004144

/-- The facts about a loop's test and step that bound the charge of the loop of `writeAll bytes`,
of at most 1,004,096 bytes: the test continues while `written` lies below the size of `bytes` and
charges nothing, and each pass writes `suffix written`, as many bytes as remain from `written` on,
continues with `written` plus the count written, and charges at most 1,004,144 bytes. -/
structure WriteLoop {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) (test : Expr pureSigs (.word :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (.word :: .word :: context) (.value .word))
    (env : Env context) (bytes : Bytes) (suffix : UInt64 → Bytes) : Prop where
  small : bytes.data.size ≤ 1004096
  tested : ∀ index written,
    test.denote pure.funs (loopEnv env index written) = decide (written < bytes.size)
  testCost : ∀ index written, pure.loopTestCost depth modes live test step env index written = 0
  testFits : ∀ index written, pure.loopTestFits depth test env index written = true
  stepped : ∀ index written, ∃ next,
    step.denote pure.funs (program.funs pure.funs) (loopEnv env index written) =
      .write .stdout (suffix written) next ∧
      ∀ count, next (writeResult 0 count) = .pure (written + count)
  sized : ∀ written : UInt64, written.toNat ≤ bytes.data.size →
    (suffix written).data.size = bytes.data.size - written.toNat
  stepBounded : ∀ index (written : UInt64), written.toNat ≤ bytes.data.size →
    Bounded host pure program depth (loopModes .owned modes) (shift 2 (loopLive test step live))
      step (loopEnv env index written) 1004144

theorem loopResume_continue {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {env : Env context} {remaining index : Nat} {state : type.denote}
    (chosen : test.denote pure.funs (loopEnv env index state) = true) :
    loopResume pure program test step env (remaining + 1) index state =
      Action.bind (step.denote pure.funs (program.funs pure.funs) (loopEnv env index state))
        (loopResume pure program test step env remaining (index + 1)) := by
  change (if test.denote pure.funs (loopEnv env index state) then _ else _) = _
  rw [chosen]
  rfl

section Loop

variable {World : Type} {host : Host World} {pure : PureContext pureSigs}
  {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
  {live : Nat → Bool} {test : Expr pureSigs (.word :: .word :: context) .bool}
  {step : Command pureSigs effectSigs (.word :: .word :: context) (.value .word)}
  {env : Env context} {bytes : Bytes} {suffix : UInt64 → Bytes}

theorem WriteLoop.wide
    (loop : WriteLoop host pure program depth modes live test step env bytes suffix) :
    bytes.size.toNat = bytes.data.size := by
  have small := loop.small
  simp only [Bytes.size, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- A pass that the test admits has bytes left to write. -/
theorem WriteLoop.remains
    (loop : WriteLoop host pure program depth modes live test step env bytes suffix)
    {index : Nat} {written : UInt64}
    (chosen : test.denote pure.funs (loopEnv env index written) = true) :
    written.toNat < bytes.data.size := by
  rw [loop.tested, decide_eq_true_iff, UInt64.lt_iff_toNat_lt, loop.wide] at chosen
  exact chosen

/-- A pass whose write the host answers as `SteadyAt` states continues with `written` plus a count
of at least 1, at least the lesser of 4,096 and the bytes that remain, and at most those bytes. -/
theorem WriteLoop.advance
    (loop : WriteLoop host pure program depth modes live test step env bytes suffix)
    {index : Nat} {written : UInt64} {world after : World} {trace : List Wasi.Event}
    {nextState : UInt64} (le : written.toNat ≤ bytes.data.size)
    (safe : SteadyAlong host 4096
      (step.denote pure.funs (program.funs pure.funs) (loopEnv env index written)) world)
    (run : Exec host (step.denote pure.funs (program.funs pure.funs) (loopEnv env index written))
      world trace (.returned nextState) after) :
    ∃ count : UInt64, nextState = written + count ∧ 0 < count.toNat ∧
      min 4096 (bytes.data.size - written.toNat) ≤ count.toNat ∧
      count.toNat ≤ bytes.data.size - written.toNat := by
  obtain ⟨next, same, continues⟩ := loop.stepped index written
  rw [same] at safe run
  cases run with
  | write_return reply rest =>
    obtain ⟨count, returned, positive, least⟩ := safe _ _ _ (.refl _ _) reply
    cases returned
    have bound := (host.write_bound reply).1
    simp only [Transfer.committed] at bound
    rw [loop.sized written le] at bound least
    rw [continues] at rest
    cases rest
    exact ⟨_, rfl, positive, least, bound⟩

theorem WriteLoop.exec_bound
    (loop : WriteLoop host pure program depth modes live test step env bytes suffix) :
    ∀ (remaining index : Nat) (written : UInt64) {world : World} {trace : List Wasi.Event}
      {outcome : Outcome UInt64} {final : World} {spent : Nat} {fits : Bool},
      written.toNat ≤ bytes.data.size →
      SteadyAlong host 4096 (loopResume pure program test step env remaining index written)
        world →
      ResourceLoopExec host pure program depth modes live test step env remaining index written
        world trace outcome final spent fits →
      spent ≤ passesCharge (bytes.data.size - written.toNat) ∧ fits = true
  | 0, _, _, _, _, _, _, _, _, _, _, execution => by
    cases execution
    exact ⟨Nat.zero_le _, rfl⟩
  | remaining + 1, index, written, world, _, _, _, _, _, le, safe, execution => by
    cases execution with
    | stop chosen =>
      rw [loop.testCost]
      exact ⟨Nat.zero_le _, loop.testFits _ _⟩
    | next chosen stepRun restRun =>
      have remains := loop.remains chosen
      have current : SteadyAlong host 4096
          (Action.bind (step.denote pure.funs (program.funs pure.funs) (loopEnv env index written))
            (loopResume pure program test step env remaining (index + 1))) world :=
        safe.congr (loopResume_continue chosen)
      obtain ⟨count, rfl, positive, least, most⟩ :=
        loop.advance le current.bind_left stepRun.erase
      have sum : (written + count).toNat = written.toNat + count.toNat := by
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by have := loop.small; omega)]
      obtain ⟨stepCost, stepFits⟩ := (loop.stepBounded index written le).1 _ _ _ _ _ _ stepRun
      obtain ⟨restCost, restFits⟩ := loop.exec_bound remaining (index + 1) (written + count)
        (by omega) (current.bind_right stepRun.erase) restRun
      rw [sum] at restCost
      rw [loop.testCost, loop.testFits, stepFits, restFits]
      refine ⟨?_, rfl⟩
      unfold passesCharge at restCost ⊢
      omega
    | exit chosen stepRun =>
      have remains := loop.remains chosen
      obtain ⟨stepCost, stepFits⟩ := (loop.stepBounded index written le).1 _ _ _ _ _ _ stepRun
      rw [loop.testCost, loop.testFits, stepFits]
      refine ⟨?_, rfl⟩
      unfold passesCharge
      omega
    | trap chosen stepRun =>
      have remains := loop.remains chosen
      obtain ⟨stepCost, stepFits⟩ := (loop.stepBounded index written le).1 _ _ _ _ _ _ stepRun
      rw [loop.testCost, loop.testFits, stepFits]
      refine ⟨?_, rfl⟩
      unfold passesCharge
      omega

theorem WriteLoop.prefix_bound
    (loop : WriteLoop host pure program depth modes live test step env bytes suffix) :
    ∀ (remaining index : Nat) (written : UInt64) {world : World} {trace : List Wasi.Event}
      {residual : Action UInt64} {final : World} {spent : Nat} {fits : Bool},
      written.toNat ≤ bytes.data.size →
      SteadyAlong host 4096 (loopResume pure program test step env remaining index written)
        world →
      ResourceLoopPrefix host pure program depth modes live test step env remaining index written
        world trace residual final spent fits →
      spent ≤ passesCharge (bytes.data.size - written.toNat) ∧ fits = true
  | 0, index, written, _, _, _, _, _, _, le, safe, progress => by
    cases progress with
    | refl => exact ⟨Nat.zero_le _, rfl⟩
    | returned execution => exact loop.exec_bound 0 index written le safe execution
  | remaining + 1, index, written, world, _, _, _, _, _, le, safe, progress => by
    cases progress with
    | refl => exact ⟨Nat.zero_le _, rfl⟩
    | test_charge =>
      rw [loop.testCost]
      exact ⟨Nat.zero_le _, loop.testFits _ _⟩
    | returned execution => exact loop.exec_bound _ index written le safe execution
    | step chosen progress =>
      have remains := loop.remains chosen
      obtain ⟨stepCost, stepFits⟩ := (loop.stepBounded index written le).2 _ _ _ _ _ _ progress
      rw [loop.testCost, loop.testFits, stepFits]
      refine ⟨?_, rfl⟩
      unfold passesCharge
      omega
    | next chosen stepRun progress =>
      have remains := loop.remains chosen
      have current : SteadyAlong host 4096
          (Action.bind (step.denote pure.funs (program.funs pure.funs) (loopEnv env index written))
            (loopResume pure program test step env remaining (index + 1))) world :=
        safe.congr (loopResume_continue chosen)
      obtain ⟨count, rfl, positive, least, most⟩ :=
        loop.advance le current.bind_left stepRun.erase
      have sum : (written + count).toNat = written.toNat + count.toNat := by
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by have := loop.small; omega)]
      obtain ⟨stepCost, stepFits⟩ := (loop.stepBounded index written le).1 _ _ _ _ _ _ stepRun
      obtain ⟨restCost, restFits⟩ := loop.prefix_bound remaining (index + 1) (written + count)
        (by omega) (current.bind_right stepRun.erase) progress
      rw [sum] at restCost
      rw [loop.testCost, loop.testFits, stepFits, restFits]
      refine ⟨?_, rfl⟩
      unfold passesCharge at restCost ⊢
      omega

/-- Every run and every prefix of the loop of `writeAll bytes` from `written` bytes written, from a
world from which the host answers its requests as `SteadyAt` states with `M` at 4,096, charges at
most `passesCharge` of the bytes that remain and has enough frames. -/
theorem WriteLoop.bounded
    (loop : WriteLoop host pure program depth modes live test step env bytes suffix)
    {remaining index : Nat} {written : UInt64} {world : World}
    (le : written.toNat ≤ bytes.data.size)
    (safe : SteadyAlong host 4096 (loopResume pure program test step env remaining index written)
      world) :
    LoopBoundedAt host pure program depth modes live test step env remaining index written world
      (passesCharge (bytes.data.size - written.toNat)) :=
  ⟨fun _ _ _ _ _ execution => loop.exec_bound remaining index written le safe execution,
    fun _ _ _ _ _ progress => loop.prefix_bound remaining index written le safe progress⟩

end Loop

/-! ## The budget of `main` -/

/-- The budget of `main` under the class with `M` at 4,096: 247 times the 1,004,144 bytes that a
block of 1,004,096 bytes charges, for `readAll`'s buffer and at most 246 suffixes. -/
def budget : Nat := 247 * 1004144

open Lean Meta in
/-- The value at `index` of an environment given as a chain of `Env.cons`. -/
private partial def envValueAt (env : Lean.Expr) (index : Nat) : MetaM (Option Lean.Expr) := do
  match (← whnfD env).getAppFnArgs with
  | (``Env.cons, #[_, _, value, rest]) =>
    if index == 0 then return some value else envValueAt rest (index - 1)
  | _ => return none

open Lean Meta Simp in
/-- Reads `Env.get env (Var.ofIndex Γ i h)` as the `i`-th value of `env` when `env` is a chain of
`Env.cons`, a definitional step, as `Verified.Examples.WasiSys.envGet` does. -/
dsimproc_decl envGet (Env.get _ (Var.ofIndex _ _ _)) := fun e => do
  let (``Env.get, #[_, _, env, reference]) := e.getAppFnArgs | return .continue
  let (``Var.ofIndex, #[_, _, index, _]) := reference.getAppFnArgs | return .continue
  let some index := index.rawNatLit? <|> index.nat? | return .continue
  let some value ← envValueAt env index | return .continue
  return .done value

/-- The cost of an `if` whose branches have one budget. -/
private theorem ite_cost {c : Prop} {decision : Decidable c} {cost branch total : Nat}
    (bound : cost + branch ≤ total) : cost + @ite Nat c decision branch branch ≤ total := by
  cases decision <;> exact bound

/-- The charge of a call of `suffix`: the block of the bytes from `start` on. -/
private theorem suffix_charge (depth : UInt64) (bytes : Bytes) (start : UInt64) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds depth).get FVar.here
      (Env.cons bytes (Env.cons start Env.nil)) = Bytes.allocationCost (bytes.size - start).toNat :=
  (command.pureSources.suffix.bound_eq bytes start).trans rfl

/-- A call of `suffix` on at most 1,004,096 bytes from a start within them charges at most
1,004,144 bytes. -/
private theorem suffix_call_le (depth : UInt64) (env : Env [Ty.bytes, Ty.word]) (bytes : Bytes)
    (start : UInt64) (same : env = .cons bytes (.cons start .nil))
    (small : bytes.data.size ≤ 1004096) (le : start.toNat ≤ bytes.data.size) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds depth).get FVar.here
      env ≤ 1004144 := by
  subst same
  rw [suffix_charge, suffix_count (by omega) le]
  exact (allocationCost_mono (show bytes.data.size - start.toNat ≤ 1004096 by omega)).trans
    (by decide)

/-- Proves a bound on the charge of an expression: evaluates its liveness tests, reads its
variables, and leaves the copies to `omega`. -/
local macro "charge" : tactic => `(tactic|
  (simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.readAllCost,
      PureContext.argumentCost, PureContext.loopInitCost, PureContext.loopCountCost,
      PureContext.loopTestCost, Expr.allocs, Var.cost, Var.ownedCost, Expr.ownedCost, Expr.mode,
      coerceCost, Ty.copyCost, envGet, Expr.denote, Args.get_cons_zero', argsSum, callCredits,
      suffix_charge, ResultTy.bindEnv, letPairEnv, letPairModes, modeAt, Nat.add_zero,
      Nat.zero_add, ↓reduceIte, ite_self] <;>
   omega))

/-- Proves the frames of an expression that calls no function that takes the call depth. -/
local macro "fits" : tactic => `(tactic| exact Expr.fits_of_depthCalls _ _ _ (by decide) _)

/-- Proves `Bounded` of a `ret`. -/
local macro "ret_bound" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule (by charge) (by fits)))

/-- Every prefix of a call of `main` from a world from which the host answers the requests of
`main` as `SteadyAt` states with `M` at 4,096 charges at most `budget` and has enough frames. -/
theorem budget_bounded {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world : Observed LinuxWorld}
    (safe : SteadyAlong (observedHost (linuxHost F L I R)) 4096
      (command.main.func.body.denote command.pure.funs
        ((EffectProg.cons command.writeAll.func EffectProg.nil).funs command.pure.funs) .nil)
      world) :
    CallPrefixBound (observedHost (linuxHost F L I R))
      (.ofProg command.pure.program command.pure.funs) command.program .here 0 .nil world
      budget := by
  intro trace residual final spent fits progress
  refine call_prefix_rule_at budget progress rfl ?_
  apply boundedAt_of_rule
  intro _ _ rule
  refine rule 1004144 (246 * 1004144) (by decide) ?_ ?_
  · apply Bounded.at
    apply bounded_of_rule
    intro _ _ rule
    exact rule (by decide) (by fits)
  intro _ input after _ _ readRun
  have size : input.2.data.size ≤ 1004096 := Returns.readAll_size ⟨_, _, _, _, _, readRun⟩
  have afterRead : SteadyAlong _ _ _ _ := SteadyAlong.bind_next safe readRun.erase
  letPairAt_free
  apply boundedAt_of_rule
  intro _ _ rule
  refine rule (246 * 1004144) (246 * 1004144) (ite_cost (by charge)) (by fits) (fun _ => ?_)
    (fun no => ?_)
  · apply Bounded.at
    ret_bound
  have afterTest : SteadyAlong _ _ _ _ := SteadyAlong.ite_no afterRead no
  apply boundedAt_of_rule
  intro _ _ rule
  refine rule (246 * 1004144) 0 (by omega) ?_ ?_
  · have atLoop : SteadyAlong _ _ _ _ :=
      SteadyAlong.loop_command (pure := .ofProg command.pure.program command.pure.funs)
        (SteadyAlong.call_here (SteadyAlong.bind_first afterTest))
    apply boundedAt_of_rule
    intro _ _ rule
    refine rule (246 * 1004144) (by charge) rfl (callBoundedAt_here (by decide) ?_)
    apply boundedAt_of_rule
    intro _ _ rule
    refine rule _ ?_ ?_ (WriteLoop.bounded (bytes := input.2)
      (suffix := fun written => command.pureSources.suffix.func.denote Funs.nil
        (Env.cons input.2 (Env.cons written Env.nil))) ?_ (Nat.zero_le _) atLoop)
    · simp only [passesCharge]
      charge
    · simp only [PureContext.loopInitFits, Bool.and_eq_true]
      exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
        Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
    refine ⟨size, fun _ _ => rfl, fun _ _ => by charge, fun _ _ => by fits,
      fun _ _ => ⟨_, rfl, fun _ => rfl⟩, fun written le => ?_, fun _ written le => ?_⟩
    · rw [command.pureSources.suffix.denote_eq]
      have := congrArg List.length (suffix_toList (by omega) le)
      simpa using this
    apply bounded_of_rule
    intro _ _ rule
    refine rule 1004144 0 (by omega) ?_ (fun _ _ => ?_)
    · apply bounded_of_rule
      intro _ _ rule
      refine rule 1004144 0 (by omega) ?_ (fun _ _ => ?_)
      · apply bounded_of_rule
        intro _ _ rule
        refine rule ?_ (by fits)
        simp +decide only [PureContext.ownedCost, PureContext.exprCost, Expr.allocs, Var.cost,
          coerceCost, Args.get_cons_zero', Args.get_cons_succ, argsSum, callCredits, Nat.add_zero,
          Nat.zero_add, ↓reduceIte]
        rw [Ty.copyCost_of_scalar _ _ (by decide), Nat.zero_add]
        exact suffix_call_le _ _ input.2 written rfl size le
      · apply bounded_of_rule
        intro _ _ rule
        exact rule
    · apply bounded_of_rule
      intro _ _ rule
      refine rule 0 0 (ite_cost (by charge)) (by fits) (fun _ => ?_) (fun _ => ?_)
      · apply bounded_of_rule
        intro _ _ rule
        exact rule (by charge) (by fits)
      · ret_bound
  · intro _ _ _ _ _ _
    apply Bounded.at
    apply bounded_of_rule
    intro _ _ rule
    refine rule 0 0 (ite_cost (by charge)) (by fits) (fun _ => ?_) (fun _ => ?_)
    · ret_bound
    · ret_bound

/-- Under a reply sequence of the class with `M` at 4,096, every prefix of a call of `main` from an
observed world whose host world is that of `linuxStart`, with no layer events, no exit marker, and
no recorded outputs, charges at most `budget` and has enough frames. -/
theorem steady_bounded {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    (steady : Steady F L I 4096 R) {world : Observed LinuxWorld}
    (start : world.world = linuxStart.world) :
    CallPrefixBound (observedHost (linuxHost F L I R))
      (.ofProg command.pure.program command.pure.funs) command.program .here 0 .nil world
      budget := by
  have safe : SteadyAlong _ _ _ _ := steady.along.bind_left.rel command.main.related
  rw [← start] at safe
  exact budget_bounded safe.observed

/-! ## The corollary for the class -/

/-- A footprint without a guest trap from `linuxStart` under a reply sequence of the class is the
accepted exit with `statusOf` of the bytes that the reads of descriptor 0 returned, and its layer
events meet `Copies`. -/
theorem footprint_steady {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    (steady : Steady F L I 4096 R) {result : Result (Observed LinuxWorld)}
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
    have safe : SteadyAlong _ _ _ _ := steady.along
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
and reply sequences `R` of `Steady F L I 4096 R`, which answer every read with a result of at most
its capacity and every write of `n` bytes with a result of at most `n`, at least 1, and at least
`min 4096 n`, every Talos run of `_start` from the command's initial store with enough fuel ends at
the accepted exit with status `statusOf (Linux.readData 0 events)` of its final layer events, 0
when the reads of descriptor 0 returned at most `limit` bytes and 1 otherwise, and the events meet
`Copies`.  The module's docstring states what the class excludes. -/
theorem linux_steady (F : OpenFlags) (L : ShimLayout) (I : Launch) (R : Linux.Replies)
    (steady : Steady F L I 4096 R) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel command.module (Wrappers.effectIndex command.pure.module 2) linuxInitial []
          (linuxEnv F L I R []) = .Trap final exitTrap ∧
        final.host.world.exited = some (statusOf (Linux.readData 0 final.host.world.events)) ∧
        Copies final.host.world.events := by
  obtain ⟨bound, footprints⟩ :=
    linux_footprint_bounded F L I R (by unfold budget; omega) (steady_bounded steady rfl)
  exact ⟨bound, fun fuel enough => footprint_steady steady (footprints fuel enough)⟩

end Verified.Examples.WasiReadAll

#print axioms Verified.Examples.WasiReadAll.budget_bounded
#print axioms Verified.Examples.WasiReadAll.footprint_steady
#print axioms Verified.Examples.WasiReadAll.linux_steady
