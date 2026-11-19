import Verified.Wasi.ResourceNativePrefix
import LeanExe.Wasi.WriteAll

/-! Runs that stop before they end.  `Stops host action world trace` states that `trace` holds the
events of a prefix of a run of `action` from `world`, which describes a compiled run that a trap of
the guest cuts short, or of a run that traps in the host or at an exit that the host rejects.
`Stops.pure`, `Stops.exit`, `Stops.read`, `Stops.write`, `Stops.sys`, `Stops.loop`, and
`Stops.bind` take such a run apart at the first step of its action: a run of
`Action.bind first next` that stops is a run of `first` that stops, or a run of `first` that
returns a value followed by a run of `next` on that value that stops.  `prefix_uncons` takes a
prefix apart at its first step, and `prefix_unbind` gives the prefixes of `Action.bind`.

`Every ok action` states that `ok` holds of every event that the action makes in a run that stops:
of each read, write, and call for every reply, and of each exit that the host rejects.
`Every.stops` gives `ok` of every event of such a run.  `writeAll_stops` gives the events of a run
of `writeAll` that stops: writes to standard output, each of which offered at least one byte, the
bytes of the window after those that the writes before it took, followed by at most one exit that
the host rejected. -/

namespace Verified.Wasi

open LeanExe LeanExe.Wasi

/-! ## Prefixes -/

/-- A prefix of a run takes no step, or a first step followed by a prefix of a run of the action
that the step leaves. -/
theorem prefix_uncons {World : Type} {host : Host World} {action residual : Action α}
    {world trace after} (progress : PrefixProgress host action world trace residual after) :
    (residual = action ∧ trace = [] ∧ after = world) ∨
      ∃ first rest middle between, PrefixAdvance host action world first middle between ∧
        PrefixProgress host middle between rest residual after ∧ trace = first ++ rest := by
  induction progress with
  | refl => exact .inl ⟨rfl, rfl, rfl⟩
  | advance step => exact .inr ⟨_, [], _, _, step, .refl _ _, (List.append_nil _).symm⟩
  | trans _ tail ihHead ihTail =>
    rcases ihHead with ⟨rfl, rfl, rfl⟩ | ⟨first, rest, middle, between, step, progress, rfl⟩
    · rcases ihTail with ⟨rfl, rfl, rfl⟩ | ⟨first, rest, middle, between, step, progress, rfl⟩
      · exact .inl ⟨rfl, rfl, rfl⟩
      · exact .inr ⟨first, rest, middle, between, step, progress, rfl⟩
    · exact .inr ⟨first, _, middle, between, step, progress.trans tail, List.append_assoc ..⟩

/-- A prefix of a run of `Action.bind first next` is a prefix of a run of `first` whose residual
continues with `next`, or a run of `first` that returns a value followed by a prefix of a run of
`next` on that value. -/
theorem prefix_unbind {World : Type} {host : Host World} {action residual : Action β}
    {world trace after} (progress : PrefixProgress host action world trace residual after) :
    ∀ {α : Type} (first : Action α) (next : α → Action β), action = Action.bind first next →
      (∃ middle, Prefix host first world trace middle after ∧
          residual = Action.bind middle next) ∨
        ∃ value done rest between, trace = done ++ rest ∧
          Exec host first world done (.returned value) between ∧
          Prefix host (next value) between rest residual after := by
  induction progress with
  | refl =>
    intro α first next same
    exact .inl ⟨first, .refl _ _, same⟩
  | advance step =>
    intro α first next same
    subst same
    rcases Resource.advance_bind_cases step with ⟨middle, advance, rfl⟩ |
        ⟨value, rfl, advance⟩
    · exact .inl ⟨middle, advance.toPrefix, rfl⟩
    · exact .inr ⟨value, [], _, _, rfl, .pure _ _, advance.toPrefix⟩
  | trans _ tail ihHead ihTail =>
    intro α first next same
    rcases ihHead first next same with ⟨middle, firstPrefix, rfl⟩ |
        ⟨value, done, rest, between, rfl, firstRun, nextPrefix⟩
    · rcases ihTail middle next rfl with ⟨last, middlePrefix, rfl⟩ |
          ⟨value, done, rest, between, rfl, middleRun, nextPrefix⟩
      · exact .inl ⟨last, firstPrefix.trans middlePrefix, rfl⟩
      · exact .inr ⟨value, _ ++ done, rest, between, (List.append_assoc ..).symm,
          firstPrefix.complete middleRun, nextPrefix⟩
    · exact .inr ⟨value, done, _, between, List.append_assoc .., firstRun,
        nextPrefix.trans tail.toPrefix⟩

/-! ## Runs that stop -/

/-- `trace` holds the events of a run of `action` from `world` that stops before it ends: a prefix
of a run, or a run that traps. -/
def Stops {World : Type} (host : Host World) (action : Action α) (world : World)
    (trace : List Event) : Prop :=
  (∃ residual after, Prefix host action world trace residual after) ∨
    ∃ message final, Exec host action world trace (.trapped message) final

section Stops

variable {World : Type} {host : Host World} {world : World} {trace : List Event}

/-- A run of `pure value` that stops makes no event. -/
theorem Stops.pure {value : α} (h : Stops host (.pure value) world trace) : trace = [] := by
  rcases h with ⟨residual, after, run⟩ | ⟨message, final, run⟩
  · rcases prefix_uncons run.progress with ⟨-, rfl, -⟩ | ⟨_, _, _, _, step, _, _⟩
    · rfl
    · cases step
  · cases run

/-- A run of an exit that stops makes no event, or the exit that the host rejected. -/
theorem Stops.exit {code : UInt64} (h : Stops host (Action.exit code : Action α) world trace) :
    trace = [] ∨ ∃ message, trace = [.exitTrap (exitStatus code) message] := by
  rcases h with ⟨residual, after, run⟩ | ⟨message, final, run⟩
  · rcases prefix_uncons run.progress with ⟨-, rfl, -⟩ | ⟨_, _, _, _, step, _, _⟩
    · exact .inl rfl
    · cases step
  · cases run with
    | exitTrap _ => exact .inr ⟨_, rfl⟩

/-- A run of a read that stops makes no event, makes a run of its continuation on the rejection of
the read's capacity that stops, makes the read's event followed by a run that stops of its
continuation on the reply with some range of the read's region, or makes the read's event that
trapped. -/
theorem Stops.read {capacity : UInt64} {next : ReadReply → Action α}
    (h : Stops host (.read capacity next) world trace) :
    trace = [] ∨ Stops host (next ⟨61, Bytes.empty, Bytes.empty⟩) world trace ∨
      (∃ errno committed range after rest,
        trace = .read capacity (.returned errno committed) :: rest ∧
        Stops host (next (readReply errno committed range)) after rest) ∨
      ∃ message committed, trace = [.read capacity (.trapped message committed)] := by
  rcases h with ⟨residual, after, run⟩ | ⟨message, final, run⟩
  · rcases prefix_uncons run.progress with ⟨-, rfl, -⟩ |
        ⟨first, rest, middle, between, step, progress, rfl⟩
    · exact .inl rfl
    · cases step with
      | read_reject => exact .inr (.inl (.inl ⟨_, _, progress.toPrefix⟩))
      | read_return =>
        exact .inr (.inr (.inl ⟨_, _, _, _, _, rfl, .inl ⟨_, _, progress.toPrefix⟩⟩))
  · cases run with
    | read_reject _ next => exact .inr (.inl (.inr ⟨_, _, next⟩))
    | read_return _ _ _ _ next => exact .inr (.inr (.inl ⟨_, _, _, _, _, rfl, .inr ⟨_, _, next⟩⟩))
    | read_trap => exact .inr (.inr (.inr ⟨_, _, rfl⟩))

/-- A run of a write that stops makes no event, makes the write's event followed by a run of its
continuation on the reply that stops, or makes the write's event that trapped. -/
theorem Stops.write {output : Output} {bytes : Bytes} {next : WriteResult → Action α}
    (h : Stops host (.write output bytes next) world trace) :
    trace = [] ∨
      (∃ errno committed after rest,
        trace = .write output bytes (.returned errno committed) :: rest ∧
        Stops host (next (writeResult errno committed)) after rest) ∨
      ∃ message committed, trace = [.write output bytes (.trapped message committed)] := by
  rcases h with ⟨residual, after, run⟩ | ⟨message, final, run⟩
  · rcases prefix_uncons run.progress with ⟨-, rfl, -⟩ |
        ⟨first, rest, middle, between, step, progress, rfl⟩
    · exact .inl rfl
    · cases step with
      | write_return => exact .inr (.inl ⟨_, _, _, _, rfl, .inl ⟨_, _, progress.toPrefix⟩⟩)
  · cases run with
    | write_return _ next => exact .inr (.inl ⟨_, _, _, _, rfl, .inr ⟨_, _, next⟩⟩)
    | write_trap => exact .inr (.inr ⟨_, _, rfl⟩)

/-- A run of a call that stops makes no event, makes a run of its continuation on the rejection of
its arguments that stops, makes the call's event followed by a run of its continuation on the
reply that stops, or makes the call's event that trapped. -/
theorem Stops.sys {call : Call} {args : List Arg} {next : Reply → Action α}
    (h : Stops host (.sys call args next) world trace) :
    trace = [] ∨ (call.reject args ≠ 0 ∧ Stops host (next ⟨call.reject args, []⟩) world trace) ∨
      (∃ errno outputs after rest, trace = .sys call args (.returned errno outputs) :: rest ∧
        Stops host (next (sysReply errno outputs)) after rest) ∨
      ∃ message committed, trace = [.sys call args (.trapped message committed)] := by
  rcases h with ⟨residual, after, run⟩ | ⟨message, final, run⟩
  · rcases prefix_uncons run.progress with ⟨-, rfl, -⟩ |
        ⟨first, rest, middle, between, step, progress, rfl⟩
    · exact .inl rfl
    · cases step with
      | sys_reject fits => exact .inr (.inl ⟨fits, .inl ⟨_, _, progress.toPrefix⟩⟩)
      | sys_return => exact .inr (.inr (.inl ⟨_, _, _, _, rfl, .inl ⟨_, _, progress.toPrefix⟩⟩))
  · cases run with
    | sys_reject fits next => exact .inr (.inl ⟨fits, .inr ⟨_, _, next⟩⟩)
    | sys_return _ _ next => exact .inr (.inr (.inl ⟨_, _, _, _, rfl, .inr ⟨_, _, next⟩⟩))
    | sys_trap => exact .inr (.inr (.inr ⟨_, _, rfl⟩))

/-- A run of a loop that stops is a run of its passes from the first that stops. -/
theorem Stops.loop {count : UInt64} {init : σ} {test : UInt64 → σ → Bool}
    {step : UInt64 → σ → Action σ} {next : σ → Action α}
    (h : Stops host (.loop count init test step next) world trace) :
    Stops host (resumeLoop test step next count.toNat 0 init) world trace := by
  rcases h with ⟨residual, after, run⟩ | ⟨message, final, run⟩
  · rcases prefix_uncons run.progress with ⟨-, rfl, -⟩ |
        ⟨first, rest, middle, between, advance, progress, rfl⟩
    · exact .inl ⟨_, _, .refl _ _⟩
    · cases advance with
      | loop => exact .inl ⟨_, _, progress.toPrefix⟩
  · cases run with
    | loop run => exact .inr ⟨_, _, run.resume⟩

/-- A run of `Action.bind first next` that stops is a run of `first` that stops, or a run of
`first` that returns a value followed by a run of `next` on that value that stops. -/
theorem Stops.bind {first : Action α} {next : α → Action β}
    (h : Stops host (Action.bind first next) world trace) :
    Stops host first world trace ∨ ∃ value done rest between, trace = done ++ rest ∧
      Exec host first world done (.returned value) between ∧ Stops host (next value) between rest := by
  rcases h with ⟨residual, after, run⟩ | ⟨message, final, run⟩
  · rcases prefix_unbind run.progress first next rfl with ⟨middle, firstPrefix, -⟩ |
        ⟨value, done, rest, between, rfl, firstRun, nextPrefix⟩
    · exact .inl (.inl ⟨middle, after, firstPrefix⟩)
    · exact .inr ⟨value, done, rest, between, rfl, firstRun, .inl ⟨_, _, nextPrefix⟩⟩
  · obtain ⟨after, done, middle, rest, firstRun, continued, rfl⟩ := Exec.unbind first run
    cases middle with
    | returned value => exact .inr ⟨value, done, rest, after, rfl, firstRun, .inr ⟨_, _, continued⟩⟩
    | exited code =>
      obtain ⟨-, same, -⟩ := continued
      cases same
    | trapped message =>
      obtain ⟨rfl, -, -⟩ := continued
      rw [List.append_nil]
      exact .inl (.inr ⟨_, _, firstRun⟩)

end Stops

/-! ## Events of every run that stops -/

/-- `ok` holds of every event that `action` makes in a run that stops: of each read, write, and call
for every reply, and of each exit that the host rejects. -/
def Every (ok : Event → Prop) : {α : Type} → Action α → Prop
  | _, .pure _ => True
  | _, .read capacity next =>
    (∀ reply, ok (.read capacity reply)) ∧ ∀ result, Every ok (next result)
  | _, .write output bytes next =>
    (∀ reply, ok (.write output bytes reply)) ∧ ∀ result, Every ok (next result)
  | _, .exit code => ∀ message, ok (.exitTrap (exitStatus code) message)
  | _, .loop _ _ _ step next =>
    (∀ index state, Every ok (step index state)) ∧ ∀ state, Every ok (next state)
  | _, .sys call args next =>
    (∀ reply, ok (.sys call args reply)) ∧ ∀ reply, Every ok (next reply)

theorem Every.bind {ok : Event → Prop} :
    ∀ {α β : Type} (first : Action α) {next : α → Action β}, Every ok first →
      (∀ value, Every ok (next value)) → Every ok (Action.bind first next)
  | _, _, .pure value, _, _, hNext => hNext value
  | _, _, .read _ continuation, _, h, hNext =>
    ⟨h.1, fun result => Every.bind (continuation result) (h.2 result) hNext⟩
  | _, _, .write _ _ continuation, _, h, hNext =>
    ⟨h.1, fun result => Every.bind (continuation result) (h.2 result) hNext⟩
  | _, _, .exit _, _, h, _ => h
  | _, _, .loop _ _ _ _ continuation, _, h, hNext =>
    ⟨h.1, fun state => Every.bind (continuation state) (h.2 state) hNext⟩
  | _, _, .sys _ _ continuation, _, h, hNext =>
    ⟨h.1, fun reply => Every.bind (continuation reply) (h.2 reply) hNext⟩

/-- `ok` holds of every event of a run of an action that stops when `Every ok` holds of the
action. -/
theorem Every.stops {ok : Event → Prop} {World : Type} {host : Host World} :
    ∀ {α : Type} (action : Action α) {world : World} {trace : List Event},
      Every ok action → Stops host action world trace → ∀ e ∈ trace, ok e := by
  intro α action
  induction action with
  | pure value =>
    intro world trace _ h e member
    rw [h.pure] at member
    nomatch member
  | read capacity next ih =>
    intro world trace every h e member
    rcases h.read with rfl | rejected | ⟨errno, committed, range, after, rest, rfl, more⟩ |
        ⟨message, committed, rfl⟩
    · nomatch member
    · exact ih _ (every.2 _) rejected e member
    · rcases List.mem_cons.mp member with rfl | member
      · exact every.1 _
      · exact ih _ (every.2 _) more e member
    · rw [List.mem_singleton.mp member]
      exact every.1 _
  | write output bytes next ih =>
    intro world trace every h e member
    rcases h.write with rfl | ⟨errno, committed, after, rest, rfl, more⟩ |
        ⟨message, committed, rfl⟩
    · nomatch member
    · rcases List.mem_cons.mp member with rfl | member
      · exact every.1 _
      · exact ih _ (every.2 _) more e member
    · rw [List.mem_singleton.mp member]
      exact every.1 _
  | exit code =>
    intro world trace every h e member
    rcases h.exit with rfl | ⟨message, rfl⟩
    · nomatch member
    · rw [List.mem_singleton.mp member]
      exact every message
  | loop count init test step next ihStep ihNext =>
    intro world trace every h
    suffices passes : ∀ (remaining index : Nat) (state : _) {world : World}
        {trace : List Event},
        Stops host (resumeLoop test step next remaining index state) world trace →
          ∀ e ∈ trace, ok e by
      exact passes _ _ _ h.loop
    intro remaining
    induction remaining with
    | zero =>
      intro index state world trace h
      exact ihNext state (every.2 state) h
    | succ remaining ihPasses =>
      intro index state world trace h
      simp only [resumeLoop] at h
      split at h
      · rcases h.bind with inside | ⟨value, done, rest, between, rfl, stepRun, more⟩
        · exact ihStep _ _ (every.1 _ _) inside
        · intro e member
          rcases List.mem_append.mp member with member | member
          · exact ihStep _ _ (every.1 _ _) (.inl ⟨_, _, Exec.returned_prefix _ stepRun⟩) e member
          · exact ihPasses _ _ more e member
      · exact ihNext state (every.2 state) h
  | sys call args next ih =>
    intro world trace every h e member
    rcases h.sys with rfl | ⟨_, rejected⟩ | ⟨errno, outputs, after, rest, rfl, more⟩ |
        ⟨message, committed, rfl⟩
    · nomatch member
    · exact ih _ (every.2 _) rejected e member
    · rcases List.mem_cons.mp member with rfl | member
      · exact every.1 _
      · exact ih _ (every.2 _) more e member
    · rw [List.mem_singleton.mp member]
      exact every.1 _

/-- `ok` holds of every event of a run of an action that returns when `Every ok` holds of the
action. -/
theorem Every.returns {ok : Event → Prop} {World : Type} {host : Host World} {action : Action α}
    {world final : World} {trace : List Event} {value : α} (every : Every ok action)
    (run : Exec host action world trace (.returned value) final) : ∀ e ∈ trace, ok e :=
  Every.stops action every (.inl ⟨_, _, Exec.returned_prefix _ run⟩)

/-! ## `writeAll` -/

/-- A run that stops of the passes of the loop of `writeAll buffer start count` from `written`
bytes taken, at most the window's length, makes writes to standard output, each of which offered at
least one byte, the bytes of the window after those that the writes before it took, followed by at
most one exit that the host rejected. -/
theorem writeAll_loop_stops {World : Type} {host : Host World} (buffer : Bytes)
    (start count : UInt64) (small : buffer.data.size < 2 ^ 64) {test : UInt64 → UInt64 → Bool}
    {step : UInt64 → UInt64 → Action UInt64}
    (tested : ∀ index written, test index written =
      decide (written < min count (buffer.size - min start buffer.size)))
    (stepped : ∀ index written, step index written =
      .write .stdout (buffer.range (min start buffer.size + written)
        (min count (buffer.size - min start buffer.size) - written)) fun reply =>
        if reply.errno != 0 then Action.exit reply.errno else .pure (written + reply.count)) :
    ∀ (remaining index : Nat) (written : UInt64) {world : World} {trace : List Event},
      written.toNat ≤ (buffer.window start count).2 →
      Stops host (resumeLoop test step .pure remaining index written) world trace →
      ∃ writes, (trace = writes ∨ ∃ code message, trace = writes ++ [.exitTrap code message]) ∧
        Offered (buffer.range start count).data.data.toList written.toNat writes ∧
        ∀ e ∈ writes, ∃ offered reply, e = .write .stdout offered reply ∧ offered.data.size ≠ 0
  | 0, _, _, _, _, _, h => ⟨[], .inl h.pure, trivial, fun _ member => nomatch member⟩
  | remaining + 1, index, written, _, _, le, h => by
    have hLength := (buffer.window_of_words small start count).2
    have hWindow := buffer.window_le start count
    have length : (buffer.range start count).data.data.toList.length =
        (buffer.window start count).2 := by
      simp
    have offers := buffer.range_after small le
    have offeredSize : (buffer.range (min start buffer.size + written)
        (min count (buffer.size - min start buffer.size) - written)).data.size =
          (buffer.window start count).2 - written.toNat := by
      have := congrArg List.length offers
      simpa [length] using this
    simp only [resumeLoop] at h
    split at h
    · rename_i passes
      rw [tested] at passes
      have left : written.toNat < (buffer.window start count).2 := by
        simpa [UInt64.lt_iff_toNat_lt, hLength] using passes
      have first : ∀ reply, ∃ offered reply', Event.write .stdout (buffer.range
          (min start buffer.size + written) (min count (buffer.size - min start buffer.size) -
            written)) reply = .write .stdout offered reply' ∧ offered.data.size ≠ 0 :=
        fun reply => ⟨_, reply, rfl, by omega⟩
      rcases h.bind with inside | ⟨value, done, rest, between, rfl, stepRun, more⟩
      · rw [stepped] at inside
        rcases inside.write with rfl | ⟨errno, committed, after, rest, rfl, reply⟩ |
            ⟨message, committed, rfl⟩
        · exact ⟨[], .inl rfl, trivial, fun _ member => nomatch member⟩
        · have one : ∀ e ∈ [Event.write .stdout (buffer.range (min start buffer.size + written)
              (min count (buffer.size - min start buffer.size) - written))
                (.returned errno committed)],
              ∃ offered reply, e = .write .stdout offered reply ∧ offered.data.size ≠ 0 :=
            fun e member => by
              rw [List.mem_singleton.mp member]
              exact first _
          split at reply
          · rcases reply.exit with rfl | ⟨message, rfl⟩
            · exact ⟨[_], .inl rfl, ⟨⟨_, _, rfl, offers⟩, trivial⟩, one⟩
            · exact ⟨[_], .inr ⟨_, message, rfl⟩, ⟨⟨_, _, rfl, offers⟩, trivial⟩, one⟩
          · rw [reply.pure]
            exact ⟨[_], .inl rfl, ⟨⟨_, _, rfl, offers⟩, trivial⟩, one⟩
        · refine ⟨[_], .inl rfl, ⟨⟨_, _, rfl, offers⟩, trivial⟩, fun e member => ?_⟩
          rw [List.mem_singleton.mp member]
          exact first _
      · rw [stepped] at stepRun
        cases stepRun with
        | @write_return _ _ _ _ _ _ _ _ _ errno committed reply next =>
          by_cases zero : errno = 0
          · subst zero
            simp only [writeResult, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true] at next
            cases next
            have bound := (host.write_bound reply).1
            simp only [Transfer.committed, offeredSize] at bound
            have sum : (written + committed).toNat = written.toNat + committed.toNat := by
              rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
            obtain ⟨writes, shape, offered, all⟩ := writeAll_loop_stops buffer start count small
              tested stepped remaining (index + 1) (written + committed) (by omega) more
            have taken : (Event.write .stdout (buffer.range (min start buffer.size + written)
                (min count (buffer.size - min start buffer.size) - written))
                  (.returned 0 committed)).stdoutTaken.length = committed.toNat := by
              simp only [Event.stdoutTaken, ↓reduceIte, offers, List.length_take,
                List.length_drop, length]
              omega
            refine ⟨.write .stdout _ (.returned 0 committed) :: writes, ?_,
              ⟨⟨_, _, rfl, offers⟩, ?_⟩, fun e member => ?_⟩
            · rcases shape with rfl | ⟨code, message, rfl⟩
              · exact .inl rfl
              · exact .inr ⟨code, message, rfl⟩
            · rw [taken, ← sum]
              exact offered
            · rcases List.mem_cons.mp member with rfl | member
              · exact first _
              · exact all e member
          · have failing : ((writeResult errno committed).errno != 0) = true := by
              simp [writeResult, zero]
            dsimp only at next
            rw [ite_eq_left failing] at next
            cases next
    · exact ⟨[], .inl h.pure, trivial, fun _ member => nomatch member⟩

/-- A run of `writeAll buffer start count` that stops makes writes to standard output, each of which
offered at least one byte, the bytes of the window that `start` and `count` name after those that
the writes before it took, followed by at most one exit that the host rejected. -/
theorem writeAll_stops {World : Type} {host : Host World} {buffer : Bytes} {start count : UInt64}
    (small : buffer.data.size < 2 ^ 64) {world : World} {trace : List Event}
    (h : Stops host (writeAll buffer start count) world trace) :
    ∃ writes, (trace = writes ∨ ∃ code message, trace = writes ++ [.exitTrap code message]) ∧
      Offered (buffer.range start count).data.data.toList 0 writes ∧
      ∀ e ∈ writes, ∃ offered reply, e = .write .stdout offered reply ∧ offered.data.size ≠ 0 :=
  writeAll_loop_stops buffer start count small (fun _ _ => rfl) (fun _ _ => rfl) _ 0 0
    (by simp) (Stops.loop h)

end Verified.Wasi
