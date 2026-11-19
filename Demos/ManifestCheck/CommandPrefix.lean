import Demos.ManifestCheck.CommandProof
import Verified.Wasi.Stops

/-! The events of every run of the command's `main` followed by its exit that stops before the
exit meet `SoFar` (`stops_soFar`): a prefix of a run, which a trap of the guest cuts short
(`prefix_soFar`), and a run that traps in the host or at an exit that the host rejects
(`trapped_soFar`).

The proof follows `main` with the lemmas of `Verified.Wasi.Stops`: a run of `Action.bind first next`
that stops is a run of `first` that stops, or a run of `first` that returns followed by a run of
`next` that stops.  The parts that return have the events that the run lemmas of the command's
proof give.  A part that stops has only the events that its every call allows (`Every.stops`): the
calls of `args` (`args_every`), the calls on the descriptor of a bracket's body
(`readManifest_every`, `hashFile_every`), and the writes of `writeAll` with at most one rejected
exit at their end (`writeAll_stops`).  `withOpen_stops` gives the events of a bracket that stops,
`step_stops` those of a pass of the checks, `checks_stops` those of their loop, and
`checkLines_stops` those of `checkLines`.  `main_stops` follows `main`, and `confined_of` assembles
`ConfinedSoFar` from the run of `args`, the `ManifestRun`, and the opens that follow. -/

namespace Demos.ManifestCheck

open LeanExe LeanExe.Wasi Verified.Wasi Library.Hashing.Words Library.Hashing.Sha256

/-! ## The use of descriptors -/

theorem HandledSoFar.closed {events : List Event} (h : Handled events) : HandledSoFar events :=
  ⟨events, [], (List.append_nil _).symm, h, .empty⟩

/-- Events of `Handled` followed by those of `HandledSoFar` meet `HandledSoFar`. -/
theorem Handled.soFar {first events : List Event} (h : Handled first)
    (rest : HandledSoFar events) : HandledSoFar (first ++ events) := by
  obtain ⟨closed, tail, rfl, handled, unfinished⟩ := rest
  exact ⟨first ++ closed, tail, (List.append_assoc ..).symm, h.append handled, unfinished⟩

theorem handled_writes : ∀ {writes : List Event},
    (∀ e ∈ writes, ∃ offered reply, e = .write .stdout offered reply) → Handled writes
  | [], _ => .nil
  | e :: writes, h => by
    obtain ⟨offered, reply, rfl⟩ := h e (List.mem_cons_self ..)
    exact .write (handled_writes fun x member => h x (List.mem_cons_of_mem _ member))

/-- Every open of events that start with an open and hold no other names the arguments of the
first. -/
theorem only_open {args : List Arg} {reply : Transfer (List Bytes)} {events : List Event}
    (none : ∀ arguments reply, Event.sys .pathOpen arguments reply ∉ events) :
    ∀ arguments reply', Event.sys .pathOpen arguments reply' ∈
      Event.sys .pathOpen args reply :: events → arguments = args := by
  intro arguments reply' member
  rcases List.mem_cons.mp member with same | member
  · exact (Event.sys.inj same).2.1
  · exact absurd member (none arguments reply')

theorem OnDescriptor.no_open {fd : UInt64} {events : List Event}
    (calls : ∀ e ∈ events, OnDescriptor fd e) :
    ∀ arguments reply, Event.sys .pathOpen arguments reply ∉ events :=
  fun arguments reply member => (calls _ member).not_open arguments reply rfl

theorem no_open_close {events : List Event} {args : List Arg} {closed : Transfer (List Bytes)}
    (none : ∀ arguments reply, Event.sys .pathOpen arguments reply ∉ events) :
    ∀ arguments reply, Event.sys .pathOpen arguments reply ∉
      events ++ [.sys .fdClose args closed] := by
  intro arguments reply member
  rcases List.mem_append.mp member with member | member
  · exact none arguments reply member
  · exact sys_ne (by decide) (List.mem_singleton.mp member)

/-! ## The events that each call allows -/

theorem args_every :
    Every (fun e => ∃ call ar rep, e = .sys call ar rep ∧ (call = .argsSizesGet ∨ call = .argsGet))
      args := by
  unfold args
  refine ⟨fun _ => ⟨_, _, _, rfl, .inl rfl⟩, fun sizes => ?_⟩
  dsimp only
  split
  · trivial
  split
  · trivial
  refine ⟨fun _ => ⟨_, _, _, rfl, .inr rfl⟩, fun got => ?_⟩
  dsimp only
  split <;> trivial

/-- Every event of a run of `readManifest` on the descriptor `fd` that stops is a call on `fd`. -/
theorem readManifest_every (fd : UInt64) (buffer : Bytes) :
    Every (OnDescriptor fd) (readManifest ⟨fd⟩ buffer) := by
  unfold readManifest readBytes
  refine Every.bind _ ⟨fun _ => .inr ⟨_, rfl⟩, fun _ => trivial⟩ fun stat => ?_
  split
  · trivial
  split
  · trivial
  refine Every.bind _ ⟨fun index state => ?_, fun _ => trivial⟩ fun s => ?_
  · refine Every.bind _ ⟨fun _ => .inl ⟨_, _, rfl⟩, fun _ => trivial⟩ fun got => ?_
    split
    · trivial
    split <;> trivial
  · split
    · trivial
    refine Every.bind _ ⟨fun _ => .inl ⟨_, _, rfl⟩, fun _ => trivial⟩ fun probe => ?_
    split
    · trivial
    split <;> trivial

/-- Every event of a run of `hashFile` on the descriptor `fd` that stops is a call on `fd`. -/
theorem hashFile_every (fd : UInt64) (buffer : Bytes) :
    Every (OnDescriptor fd) (hashFile ⟨fd⟩ buffer) := by
  unfold hashFile
  refine Every.bind _ ⟨fun index state => ?_, fun _ => trivial⟩ fun _ => trivial
  refine Every.bind _ ⟨fun _ => .inl ⟨_, _, rfl⟩, fun _ => trivial⟩ fun got => ?_
  split
  · trivial
  split
  · trivial
  split <;> trivial

/-! ## Brackets -/

/-- A run of `withOpen` that stops, under descriptor 3 with the flag `symlink_follow` and the
rights `rights`, around an error continuation that returns `fallback errno` and a body whose every
event in a run that stops is a call on its descriptor, makes the events of `HandledSoFar`, and
every open among them names `name` with the rights `rights`. -/
theorem withOpen_stops {World α : Type} {host : Host World} {name : Bytes} {rights : UInt64}
    {fallback : UInt64 → α} {body : Handle → Action α}
    (calls : ∀ fd, Every (OnDescriptor fd) (body ⟨fd⟩)) {world : World} {trace : List Event}
    (h : Stops host (withOpen .preopened 1 name 0 rights 0 0 (fun errno => pure (fallback errno))
      body) world trace) :
    HandledSoFar trace ∧ ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ trace →
      arguments = openArgs rights name.data.data.toList := by
  rw [openArgs_bytes]
  unfold withOpen at h
  rcases h.sys with rfl | ⟨rejected, fallen⟩ | ⟨errno, outputs, after, rest, rfl, opened⟩ |
      ⟨message, committed, rfl⟩
  · exact ⟨HandledSoFar.closed .nil, fun _ _ member => nomatch member⟩
  · simp only [bne_iff_ne, ne_eq, rejected, not_false_eq_true, ↓reduceIte] at fallen
    rw [fallen.pure]
    exact ⟨HandledSoFar.closed .nil, fun _ _ member => nomatch member⟩
  · by_cases zero : errno = 0
    · subst zero
      have hReply : sysReply 0 outputs = ⟨0, outputs⟩ := rfl
      simp only [hReply, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at opened
      rcases opened.bind with inside | ⟨value, done, last, between, rfl, bodyRun, closing⟩
      · have inner := Every.stops _ (calls _) inside
        exact ⟨⟨[], _, rfl, .nil, .opened inner⟩, only_open (OnDescriptor.no_open inner)⟩
      · have inner := Every.returns (calls _) bodyRun
        have none := OnDescriptor.no_open inner
        rcases closing.sys with rfl | ⟨_, fallen⟩ | ⟨closeErrno, closed, after, tail, rfl, ended⟩ |
            ⟨message, closed, rfl⟩
        · rw [List.append_nil]
          exact ⟨⟨[], _, rfl, .nil, .opened inner⟩, only_open none⟩
        · rw [fallen.pure, List.append_nil]
          exact ⟨⟨[], _, rfl, .nil, .opened inner⟩, only_open none⟩
        · rw [ended.pure]
          exact ⟨HandledSoFar.closed (.bracket inner .nil), only_open (no_open_close none)⟩
        · exact ⟨HandledSoFar.closed (.bracket inner .nil), only_open (no_open_close none)⟩
    · have hReply : sysReply errno outputs = ⟨errno, []⟩ := by simp [sysReply, zero]
      have off : ((errno != 0) = true) = True := eq_true (bne_iff_ne.mpr zero)
      simp only [hReply, off, ↓reduceIte] at opened
      rw [opened.pure]
      exact ⟨⟨[_], [], rfl, .refused zero .nil, .empty⟩,
        only_open fun _ _ member => nomatch member⟩
  · exact ⟨⟨[], _, rfl, .nil, .openTrapped⟩, only_open fun _ _ member => nomatch member⟩

/-! ## The checks -/

/-- The events of a run that stopped of the checks of the lines of the manifest's bytes `m`: those
of `HandledSoFar`, and every open names the name of a line of `m`. -/
def LinesSoFar (m : List UInt8) (events : List Event) : Prop :=
  HandledSoFar events ∧ ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ events →
    ∃ l ∈ lines m, arguments = openArgs fileRights (l.2.drop 66)

theorem LinesSoFar.nil {m : List UInt8} : LinesSoFar m [] :=
  ⟨HandledSoFar.closed .nil, fun _ _ member => nomatch member⟩

theorem LinesSoFar.after {m : List UInt8} {first events : List Event} (handled : Handled first)
    (opens : ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ first →
      ∃ l ∈ lines m, arguments = openArgs fileRights (l.2.drop 66))
    (rest : LinesSoFar m events) : LinesSoFar m (first ++ events) :=
  ⟨handled.soFar rest.1, fun arguments reply member => by
    rcases List.mem_append.mp member with member | member
    · exact opens arguments reply member
    · exact rest.2 arguments reply member⟩

/-- A run of `writeAll` that stops makes the events of `LinesSoFar`: writes to standard output and
at most one rejected exit. -/
theorem writes_soFar {World : Type} {host : Host World} {buffer : Bytes} {start count : UInt64}
    {world : World} {events : List Event} (m : List UInt8)
    (h : Stops host (writeAll buffer start count) world events) : LinesSoFar m events := by
  obtain ⟨writes, shape, all⟩ := writeAll_stops h
  have none : ∀ arguments reply, Event.sys .pathOpen arguments reply ∉ writes :=
    fun arguments reply member => by
      obtain ⟨_, _, same⟩ := all _ member
      cases same
  rcases shape with rfl | ⟨code, message, rfl⟩
  · exact ⟨HandledSoFar.closed (handled_writes all),
      fun arguments reply member => absurd member (none arguments reply)⟩
  · refine ⟨⟨writes, _, rfl, handled_writes all, .exitRejected⟩, fun arguments reply member => ?_⟩
    rcases List.mem_append.mp member with member | member
    · exact absurd member (none arguments reply)
    · cases List.mem_singleton.mp member

/-- A run that stops of the pass of `checkLines` on line `j` of a manifest that the pure core
accepts makes the events of `LinesSoFar`. -/
theorem step_stops {World : Type} {host : Host World} (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2)
    (j : Nat) (hj : j < (lines m.data.data.toList).length) {buffer : Bytes}
    (hsize : buffer.data.size = 65536) (failed : UInt64) {world : World} {trace : List Event}
    (h : Stops host (checkStep m (parse m) (UInt64.ofNat j) (buffer, failed, 0)) world trace) :
    LinesSoFar m.data.data.toList trace := by
  have hlsmall := lines_length m.data.data.toList
  have hlenm : m.data.data.toList.length = m.data.size := by simp
  have hparse := parse_accepted m hm accepted
  have hmem : (lines m.data.data.toList)[j] ∈ lines m.data.data.toList := List.getElem_mem hj
  generalize hls : lines m.data.data.toList = ls at accepted hj hlsmall hparse hmem ⊢
  have hin : ls[j] ∈ lines m.data.data.toList := by rw [hls]; exact hmem
  have hpos := lines_pos m.data.data.toList ls[j] hin
  obtain ⟨hstart, hstop⟩ := entry_get ls j hj (by omega)
  have hl : (m.data.data.toList.drop ls[j].1).take (ls[j].1 + ls[j].2.length - ls[j].1) =
      ls[j].2 := by
    rw [Nat.add_sub_cancel_left]
    exact hpos.1
  have hline : WellFormed ((m.data.data.toList.drop ls[j].1).take
      (ls[j].1 + ls[j].2.length - ls[j].1)) := by
    rw [hl]
    exact accepted.2 _ hmem
  obtain ⟨hname, -⟩ := entry_name m hm ls[j].1 (ls[j].1 + ls[j].2.length) (by omega) (by omega)
    hline
  rw [hl] at hname
  unfold checkStep at h
  rw [hparse, hstart, hstop] at h
  dsimp only at h
  rcases h.bind with inside | ⟨r, first, rest, after, rfl, checkRun, writing⟩
  · obtain ⟨handled, opens⟩ := withOpen_stops (body := fun file => hashFile file buffer)
      (fun fd => hashFile_every fd buffer) inside
    refine ⟨handled, fun arguments reply member => ⟨ls[j], hin, ?_⟩⟩
    rw [opens arguments reply member, hname, fileRights]
  · obtain ⟨-, -, results⟩ := entry_check m hm ls[j].1 (ls[j].1 + ls[j].2.length) (by omega)
      (by omega) hline hsize checkRun
    obtain ⟨-, check⟩ := results r rfl
    rw [hl] at check
    refine LinesSoFar.after check.handled
      (fun arguments reply member => ⟨ls[j], hin, check.opens arguments reply member⟩) ?_
    rcases writing.bind with inside | ⟨v, writes, last, after', rfl, writeRun, ended⟩
    · exact writes_soFar _ inside
    · rw [ended.pure, List.append_nil]
      exact writes_soFar _ (.inl ⟨_, _, Exec.returned_prefix _ writeRun⟩)

/-- A run of the loop of `checkLines` from a state whose writes stalled makes no event. -/
theorem stalled_stops {World : Type} {host : Host World} {test : UInt64 → CheckState → Bool}
    {step : UInt64 → CheckState → Action CheckState} (tested : ∀ i s, test i s = (s.2.2 == 0))
    {remaining index : Nat} {buffer : Bytes} {failed : UInt64} {world : World}
    {trace : List Event}
    (h : Stops host (resumeLoop test step .pure remaining index (buffer, failed, 1)) world trace) :
    trace = [] := by
  cases remaining with
  | zero => exact h.pure
  | succ remaining =>
    simp only [resumeLoop] at h
    split at h
    · rename_i passes
      rw [tested] at passes
      change ((1 : UInt64) == 0) = true at passes
      exact absurd passes (by decide)
    · exact h.pure

/-- A run that stops of the loop of `checkLines` on a manifest that the pure core accepts, from
line `j` with the passes for the lines that remain, makes the events of `LinesSoFar`. -/
theorem checks_stops {World : Type} {host : Host World} (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2)
    {test : UInt64 → CheckState → Bool} {step : UInt64 → CheckState → Action CheckState}
    (tested : ∀ i s, test i s = (s.2.2 == 0))
    (stepped : ∀ i s, step i s = checkStep m (parse m) i s) :
    ∀ (remaining j : Nat) (buffer : Bytes) (failed : UInt64) {world : World}
      {trace : List Event},
      j + remaining = (lines m.data.data.toList).length → buffer.data.size = 65536 →
      Stops host (resumeLoop test step .pure remaining j (buffer, failed, 0)) world trace →
      LinesSoFar m.data.data.toList trace
  | 0, _, _, _, _, _, _, _, h => by
    rw [Stops.pure h]
    exact LinesSoFar.nil
  | remaining + 1, j, buffer, failed, _, _, hj, hsize, h => by
    have hjl : j < (lines m.data.data.toList).length := by omega
    simp only [resumeLoop, tested, beq_self_eq_true, ↓reduceIte] at h
    rcases h.bind with inside | ⟨s, done, rest, between, rfl, stepRun, more⟩
    · rw [stepped] at inside
      exact step_stops m hm accepted j hjl hsize failed inside
    · rw [stepped] at stepRun
      obtain ⟨returns, -⟩ := check_step m hm accepted j hjl hsize failed stepRun
      obtain ⟨ok, fileEvents, writes, buffer', stalled, rfl, rfl, check, hbuf, ending⟩ :=
        returns _ rfl
      have wrote : ∀ e ∈ writes, WroteSome e := by
        rcases ending with ⟨-, lw⟩ | ⟨-, lw⟩ <;> exact lw.2.2.1
      have none : ∀ arguments reply, Event.sys .pathOpen arguments reply ∉ writes := by
        rcases ending with ⟨-, lw⟩ | ⟨-, lw⟩ <;> exact lw.no_open
      refine LinesSoFar.after (check.handled.append (Handled.writes wrote))
        (fun arguments reply member => ?_) ?_
      · rcases List.mem_append.mp member with member | member
        · exact ⟨_, List.getElem_mem hjl, check.opens arguments reply member⟩
        · exact absurd member (none arguments reply)
      · rcases ending with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact checks_stops m hm accepted tested stepped remaining (j + 1) buffer' _ (by omega)
            hbuf more
        · rw [stalled_stops tested more]
          exact LinesSoFar.nil

/-- A run that stops of `checkLines` on a manifest that the pure core accepts makes the events of
`LinesSoFar`. -/
theorem checkLines_stops {World : Type} {host : Host World} (m : Bytes)
    (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2)
    {buffer : Bytes} (hsize : buffer.data.size = 65536) {world : World} {trace : List Event}
    (h : Stops host (checkLines m (parse m) buffer) world trace) :
    LinesSoFar m.data.data.toList trace := by
  unfold checkLines at h
  rcases h.bind with inside | ⟨s, done, rest, between, rfl, loopRun, ending⟩
  · have passes := inside.loop
    rw [parse_passes m hm accepted] at passes
    exact checks_stops m hm accepted (fun _ _ => rfl) (fun _ _ => rfl) _ 0 buffer 0 (by simp) hsize
      passes
  · cases loopRun with
    | loop loopRun =>
      rw [parse_passes m hm accepted] at loopRun
      obtain ⟨returned, -⟩ := checks_loop m hm accepted (fun _ _ => rfl) (fun _ _ => rfl) _ 0
        buffer 0 (by simp) hsize (.inl rfl) loopRun
      have checks := returned s rfl
      have empty : rest = [] := by
        split at ending <;> exact ending.pure
      subst empty
      rw [List.append_nil]
      refine ⟨HandledSoFar.closed checks.handled, fun arguments reply member => ?_⟩
      obtain ⟨l, hl, same⟩ := checks.opens arguments reply member
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      exact ⟨l', hl', same⟩

/-! ## `main` -/

/-- The events of `args` alone meet `SoFar`. -/
theorem soFar_args {World : Type} {host : Host World} {world : World} {trace : List Event}
    (calls : ∀ e ∈ trace, ∃ call ar rep, e = .sys call ar rep ∧
      (call = .argsSizesGet ∨ call = .argsGet)) :
    SoFar host world trace :=
  ⟨.inl (no_open_of_args calls), HandledSoFar.closed (handled_of_args calls)⟩

/-- `ConfinedSoFar` of the events of a run of `args` whose buffer holds one argument, `name`,
those of a `ManifestRun` of `name` with the status `status` and the bytes `manifest`, and events
whose every open names a line of `manifest` after a status of 0. -/
theorem confined_of {World : Type} {host : Host World} {world after : World} {a : ArgsResult}
    {pre opening post : List Event} {name manifest : List UInt8} {status : UInt64}
    (argsRun : Exec host args world pre (.returned a) after)
    (hone : OneArgument a.bytes.data.data.toList name)
    (mrun : ManifestRun name opening status manifest)
    (opens : ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ post →
      status = 0 ∧ ∃ l ∈ lines manifest, arguments = openArgs fileRights (l.2.drop 66)) :
    ConfinedSoFar host world (pre ++ (opening ++ post)) := by
  have preEvents := args_events argsRun
  refine .inr ⟨a, pre, opening ++ post, after, if status = 0 then manifest else [], rfl, argsRun,
    ?_, fun arguments reply member => ?_⟩
  · by_cases zero : status = 0
    · rw [ite_eq_left zero]
      subst zero
      exact .inr ⟨name, opening, post, rfl, mrun⟩
    · rw [ite_eq_right zero]
      exact .inl rfl
  · rcases List.mem_append.mp member with member | member
    · exact absurd member (no_open_of_args preEvents arguments reply)
    rcases List.mem_append.mp member with member | member
    · exact ⟨name, .inl ⟨mrun.opens arguments reply member, hone⟩⟩
    · obtain ⟨zero, l, hl, same⟩ := opens arguments reply member
      refine ⟨l.2.drop 66, .inr ⟨same, l, ?_, rfl⟩⟩
      rw [ite_eq_left zero]
      exact hl

/-- `SoFar` of the events of `confined_of` whose last part meets `HandledSoFar`. -/
theorem soFar_of {World : Type} {host : Host World} {world after : World} {a : ArgsResult}
    {pre opening post : List Event} {name manifest : List UInt8} {status : UInt64}
    (argsRun : Exec host args world pre (.returned a) after)
    (hone : OneArgument a.bytes.data.data.toList name)
    (mrun : ManifestRun name opening status manifest) (handled : HandledSoFar post)
    (opens : ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ post →
      status = 0 ∧ ∃ l ∈ lines manifest, arguments = openArgs fileRights (l.2.drop 66)) :
    SoFar host world (pre ++ (opening ++ post)) :=
  ⟨confined_of argsRun hone mrun opens,
    (handled_of_args (args_events argsRun)).soFar (mrun.handled.soFar handled)⟩

/-- `SoFar` of the events of a run of `args` whose buffer holds one argument, `name`, followed by
events of `HandledSoFar` whose every open names `name` with the rights `manifestRights`. -/
theorem soFar_opening {World : Type} {host : Host World} {world after : World} {a : ArgsResult}
    {pre rest : List Event} {name : List UInt8}
    (argsRun : Exec host args world pre (.returned a) after)
    (hone : OneArgument a.bytes.data.data.toList name) (handled : HandledSoFar rest)
    (opens : ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ rest →
      arguments = openArgs manifestRights name) :
    SoFar host world (pre ++ rest) := by
  have preEvents := args_events argsRun
  refine ⟨.inr ⟨a, pre, rest, after, [], rfl, argsRun, .inl rfl, fun arguments reply member => ?_⟩,
    (handled_of_args preEvents).soFar handled⟩
  rcases List.mem_append.mp member with member | member
  · exact absurd member (no_open_of_args preEvents arguments reply)
  · exact ⟨name, .inl ⟨opens arguments reply member, hone⟩⟩

/-- The events of every run of `main` that stops meet `SoFar`. -/
theorem main_stops {World : Type} {host : Host World} {world : World} {trace : List Event}
    (h : Stops host main world trace) : SoFar host world trace := by
  unfold main at h
  rcases h.bind with inside | ⟨a, pre, rest, after, rfl, argsRun, cont⟩
  · exact soFar_args (Every.stops _ args_every inside)
  obtain ⟨-, argsFacts⟩ := args_returned argsRun
  obtain ⟨-, aSize⟩ := argsFacts a rfl
  have preEvents := args_events argsRun
  change Stops host (if a.errno != 0 then Action.pure a.errno else _) after rest at cont
  split at cont
  · rw [cont.pure, List.append_nil]
    exact soFar_args preEvents
  dsimp only at cont
  split at cont
  · rw [cont.pure, List.append_nil]
    exact soFar_args preEvents
  rename_i accept
  have hone := (argument_cases a.bytes (by omega)).2 (by simpa using accept)
  generalize slice a.bytes ((argScan a.bytes).2.1 + 1)
    (a.bytes.size - (argScan a.bytes).2.1 - 2) = name at hone cont
  have hnsize : name.data.size < 2 ^ 32 := by
    obtain ⟨program, hprog, -, -⟩ := hone
    have := congrArg List.length hprog
    simp at this
    omega
  have hargs : openArgs manifestRights name.data.data.toList =
      [.word 3, .word 1, .bytes name, .word 0, .word 2097154, .word 0, .word 0] := by
    rw [openArgs_bytes]
    rfl
  generalize hbuf : (Bytes.build chunk fun _ => 0) = buffer at cont
  have hbsize : buffer.data.size = 65536 := by
    rw [← hbuf, build_size]
    rfl
  rcases cont.bind with inside | ⟨got, opening, post, after2, rfl, openRun, cont2⟩
  · obtain ⟨handled, opens⟩ := withOpen_stops (body := fun file => readManifest file buffer)
      (fun fd => readManifest_every fd buffer) inside
    exact soFar_opening argsRun hone handled opens
  obtain ⟨-, openResults⟩ := withOpen_run (rights := 2097154)
    (fallback := fun errno => (errno, Bytes.build 0 fun _ => 0, Bytes.build 0 fun _ => 0))
    (body := fun file => readManifest file buffer) hnsize (.inr rfl)
    (fun fd _ _ _ _ hfd bodyRun => (readManifest_run hfd hbsize bodyRun).1) openRun
  obtain ⟨errno, outputs, failed | opened⟩ := openResults got rfl
  · obtain ⟨hne, -, htrace, rfl⟩ := failed
    rw [← hargs] at htrace
    subst htrace
    have mrun := ManifestRun.refused (name := name.data.data.toList) (outputs := outputs) hne
    dsimp only at cont2
    split at cont2
    · rw [cont2.pure]
      exact soFar_of argsRun hone mrun (HandledSoFar.closed .nil) fun _ _ member => nomatch member
    · rename_i bad
      exact absurd (by simpa using hne) bad
  obtain ⟨rfl, small, events, after3, closing, closeErrno, committed, -, htrace, bodyRun,
    hclose⟩ := opened
  obtain ⟨-, bodyFacts⟩ := readManifest_run small hbsize bodyRun
  obtain ⟨bytes, body, -, sbytes, rbuf⟩ := bodyFacts got.1 rfl
  rw [← hargs] at htrace
  subst htrace
  have mrun := ManifestRun.opened (name := name.data.data.toList) (closeErrno := closeErrno)
    (committed := committed) body
  change Stops host (if got.1.1 != 0 then pure got.1.1 else _) after2 post at cont2
  split at cont2
  · rw [cont2.pure]
    exact soFar_of argsRun hone mrun (HandledSoFar.closed .nil) fun _ _ member => nomatch member
  rename_i zero1
  have hz1 : got.1.1 = 0 := by simpa using zero1
  rw [ite_eq_right (by simpa using hz1)] at mrun
  have hbytes := sbytes hz1
  change Stops host (if got.2 != 0 then pure got.2 else _) after2 post at cont2
  split at cont2
  · rw [cont2.pure]
    exact soFar_of argsRun hone mrun (HandledSoFar.closed .nil) fun _ _ member => nomatch member
  rename_i zero2
  have hz2 : closeErrno = 0 := by rw [← hclose]; simpa using zero2
  obtain ⟨hmb, hmsmall⟩ := hbytes
  generalize got.1.2.1 = m at cont2 hmb
  generalize got.1.2.2 = buffer' at cont2 rbuf
  subst hmb
  have hm : m.data.size < 2 ^ 32 := by simpa using hmsmall
  subst hz2
  by_cases acc : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2
  · split at cont2
    · rename_i hsz
      exact absurd (eq_of_beq hsz) (parse_size_ne m hm acc)
    · obtain ⟨handled, opens⟩ := checkLines_stops m hm acc rbuf cont2
      exact soFar_of argsRun hone mrun handled fun arguments reply member =>
        ⟨rfl, opens arguments reply member⟩
  · split at cont2
    · rw [cont2.pure]
      exact soFar_of argsRun hone mrun (HandledSoFar.closed .nil) fun _ _ member => nomatch member
    · rename_i hsz
      rw [parse_refused m hm acc] at hsz
      simp at hsz

/-! ## The runs that stop -/

/-- `ConfinedSoFar` of the events of `Meets` followed by events that open nothing. -/
theorem confined_of_meets {World : Type} {host : Host World} {world : World}
    {events more : List Event} {code : UInt64} (meets : Meets host world events code)
    (noOpen : ∀ arguments reply, Event.sys .pathOpen arguments reply ∉ more) :
    ConfinedSoFar host world (events ++ more) := by
  obtain ⟨a, manifest, ⟨pre, rest, middle, rfl, argsRun, failed, refused, accepted⟩, -, -⟩ :=
    meets
  have preEvents := args_events argsRun
  have plain : rest = [] → ConfinedSoFar host world (pre ++ rest ++ more) := by
    rintro rfl
    refine .inl fun arguments reply member => ?_
    rcases List.mem_append.mp member with member | member
    · rw [List.append_nil] at member
      exact no_open_of_args preEvents arguments reply member
    · exact noOpen arguments reply member
  by_cases hz : a.errno = 0
  · by_cases named : ∃ name, OneArgument a.bytes.data.data.toList name
    · obtain ⟨name, hone⟩ := named
      obtain ⟨opening, post, status, rfl, mrun, stopped, rejected, checked⟩ :=
        accepted hz name hone
      rw [List.append_assoc, List.append_assoc]
      refine confined_of argsRun hone mrun fun arguments reply member => ?_
      rcases List.mem_append.mp member with member | member
      · by_cases zero : status = 0
        · by_cases acc : lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2
          · obtain ⟨l, hl, same⟩ := (checked zero acc.1 acc.2).opens arguments reply member
            obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
            exact ⟨zero, l', hl', same⟩
          · have bad : lines manifest = [] ∨ ∃ l ∈ lines manifest, ¬ WellFormed l.2 := by
              by_cases e : lines manifest = []
              · exact .inl e
              · right
                by_contra hall
                exact acc ⟨e, fun l hl => by_contra fun hn => hall ⟨l, hl, hn⟩⟩
            rw [(rejected zero bad).2] at member
            nomatch member
        · rw [(stopped zero).2] at member
          nomatch member
      · exact absurd member (noOpen arguments reply)
    · exact plain (refused hz fun name hone => named ⟨name, hone⟩).2
  · exact plain (failed hz).2

/-- The events of every run of `main` followed by its exit that stops before the exit, a prefix of
a run or a run that traps, meet `SoFar`. -/
theorem stops_soFar {World : Type} {host : Host World} {world : World} {trace : List Event}
    (h : Stops host (main.bind fun status => Action.exit (α := Unit) status) world trace) :
    SoFar host world trace := by
  rcases h.bind with inside | ⟨status, events, rest, after, rfl, mainRun, exiting⟩
  · exact main_stops inside
  obtain ⟨returned, -⟩ := main_runs mainRun
  obtain ⟨-, meets⟩ := returned status rfl
  have handled : Handled events := by
    obtain ⟨-, -, -, -, handled⟩ := meets
    exact handled
  rcases exiting.exit with rfl | ⟨message, rfl⟩
  · exact ⟨confined_of_meets meets (fun _ _ member => nomatch member),
      ⟨events, [], rfl, handled, .empty⟩⟩
  · exact ⟨confined_of_meets meets (fun _ _ member => by simp at member),
      ⟨events, _, rfl, handled, .exitRejected⟩⟩

/-- The events of every run of `main` followed by its exit that traps, in the host or at an exit
that the host rejects, meet `SoFar`. -/
theorem trapped_soFar {World : Type} {host : Host World} {world final : World}
    {trace : List Event} {message : String}
    (run : Exec host (main.bind fun status => Action.exit (α := Unit) status) world trace
      (.trapped message) final) :
    SoFar host world trace :=
  stops_soFar (.inr ⟨_, _, run⟩)

/-- The events of every prefix of a run of `main` followed by its exit meet `SoFar`. -/
theorem prefix_soFar {World : Type} {host : Host World} {world after : World}
    {trace : List Event} {residual : Action Unit}
    (run : Prefix host (main.bind fun status => Action.exit (α := Unit) status) world trace
      residual after) :
    SoFar host world trace :=
  stops_soFar (.inl ⟨_, _, run⟩)

#print axioms stops_soFar

end Demos.ManifestCheck
