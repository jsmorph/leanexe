module

public import Demos.ManifestCheck.CommandProof
public import Verified.Wasi.Stops

@[expose] public section

/-! The events of every run of the command's `main` followed by its exit that stops without an
accepted exit meet `SoFar` (`stops_soFar`): a prefix of a run, which a trap of the guest cuts short
(`prefix_soFar`), and a run that traps in the host or at an exit that the host rejects
(`trapped_soFar`).

The proof follows `main` with the lemmas of `Verified.Wasi.Stops`: a run of `Action.bind first next`
that stops is a run of `first` that stops, or a run of `first` that returns followed by a run of
`next` that stops.  The parts that return have the events that the run lemmas of the command's
proof give.  A part that stops has only the events that its every call allows (`Every.stops`): the
calls of `args` (`args_every`), the calls on the descriptor of a bracket's body
(`readManifest_every`, `hashFile_every`), and the writes of `writeAll` with at most one rejected
exit at their end, each of which offers the bytes of the output line that the writes before it
did not take (`writeAll_stops`).  `withOpen_stops` gives the events of a bracket that stops, which
write nothing to standard output (`Quiet`), `step_stops` those of a pass of the checks,
`checks_stops` those of their loop, and `checkLines_stops` those of `checkLines`.  Each gives
`LinesSoFar`, which holds the opens, the use of descriptors, and the checks and output lines of
`ChecksSoFar` for the lines that remain.  `main_stops` follows `main`, `confined_of` assembles
`ConfinedSoFar` from the run of `args`, the `ManifestRun`, and the opens that follow, which name
lines of a manifest that the pure core accepts, and `soFar_of` adds `VerdictsSoFar`.  A run that
stops after `main` returned has the events of `Meets`, whose `Checks` give `ChecksSoFar`
(`verdicts_of_meets`). -/

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

/-! ## Events that write nothing -/

theorem Quiet.nil : Quiet [] := fun _ _ member => nomatch member

theorem Quiet.append {first rest : List Event} (h : Quiet first) (more : Quiet rest) :
    Quiet (first ++ rest) := fun offered reply member => by
  rcases List.mem_append.mp member with member | member
  · exact h offered reply member
  · exact more offered reply member

theorem Quiet.cons_sys {call : Call} {args : List Arg} {reply : Transfer (List Bytes)}
    {events : List Event} (h : Quiet events) : Quiet (.sys call args reply :: events) :=
  fun offered reply' member => by
    rcases List.mem_cons.mp member with same | member
    · cases same
    · exact h offered reply' member

theorem Quiet.exitTrap {code : UInt64} {message : String} : Quiet [.exitTrap code message] :=
  fun _ _ member => by cases List.mem_singleton.mp member

theorem Quiet.calls {fd : UInt64} {events : List Event} (calls : ∀ e ∈ events, OnDescriptor fd e) :
    Quiet events := fun offered reply member => by
  rcases calls _ member with ⟨_, _, same⟩ | ⟨_, same⟩ <;> cases same

theorem quiet_of_args {trace : List Event} (h : ∀ e ∈ trace, ∃ call ar rep,
    e = .sys call ar rep ∧ (call = .argsSizesGet ∨ call = .argsGet)) : Quiet trace :=
  fun offered reply member => by
    obtain ⟨_, _, _, same, -⟩ := h _ member
    cases same

theorem ManifestRun.quiet {name : List UInt8} {events : List Event} {status : UInt64}
    {bytes : List UInt8} (h : ManifestRun name events status bytes) : Quiet events := by
  cases h with
  | refused _ => exact Quiet.cons_sys Quiet.nil
  | opened reading =>
    exact (Quiet.cons_sys (Quiet.calls reading.calls)).append (Quiet.cons_sys Quiet.nil)

theorem FileCheck.quiet {name line : List UInt8} {events : List Event} {ok : Bool}
    (h : FileCheck name line events ok) : Quiet events := by
  cases h with
  | refused _ => exact Quiet.cons_sys Quiet.nil
  | opened reads _ =>
    exact (Quiet.cons_sys (Quiet.calls reads.calls)).append (Quiet.cons_sys Quiet.nil)

/-- The checks of `Checks` meet `ChecksSoFar`: a line whose writes stalled or failed is one whose
writes offered the bytes that remained. -/
theorem Checks.soFar {ls : List (List UInt8)} {allOk : Bool} {events : List Event}
    {code : UInt64} (h : Checks ls allOk events code) : ChecksSoFar ls events := by
  induction h with
  | done => exact .none
  | line check wrote _ ih => exact .line check wrote ih
  | stalled check wrote => exact .writing check wrote.1 wrote.2.2.1
  | failed check wrote => exact .writing check wrote.1 wrote.2.2.1

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

/-- `Every (OnDescriptor fd)` holds of `readManifest` on the descriptor `fd`: every event that it
makes, for every reply, is a call on `fd`. -/
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

/-- `Every (OnDescriptor fd)` holds of `hashFile` on the descriptor `fd`: every event that it
makes, for every reply, is a call on `fd`. -/
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
rights `rights`, around an error continuation that returns `fallback errno` and a body of which
`Every (OnDescriptor fd)` holds on every descriptor `fd`, makes the events of `HandledSoFar`, and
every open among them has the arguments `openArgs rights` of `name`.  No event among them writes
to standard output. -/
theorem withOpen_stops {World α : Type} {host : Host World} {name : Bytes} {rights : UInt64}
    {fallback : UInt64 → α} {body : Handle → Action α}
    (calls : ∀ fd, Every (OnDescriptor fd) (body ⟨fd⟩)) {world : World} {trace : List Event}
    (h : Stops host (withOpen .preopened 1 name 0 rights 0 0 (fun errno => pure (fallback errno))
      body) world trace) :
    HandledSoFar trace ∧ (∀ arguments reply, Event.sys .pathOpen arguments reply ∈ trace →
      arguments = openArgs rights name.data.data.toList) ∧ Quiet trace := by
  rw [openArgs_bytes]
  unfold withOpen at h
  rcases h.sys with rfl | ⟨rejected, fallen⟩ | ⟨errno, outputs, after, rest, rfl, opened⟩ |
      ⟨message, committed, rfl⟩
  · exact ⟨HandledSoFar.closed .nil, (fun _ _ member => nomatch member), Quiet.nil⟩
  · simp only [bne_iff_ne, ne_eq, rejected, not_false_eq_true, ↓reduceIte] at fallen
    rw [fallen.pure]
    exact ⟨HandledSoFar.closed .nil, (fun _ _ member => nomatch member), Quiet.nil⟩
  · by_cases zero : errno = 0
    · subst zero
      have hReply : sysReply 0 outputs = ⟨0, outputs⟩ := rfl
      simp only [hReply, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at opened
      rcases opened.bind with inside | ⟨value, done, last, between, rfl, bodyRun, closing⟩
      · have inner := Every.stops _ (calls _) inside
        exact ⟨⟨[], _, rfl, .nil, .opened inner⟩, only_open (OnDescriptor.no_open inner),
          Quiet.cons_sys (Quiet.calls inner)⟩
      · have inner := Every.returns (calls _) bodyRun
        have none := OnDescriptor.no_open inner
        have quiet := Quiet.calls inner
        rcases closing.sys with rfl | ⟨_, fallen⟩ | ⟨closeErrno, closed, after, tail, rfl, ended⟩ |
            ⟨message, closed, rfl⟩
        · rw [List.append_nil]
          exact ⟨⟨[], _, rfl, .nil, .opened inner⟩, only_open none, Quiet.cons_sys quiet⟩
        · rw [fallen.pure, List.append_nil]
          exact ⟨⟨[], _, rfl, .nil, .opened inner⟩, only_open none, Quiet.cons_sys quiet⟩
        · rw [ended.pure]
          exact ⟨HandledSoFar.closed (.bracket inner .nil), only_open (no_open_close none),
            Quiet.cons_sys (quiet.append (Quiet.cons_sys Quiet.nil))⟩
        · exact ⟨HandledSoFar.closed (.bracket inner .nil), only_open (no_open_close none),
            Quiet.cons_sys (quiet.append (Quiet.cons_sys Quiet.nil))⟩
    · have hReply : sysReply errno outputs = ⟨errno, []⟩ := by simp [sysReply, zero]
      have off : ((errno != 0) = true) = True := eq_true (bne_iff_ne.mpr zero)
      simp only [hReply, off, ↓reduceIte] at opened
      rw [opened.pure]
      exact ⟨⟨[_], [], rfl, .refused zero .nil, .empty⟩,
        only_open (fun _ _ member => nomatch member), Quiet.cons_sys Quiet.nil⟩
  · exact ⟨⟨[], _, rfl, .nil, .openTrapped⟩, only_open (fun _ _ member => nomatch member),
      Quiet.cons_sys Quiet.nil⟩

/-! ## The checks -/

/-- The events of a run that stopped of the checks of the lines `ls` of the manifest's bytes `m`:
those of `HandledSoFar`, every open has the arguments `openArgs fileRights` of the name of a line of
`m`, and the events are those of `ChecksSoFar ls` followed by events that write nothing to standard
output. -/
def LinesSoFar (m : List UInt8) (ls : List (List UInt8)) (events : List Event) : Prop :=
  HandledSoFar events ∧ (∀ arguments reply, Event.sys .pathOpen arguments reply ∈ events →
    ∃ l ∈ lines m, arguments = openArgs fileRights (l.2.drop 66)) ∧
  ∃ checked tail, events = checked ++ tail ∧ ChecksSoFar ls checked ∧ Quiet tail

/-- Events that write nothing to standard output meet `LinesSoFar` when they meet its first two
parts. -/
theorem LinesSoFar.quiet {m : List UInt8} {ls : List (List UInt8)} {events : List Event}
    (handled : HandledSoFar events)
    (opens : ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ events →
      ∃ l ∈ lines m, arguments = openArgs fileRights (l.2.drop 66))
    (quiet : Quiet events) : LinesSoFar m ls events :=
  ⟨handled, opens, [], events, rfl, .none, quiet⟩

theorem LinesSoFar.nil {m : List UInt8} {ls : List (List UInt8)} : LinesSoFar m ls [] :=
  LinesSoFar.quiet (HandledSoFar.closed .nil) (fun _ _ member => nomatch member) Quiet.nil

/-- The check of a line `p` of `m` whose writes took its whole output line, followed by events of
`LinesSoFar` for the lines `ls`, meets `LinesSoFar` for `p.2 :: ls`. -/
theorem LinesSoFar.line {m : List UInt8} {p : Nat × List UInt8} {ls : List (List UInt8)}
    {ok : Bool} {fileEvents writes events : List Event} (member : p ∈ lines m)
    (check : FileCheck (p.2.drop 66) p.2 fileEvents ok)
    (wrote : LineWrites (lineText (p.2.drop 66) ok) writes .all) (rest : LinesSoFar m ls events) :
    LinesSoFar m (p.2 :: ls) (fileEvents ++ writes ++ events) := by
  obtain ⟨handled, opens, checked, tail, rfl, checks, quiet⟩ := rest
  refine ⟨(check.handled.append (Handled.writes wrote.2.2.1)).soFar handled,
    fun arguments reply member' => ?_, fileEvents ++ writes ++ checked, tail, by simp,
    .line check wrote checks, quiet⟩
  rcases List.mem_append.mp member' with member' | member'
  · rcases List.mem_append.mp member' with member' | member'
    · exact ⟨p, member, check.opens arguments reply member'⟩
    · exact absurd member' (wrote.no_open arguments reply)
  · exact opens arguments reply member'

/-- The check of a line `p` of `m` followed by writes that offer at least one byte each, the bytes
of its output line after those that the writes before them took, and by no event or an exit that
the host rejected, meets `LinesSoFar` for `p.2 :: ls`. -/
theorem LinesSoFar.writing {m : List UInt8} {p : Nat × List UInt8} {ls : List (List UInt8)}
    {ok : Bool} {fileEvents writes tail : List Event} (member : p ∈ lines m)
    (check : FileCheck (p.2.drop 66) p.2 fileEvents ok)
    (offered : Offered (lineText (p.2.drop 66) ok) 0 writes) (some : ∀ e ∈ writes, WroteSome e)
    (ended : tail = [] ∨ ∃ code message, tail = [.exitTrap code message]) :
    LinesSoFar m (p.2 :: ls) (fileEvents ++ (writes ++ tail)) := by
  have handled : HandledSoFar (writes ++ tail) := by
    rcases ended with rfl | ⟨code, message, rfl⟩
    · rw [List.append_nil]
      exact HandledSoFar.closed (Handled.writes some)
    · exact ⟨writes, _, rfl, Handled.writes some, .exitRejected⟩
  have quiet : Quiet tail := by
    rcases ended with rfl | ⟨code, message, rfl⟩
    · exact Quiet.nil
    · exact Quiet.exitTrap
  refine ⟨check.handled.soFar handled, fun arguments reply member' => ?_, fileEvents ++ writes,
    tail, by simp, .writing check offered some, quiet⟩
  rcases List.mem_append.mp member' with member' | member'
  · exact ⟨p, member, check.opens arguments reply member'⟩
  rcases List.mem_append.mp member' with member' | member'
  · obtain ⟨_, _, same, -⟩ := some _ member'
    cases same
  · rcases ended with rfl | ⟨code, message, rfl⟩
    · nomatch member'
    · cases List.mem_singleton.mp member'

/-- The output line of a name of fewer than `2^32` bytes holds the bytes of `lineText` of the name,
and fewer than `2^33` of them. -/
theorem render_line (name : Bytes) (hn : name.data.size < 2 ^ 32) (ok : Bool) :
    (render name ok).data.data.toList = lineText name.data.data.toList ok ∧
      (render name ok).data.size < 2 ^ 33 := by
  refine ⟨by rw [render_eq name ok (by omega), lineText, bytesOf_toList], ?_⟩
  have h1 : (render name ok).data.size = (name.size + if ok then 5 else 9).toNat := by
    unfold render
    exact build_size _ _
  have h2 : name.size.toNat = name.data.size := Bytes.size_toNat name (by omega)
  rw [h1, UInt64.toNat_add, h2]
  cases ok <;> simp <;> omega

/-- A run that stops of the pass of `checkLines` on line `j` of a manifest of fewer than `2^32`
bytes that the pure core accepts, from a state with a read buffer of 65,536 bytes and writes that
have not stalled, makes the events of `LinesSoFar` for the lines from line `j`. -/
theorem step_stops {World : Type} {host : Host World} (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2)
    (j : Nat) (hj : j < (lines m.data.data.toList).length) {buffer : Bytes}
    (hsize : buffer.data.size = 65536) (failed : UInt64) {world : World} {trace : List Event}
    (h : Stops host (checkStep m (parse m) (UInt64.ofNat j) (buffer, failed, 0)) world trace) :
    LinesSoFar m.data.data.toList (((lines m.data.data.toList).drop j).map (·.2)) trace := by
  have hlsmall := lines_length m.data.data.toList
  have hlenm : m.data.data.toList.length = m.data.size := by simp
  have hparse := parse_accepted m hm accepted
  have hmem : (lines m.data.data.toList)[j] ∈ lines m.data.data.toList := List.getElem_mem hj
  rw [List.drop_eq_getElem_cons hj, List.map_cons]
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
  obtain ⟨hname, hnsize⟩ := entry_name m hm ls[j].1 (ls[j].1 + ls[j].2.length) (by omega)
    (by omega) hline
  rw [hl] at hname
  unfold checkStep at h
  rw [hparse, hstart, hstop] at h
  dsimp only at h
  rcases h.bind with inside | ⟨r, first, rest, after, rfl, checkRun, writing⟩
  · obtain ⟨handled, opens, quiet⟩ := withOpen_stops (body := fun file => hashFile file buffer)
      (fun fd => hashFile_every fd buffer) inside
    refine LinesSoFar.quiet handled (fun arguments reply member => ⟨ls[j], hin, ?_⟩) quiet
    rw [opens arguments reply member, hname, fileRights]
  · obtain ⟨-, -, results⟩ := entry_check m hm ls[j].1 (ls[j].1 + ls[j].2.length) (by omega)
      (by omega) hline hsize checkRun
    obtain ⟨-, check⟩ := results r rfl
    rw [hl] at check
    generalize slice m (UInt64.ofNat ls[j].1 + 66)
      (UInt64.ofNat (ls[j].1 + ls[j].2.length) - UInt64.ofNat ls[j].1 - 66) = name
      at hname hnsize writing
    generalize (r.1.2.1 == 1 && r.2 == 0 && hexMatches m (UInt64.ofNat ls[j].1) r.1.1) = ok
      at check writing
    obtain ⟨text, tsize⟩ := render_line name hnsize ok
    have finish : ∀ {events : List Event},
        Stops host (writeAll (render name ok) 0 (render name ok).size) after events →
        LinesSoFar m.data.data.toList (ls[j].2 :: (ls.drop (j + 1)).map (·.2))
          (first ++ events) := by
      intro events stops
      obtain ⟨writes, shape, offered, some⟩ := writeAll_stops (by omega) stops
      rw [Bytes.range_zero_size _ (by omega), text, hname] at offered
      rcases shape with rfl | ⟨code, message, rfl⟩
      · have done := LinesSoFar.writing (ls := (ls.drop (j + 1)).map (·.2)) (tail := []) hin
          check offered some (.inl rfl)
        rwa [List.append_nil] at done
      · exact LinesSoFar.writing hin check offered some (.inr ⟨code, message, rfl⟩)
    rcases writing.bind with inside | ⟨v, writes, last, after', rfl, writeRun, ended⟩
    · exact finish inside
    · rw [ended.pure, List.append_nil]
      exact finish (.inl ⟨_, _, Exec.returned_prefix _ writeRun⟩)

/-- A run that stops of a loop whose test is that of `checkLines`, `s.2.2 == 0`, from a state whose
writes stalled, `s.2.2 = 1`, makes no event, whatever its step. -/
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

/-- A run that stops of the loop of `checkLines`, with its test and its step, on a manifest of
fewer than `2^32` bytes that the pure core accepts, from line `j` with the passes for the lines that
remain and a state with a read buffer of 65,536 bytes and writes that have not stalled, makes the
events of `LinesSoFar` for the lines from line `j`. -/
theorem checks_stops {World : Type} {host : Host World} (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2)
    {test : UInt64 → CheckState → Bool} {step : UInt64 → CheckState → Action CheckState}
    (tested : ∀ i s, test i s = (s.2.2 == 0))
    (stepped : ∀ i s, step i s = checkStep m (parse m) i s) :
    ∀ (remaining j : Nat) (buffer : Bytes) (failed : UInt64) {world : World}
      {trace : List Event},
      j + remaining = (lines m.data.data.toList).length → buffer.data.size = 65536 →
      Stops host (resumeLoop test step .pure remaining j (buffer, failed, 0)) world trace →
      LinesSoFar m.data.data.toList (((lines m.data.data.toList).drop j).map (·.2)) trace
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
      rw [List.drop_eq_getElem_cons hjl, List.map_cons]
      rcases ending with ⟨rfl, lw⟩ | ⟨rfl, lw⟩
      · exact LinesSoFar.line (List.getElem_mem hjl) check lw
          (checks_stops m hm accepted tested stepped remaining (j + 1) buffer' _ (by omega) hbuf
            more)
      · rw [stalled_stops tested more, List.append_nil]
        have done := LinesSoFar.writing (ls := ((lines m.data.data.toList).drop (j + 1)).map (·.2))
          (tail := []) (List.getElem_mem hjl) check lw.1 lw.2.2.1 (.inl rfl)
        rwa [List.append_nil] at done

/-- A run that stops of `checkLines` on a manifest of fewer than `2^32` bytes that the pure core
accepts, with a read buffer of 65,536 bytes, makes the events of `LinesSoFar` for the manifest's
lines. -/
theorem checkLines_stops {World : Type} {host : Host World} (m : Bytes)
    (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2)
    {buffer : Bytes} (hsize : buffer.data.size = 65536) {world : World} {trace : List Event}
    (h : Stops host (checkLines m (parse m) buffer) world trace) :
    LinesSoFar m.data.data.toList ((lines m.data.data.toList).map (·.2)) trace := by
  unfold checkLines at h
  rcases h.bind with inside | ⟨s, done, rest, between, rfl, loopRun, ending⟩
  · have passes := inside.loop
    rw [parse_passes m hm accepted] at passes
    have lsf := checks_stops m hm accepted (fun _ _ => rfl) (fun _ _ => rfl) _ 0 buffer 0
      (by simp) hsize passes
    rwa [List.drop_zero] at lsf
  · cases loopRun with
    | loop loopRun =>
      rw [parse_passes m hm accepted] at loopRun
      obtain ⟨returned, -⟩ := checks_loop m hm accepted (fun _ _ => rfl) (fun _ _ => rfl) _ 0
        buffer 0 (by simp) hsize (.inl rfl) loopRun
      have checks := returned s rfl
      rw [List.drop_zero] at checks
      have empty : rest = [] := by
        split at ending <;> exact ending.pure
      subst empty
      rw [List.append_nil]
      refine ⟨HandledSoFar.closed checks.handled, fun arguments reply member => ?_, done, [],
        (List.append_nil _).symm, checks.soFar, Quiet.nil⟩
      obtain ⟨l, hl, same⟩ := checks.opens arguments reply member
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      exact ⟨l', hl', same⟩

/-! ## `main` -/

/-- The events of `args` alone meet `SoFar`. -/
theorem soFar_args {World : Type} {host : Host World} {world : World} {trace : List Event}
    (calls : ∀ e ∈ trace, ∃ call ar rep, e = .sys call ar rep ∧
      (call = .argsSizesGet ∨ call = .argsGet)) :
    SoFar host world trace :=
  ⟨.inl (no_open_of_args calls), HandledSoFar.closed (handled_of_args calls),
    .inl (quiet_of_args calls)⟩

/-- `ConfinedSoFar` of the events of a run of `args` whose buffer holds one argument, `name`,
those of a `ManifestRun` of `name` with the status `status` and the bytes `manifest`, and events
whose every open names a line of `manifest` after a status of 0 and a manifest that the pure core
accepts. -/
theorem confined_of {World : Type} {host : Host World} {world after : World} {a : ArgsResult}
    {pre opening post : List Event} {name manifest : List UInt8} {status : UInt64}
    (argsRun : Exec host args world pre (.returned a) after)
    (hone : OneArgument a.bytes.data.data.toList name)
    (mrun : ManifestRun name opening status manifest)
    (opens : ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ post →
      status = 0 ∧ (lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2) ∧
        ∃ l ∈ lines manifest, arguments = openArgs fileRights (l.2.drop 66)) :
    ConfinedSoFar host world (pre ++ (opening ++ post)) := by
  have preEvents := args_events argsRun
  have early : ∀ (bytes : List UInt8) arguments reply,
      Event.sys .pathOpen arguments reply ∈ pre ++ opening →
      ∃ n, (arguments = openArgs manifestRights n ∧ OneArgument a.bytes.data.data.toList n) ∨
        (arguments = openArgs fileRights n ∧ ∃ l ∈ lines bytes, WellFormed l.2 ∧
          n = l.2.drop 66) := by
    intro bytes arguments reply member
    rcases List.mem_append.mp member with member | member
    · exact absurd member (no_open_of_args preEvents arguments reply)
    · exact ⟨name, .inl ⟨mrun.opens arguments reply member, hone⟩⟩
  by_cases good : status = 0 ∧ lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2
  · obtain ⟨rfl, nonempty, formed⟩ := good
    refine .inr ⟨a, pre, opening ++ post, after, manifest, rfl, argsRun,
      .inr ⟨name, opening, post, rfl, mrun, nonempty, formed⟩, fun arguments reply member => ?_⟩
    rw [← List.append_assoc] at member
    rcases List.mem_append.mp member with member | member
    · exact early manifest arguments reply member
    · obtain ⟨-, -, l, hl, same⟩ := opens arguments reply member
      exact ⟨l.2.drop 66, .inr ⟨same, l, hl, formed l hl, rfl⟩⟩
  · refine .inr ⟨a, pre, opening ++ post, after, [], rfl, argsRun, .inl rfl,
      fun arguments reply member => ?_⟩
    rw [← List.append_assoc] at member
    rcases List.mem_append.mp member with member | member
    · exact early [] arguments reply member
    · obtain ⟨zero, accepted, -⟩ := opens arguments reply member
      exact absurd ⟨zero, accepted⟩ good

/-- `SoFar` of the events of `confined_of` whose last part meets `HandledSoFar` and either writes
nothing to standard output or, after a status of 0 and a manifest that the pure core accepts, holds
the events of `ChecksSoFar` for the manifest's lines followed by events that write nothing to
standard output. -/
theorem soFar_of {World : Type} {host : Host World} {world after : World} {a : ArgsResult}
    {pre opening post : List Event} {name manifest : List UInt8} {status : UInt64}
    (argsRun : Exec host args world pre (.returned a) after)
    (hone : OneArgument a.bytes.data.data.toList name)
    (mrun : ManifestRun name opening status manifest) (handled : HandledSoFar post)
    (opens : ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ post →
      status = 0 ∧ (lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2) ∧
        ∃ l ∈ lines manifest, arguments = openArgs fileRights (l.2.drop 66))
    (verdicts : Quiet post ∨ status = 0 ∧
      (lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2) ∧
      ∃ checked tail, post = checked ++ tail ∧ ChecksSoFar ((lines manifest).map (·.2)) checked ∧
        Quiet tail) :
    SoFar host world (pre ++ (opening ++ post)) := by
  refine ⟨confined_of argsRun hone mrun opens,
    (handled_of_args (args_events argsRun)).soFar (mrun.handled.soFar handled), ?_⟩
  have early : Quiet (pre ++ opening) :=
    (quiet_of_args (args_events argsRun)).append mrun.quiet
  rcases verdicts with quiet | ⟨rfl, accepted, checked, tail, rfl, checks, quiet⟩
  · rw [← List.append_assoc]
    exact .inl (early.append quiet)
  · exact .inr ⟨a, pre, after, name, opening, manifest, checked, tail, by simp, argsRun, hone,
      mrun, accepted.1, accepted.2, checks, quiet⟩

/-- `SoFar` of the events of a run of `args` whose buffer holds one argument, `name`, followed by
events of `HandledSoFar` that write nothing to standard output and whose every open names `name`
with the rights `manifestRights`. -/
theorem soFar_opening {World : Type} {host : Host World} {world after : World} {a : ArgsResult}
    {pre rest : List Event} {name : List UInt8}
    (argsRun : Exec host args world pre (.returned a) after)
    (hone : OneArgument a.bytes.data.data.toList name) (handled : HandledSoFar rest)
    (opens : ∀ arguments reply, Event.sys .pathOpen arguments reply ∈ rest →
      arguments = openArgs manifestRights name) (quiet : Quiet rest) :
    SoFar host world (pre ++ rest) := by
  have preEvents := args_events argsRun
  refine ⟨.inr ⟨a, pre, rest, after, [], rfl, argsRun, .inl rfl, fun arguments reply member => ?_⟩,
    (handled_of_args preEvents).soFar handled, .inl ((quiet_of_args preEvents).append quiet)⟩
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
  · obtain ⟨handled, opens, quiet⟩ := withOpen_stops
      (body := fun file => readManifest file buffer) (fun fd => readManifest_every fd buffer) inside
    exact soFar_opening argsRun hone handled opens quiet
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
      exact soFar_of argsRun hone mrun (HandledSoFar.closed .nil)
        (fun _ _ member => nomatch member) (.inl Quiet.nil)
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
    exact soFar_of argsRun hone mrun (HandledSoFar.closed .nil)
      (fun _ _ member => nomatch member) (.inl Quiet.nil)
  rename_i zero1
  have hz1 : got.1.1 = 0 := by simpa using zero1
  rw [ite_eq_right (by simpa using hz1)] at mrun
  have hbytes := sbytes hz1
  change Stops host (if got.2 != 0 then pure got.2 else _) after2 post at cont2
  split at cont2
  · rw [cont2.pure]
    exact soFar_of argsRun hone mrun (HandledSoFar.closed .nil)
      (fun _ _ member => nomatch member) (.inl Quiet.nil)
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
    · obtain ⟨handled, opens, checked⟩ := checkLines_stops m hm acc rbuf cont2
      exact soFar_of argsRun hone mrun handled
        (fun arguments reply member => ⟨rfl, acc, opens arguments reply member⟩)
        (.inr ⟨rfl, acc, checked⟩)
  · split at cont2
    · rw [cont2.pure]
      exact soFar_of argsRun hone mrun (HandledSoFar.closed .nil)
        (fun _ _ member => nomatch member) (.inl Quiet.nil)
    · rename_i hsz
      rw [parse_refused m hm acc] at hsz
      simp at hsz

/-! ## The runs that stop -/

/-- A manifest that the pure core refuses has no line or a line outside the format. -/
theorem refused_of_not {manifest : List UInt8}
    (h : ¬ (lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2)) :
    lines manifest = [] ∨ ∃ l ∈ lines manifest, ¬ WellFormed l.2 := by
  by_cases e : lines manifest = []
  · exact .inl e
  · right
    by_contra hall
    exact h ⟨e, fun l hl => by_contra fun hn => hall ⟨l, hl, hn⟩⟩

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
            exact ⟨zero, acc, l', hl', same⟩
          · rw [(rejected zero (refused_of_not acc)).2] at member
            nomatch member
        · rw [(stopped zero).2] at member
          nomatch member
      · exact absurd member (noOpen arguments reply)
    · exact plain (refused hz fun name hone => named ⟨name, hone⟩).2
  · exact plain (failed hz).2

/-- `VerdictsSoFar` of the events of `Meets` followed by events that write nothing to standard
output. -/
theorem verdicts_of_meets {World : Type} {host : Host World} {world : World}
    {events more : List Event} {code : UInt64} (meets : Meets host world events code)
    (quiet : Quiet more) : VerdictsSoFar host world (events ++ more) := by
  obtain ⟨a, manifest, ⟨pre, rest, middle, rfl, argsRun, failed, refused, accepted⟩, -, -⟩ :=
    meets
  have preQuiet := quiet_of_args (args_events argsRun)
  have plain : ∀ {events : List Event}, Quiet events →
      VerdictsSoFar host world (pre ++ events ++ more) :=
    fun restQuiet => .inl ((preQuiet.append restQuiet).append quiet)
  by_cases hz : a.errno = 0
  · by_cases named : ∃ name, OneArgument a.bytes.data.data.toList name
    · obtain ⟨name, hone⟩ := named
      obtain ⟨opening, post, status, rfl, mrun, stopped, rejected, checked⟩ :=
        accepted hz name hone
      by_cases zero : status = 0
      · subst zero
        by_cases acc : lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2
        · exact .inr ⟨a, pre, middle, name, opening, manifest, post, more, by simp, argsRun,
            hone, mrun, acc.1, acc.2, (checked rfl acc.1 acc.2).soFar, quiet⟩
        · rw [(rejected rfl (refused_of_not acc)).2, List.append_nil]
          exact plain mrun.quiet
      · rw [(stopped zero).2, List.append_nil]
        exact plain mrun.quiet
    · rw [(refused hz fun name hone => named ⟨name, hone⟩).2]
      exact plain Quiet.nil
  · rw [(failed hz).2]
    exact plain Quiet.nil

/-- The events of every run of `main` followed by its exit that stops without an accepted exit, a
prefix of a run or a run that traps, meet `SoFar`. -/
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
      ⟨events, [], rfl, handled, .empty⟩, verdicts_of_meets meets Quiet.nil⟩
  · exact ⟨confined_of_meets meets (fun _ _ member => by simp at member),
      ⟨events, _, rfl, handled, .exitRejected⟩, verdicts_of_meets meets Quiet.exitTrap⟩

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
