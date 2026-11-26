module

public import LeanExe.Wasi.Semantics

@[expose] public section

/-! `writeAll buffer start count` writes the bytes of the window of `buffer` that `start` and
`count` name to standard output with a loop of at most the window's length plus one passes.  It
computes the window's first position and length as words, as `Bytes.window` states them.  Each
pass that finds bytes left writes the window of the same buffer that starts `written` bytes past
the first position and holds the bytes that remain, and adds the count that the write returned to
`written`, so a short write is followed by a write of the rest while passes remain.  No pass copies
the buffer.  A write that returns an errno ends the run with the exit of that errno.  The loop
returns the number of bytes that the writes took, which falls short of the window's length only
when the passes run out.

`WriteAllRun host bytes written passes events outcome` states the events and the outcome of every
run of the loop under `host` over the bytes `bytes` from `written` bytes taken with `passes`
passes left, and `writeAll_run` proves it of every run of `writeAll buffer start count` over a
buffer of fewer than `2^64 - 1` bytes, over the window's bytes from 0 with the window's length plus
one passes.  `writeAll_run_whole` states the case of the whole buffer, a start of 0 and a count of
its size.  `stdoutTaken` collects the bytes that the writes of a trace to standard output took when
they returned errno 0, and `Offered bytes taken events` states that each event is a write to
standard output that offered the bytes of `bytes` after the first `taken` and those that the
writes before it took.  `WroteSome e` states that the event `e` is a write to standard output that
offered at least one byte, and `WriteAllRun.shape` states that every write of a run that returns
or exits is one, since a pass writes only while bytes remain, and that the writes number at most
the passes.  `WriteAllRun.taken` states, for fewer than `2^64` bytes, that a run that returns
`value` made writes that each returned errno 0, offered the bytes that remained, and took the
bytes from `written` up to `value`, one write for each pass when `value` falls short of the bytes.
A run that exits does so with the errno, from 1 to 76, of its last write, after taking fewer than
the bytes from `written` on.  `WriteAllRun.trapped_write` states that a run that traps under a
host that rejects no exit status below 126 has a trapped write. -/

namespace LeanExe.Wasi

/-- Writes the bytes of the window of `buffer` that `start` and `count` name to stdout, continuing
after short writes, and exits with the errno of a write that fails. -/
def writeAll (buffer : Bytes) (start count : UInt64) : Action UInt64 :=
  let first := min start buffer.size
  let length := min count (buffer.size - first)
  loop (length + 1) 0 (fun _ written => written < length) fun _ written => do
    let reply ← writeStdout buffer (first + written) (length - written)
    if reply.errno != 0 then exit reply.errno else pure (written + reply.count)

/-- The bytes that the event `e` took as a write to standard output: the first bytes that it
offered, as many as its count, when it returned errno 0, and none otherwise. -/
def Event.stdoutTaken : Event → List UInt8
  | .write .stdout offered (.returned errno count) =>
    if errno = 0 then offered.data.data.toList.take count.toNat else []
  | _ => []

/-- The bytes that the writes of `events` to standard output took, in order. -/
def stdoutTaken (events : List Event) : List UInt8 := events.flatMap Event.stdoutTaken

@[simp] theorem stdoutTaken_nil : stdoutTaken [] = [] := rfl

@[simp] theorem stdoutTaken_cons (e : Event) (events : List Event) :
    stdoutTaken (e :: events) = e.stdoutTaken ++ stdoutTaken events := List.flatMap_cons

theorem stdoutTaken_append (first rest : List Event) :
    stdoutTaken (first ++ rest) = stdoutTaken first ++ stdoutTaken rest := List.flatMap_append

/-- `Offered bytes taken events`: each event of `events` is a write to standard output that
offered the bytes of `bytes` after the first `taken` and those that the writes before it took. -/
def Offered (bytes : List UInt8) : Nat → List Event → Prop
  | _, [] => True
  | taken, e :: rest => (∃ offered reply, e = .write .stdout offered reply ∧
      offered.data.data.toList = bytes.drop taken) ∧
    Offered bytes (taken + e.stdoutTaken.length) rest

/-- The event `e` is a write to standard output that offered at least one byte. -/
def WroteSome (e : Event) : Prop :=
  ∃ offered reply, e = .write .stdout offered reply ∧ offered.data.size ≠ 0

/-- The runs of the loop of `writeAll` under `host` over the bytes `bytes` from `written` bytes
taken with `passes` passes left: their events and outcomes.  The loop returns `written` when no
byte is left or no pass is.  Otherwise a pass offers the bytes from `written` on: a write that
returns errno 0 and a count of at most those bytes continues the loop with the count added, a
write that returns another errno, at most 76, ends the run with a run of the exit of that errno,
and a write that traps ends the run with the trap. -/
inductive WriteAllRun {World : Type} (host : Host World) (bytes : List UInt8) :
    UInt64 → Nat → List Event → Outcome UInt64 → Prop
  | done {written : UInt64} {passes : Nat} (ended : bytes.length ≤ written.toNat) :
      WriteAllRun host bytes written passes [] (.returned written)
  | spent {written : UInt64} (left : written.toNat < bytes.length) :
      WriteAllRun host bytes written 0 [] (.returned written)
  | wrote {written count : UInt64} {passes : Nat} {offered : Bytes} {events : List Event}
      {outcome : Outcome UInt64} (left : written.toNat < bytes.length)
      (offers : offered.data.data.toList = bytes.drop written.toNat)
      (within : count.toNat ≤ bytes.length - written.toNat)
      (rest : WriteAllRun host bytes (written + count) passes events outcome) :
      WriteAllRun host bytes written (passes + 1)
        (.write .stdout offered (.returned 0 count) :: events) outcome
  | failed {written errno count : UInt64} {passes : Nat} {offered : Bytes} {events : List Event}
      {outcome : Outcome UInt64} (left : written.toNat < bytes.length)
      (offers : offered.data.data.toList = bytes.drop written.toNat) (nonzero : errno ≠ 0)
      (valid : errno.toNat ≤ 76)
      (ended : ∃ world final, Exec host (Action.exit errno) world events outcome final) :
      WriteAllRun host bytes written (passes + 1)
        (.write .stdout offered (.returned errno count) :: events) outcome
  | trapped {written : UInt64} {passes : Nat} {offered : Bytes} {message : String}
      {committed : UInt64} (left : written.toNat < bytes.length)
      (offers : offered.data.data.toList = bytes.drop written.toNat) :
      WriteAllRun host bytes written (passes + 1)
        [.write .stdout offered (.trapped message committed)] (.trapped message)

/-- Every run of the loop of `writeAll buffer start count` from `written` bytes taken, at most the
window's length, meets `WriteAllRun` over the window's bytes. -/
theorem writeAll_loop_run {World : Type} {host : Host World} (buffer : Bytes) (start count : UInt64)
    (small : buffer.data.size < 2 ^ 64) {test : UInt64 → UInt64 → Bool}
    {step : UInt64 → UInt64 → Action UInt64}
    (tested : ∀ index written, test index written =
      decide (written < min count (buffer.size - min start buffer.size)))
    (stepped : ∀ index written, step index written =
      .write .stdout (buffer.range (min start buffer.size + written)
        (min count (buffer.size - min start buffer.size) - written)) fun reply =>
        if reply.errno != 0 then exit reply.errno else .pure (written + reply.count)) :
    ∀ (remaining index : Nat) (written : UInt64) {world trace outcome final},
      written.toNat ≤ (buffer.window start count).2 →
      LoopExec host remaining index written test step .pure world trace outcome final →
      WriteAllRun host (buffer.range start count).data.data.toList written remaining trace outcome
  | 0, _, written, _, _, _, _, _, execution => by
    cases execution with
    | zero next =>
      cases next
      by_cases ended : (buffer.range start count).data.data.toList.length ≤ written.toNat
      · exact .done ended
      · exact .spent (by omega)
  | remaining + 1, index, written, _, _, _, _, le, execution => by
    have hLength := (buffer.window_of_words small start count).2
    have hWindow := buffer.window_le start count
    have length : (buffer.range start count).data.data.toList.length =
        (buffer.window start count).2 := by
      simp
    have offers := buffer.range_after small le
    have offered : (buffer.range (min start buffer.size + written)
        (min count (buffer.size - min start buffer.size) - written)).data.size =
          (buffer.window start count).2 - written.toNat := by
      have := congrArg List.length offers
      simpa [length] using this
    cases execution with
    | stop test next =>
      cases next
      rw [tested] at test
      refine .done ?_
      simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, hLength] at test
      omega
    | next test step rest =>
      rw [tested] at test
      have left : written.toNat < (buffer.window start count).2 := by
        simpa [UInt64.lt_iff_toNat_lt, hLength] using test
      rw [stepped] at step
      cases step with
      | @write_return _ _ _ _ _ _ _ _ _ errno committed reply next =>
        by_cases zero : errno = 0
        · subst zero
          simp only [writeResult, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true] at next
          cases next
          have bound := (host.write_bound reply).1
          simp only [Transfer.committed, offered] at bound
          have sum : (written + committed).toNat = written.toNat + committed.toNat := by
            rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
          exact .wrote (by omega) offers (by omega)
            (writeAll_loop_run buffer start count small tested stepped remaining (index + 1)
              (written + committed) (by omega) rest)
        · have failing : ((writeResult errno committed).errno != 0) = true := by
            simp [writeResult, zero]
          dsimp only at next
          rw [ite_eq_left failing] at next
          cases next
    | exit test step =>
      rw [tested] at test
      have left : written.toNat < (buffer.window start count).2 := by
        simpa [UInt64.lt_iff_toNat_lt, hLength] using test
      rw [stepped] at step
      cases step with
      | @write_return _ _ _ _ _ _ _ _ _ errno committed reply next =>
        by_cases zero : errno = 0
        · subst zero
          simp only [writeResult, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true] at next
          cases next
        · have failing : ((writeResult errno committed).errno != 0) = true := by
            simp [writeResult, zero]
          dsimp only at next
          rw [ite_eq_left failing] at next
          exact .failed (by omega) offers zero (host.write_bound reply).2 ⟨_, _, next⟩
    | trap test step =>
      rw [tested] at test
      have left : written.toNat < (buffer.window start count).2 := by
        simpa [UInt64.lt_iff_toNat_lt, hLength] using test
      rw [stepped] at step
      cases step with
      | @write_return _ _ _ _ _ _ _ _ _ errno committed reply next =>
        by_cases zero : errno = 0
        · subst zero
          simp only [writeResult, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true] at next
          cases next
        · have failing : ((writeResult errno committed).errno != 0) = true := by
            simp [writeResult, zero]
          dsimp only at next
          rw [ite_eq_left failing] at next
          exact .failed (by omega) offers zero (host.write_bound reply).2 ⟨_, _, next⟩
      | write_trap _ => exact .trapped (by omega) offers

/-- Every run of `writeAll buffer start count` over a buffer of fewer than `2^64 - 1` bytes meets
`WriteAllRun` over the window's bytes from 0 bytes taken with the window's length plus one
passes. -/
theorem writeAll_run {World : Type} {host : Host World} {buffer : Bytes} {start count : UInt64}
    (small : buffer.data.size + 1 < 2 ^ 64) {world : World} {trace : List Event}
    {outcome : Outcome UInt64} {final : World}
    (execution : Exec host (writeAll buffer start count) world trace outcome final) :
    WriteAllRun host (buffer.range start count).data.data.toList 0
      ((buffer.window start count).2 + 1) trace outcome := by
  have hLength := (buffer.window_of_words (by omega) start count).2
  have hWindow := buffer.window_le start count
  have passes : (min count (buffer.size - min start buffer.size) + 1).toNat =
      (buffer.window start count).2 + 1 := by
    rw [UInt64.toNat_add, hLength, UInt64.toNat_one]
    exact Nat.mod_eq_of_lt (by omega)
  change Exec host (.loop (min count (buffer.size - min start buffer.size) + 1) 0 _ _ .pure)
    world trace outcome final at execution
  cases execution with
  | loop run =>
    rw [passes] at run
    exact writeAll_loop_run buffer start count (by omega) (fun _ _ => rfl) (fun _ _ => rfl) _ 0 0
      (by simp) run

/-- Every run of `writeAll bytes 0 bytes.size` over fewer than `2^64 - 1` bytes `bytes` meets
`WriteAllRun` over the bytes of `bytes` from 0 bytes taken with `bytes`'s size plus one passes. -/
theorem writeAll_run_whole {World : Type} {host : Host World} {bytes : Bytes}
    (small : bytes.data.size + 1 < 2 ^ 64) {world : World} {trace : List Event}
    {outcome : Outcome UInt64} {final : World}
    (execution : Exec host (writeAll bytes 0 bytes.size) world trace outcome final) :
    WriteAllRun host bytes.data.data.toList 0 (bytes.data.size + 1) trace outcome := by
  have run := writeAll_run small execution
  have hLength : (bytes.window 0 bytes.size).2 = bytes.data.size := by
    rw [Bytes.window_snd, bytes.size_toNat (by omega)]
    simp
  rwa [bytes.range_zero_size (by omega), hLength] at run

theorem exitStatus_of_lt {code : UInt64} (small : code.toNat < 2 ^ 32) :
    exitStatus code = code := by
  apply UInt64.toNat_inj.mp
  simp only [exitStatus_toNat]
  omega

/-- A run of the loop of `writeAll` over fewer than `2^64` bytes `bytes` from `written` bytes taken,
at most `bytes`'s length, that returns `value` made writes to standard output that each returned
errno 0 and offered the bytes that remained, and took the bytes from `written` up to `value`, at
most `bytes`'s length.  When `value` falls short of `bytes`'s length, the run made one write for
each of its passes.  A run that exits does so with a status `code` from 1 to 76 after events that
end with a write that returned the errno `code` and the exit, every write before which returned
errno 0, each write offered the bytes that remained, and the bytes that the writes took form a
prefix of the bytes from `written` on that leaves at least one byte. -/
theorem WriteAllRun.taken {World : Type} {host : Host World} {bytes : List UInt8}
    (small : bytes.length < 2 ^ 64) {written : UInt64} {passes : Nat} {events : List Event}
    {outcome : Outcome UInt64} (run : WriteAllRun host bytes written passes events outcome) :
    written.toNat ≤ bytes.length →
      (∀ value, outcome = .returned value →
        (∀ e ∈ events, ∃ offered count, e = .write .stdout offered (.returned 0 count)) ∧
        written.toNat ≤ value.toNat ∧ value.toNat ≤ bytes.length ∧
        stdoutTaken events = (bytes.drop written.toNat).take (value.toNat - written.toNat) ∧
        Offered bytes written.toNat events ∧
        (value.toNat < bytes.length → events.length = passes)) ∧
      (∀ code, outcome = .exited code →
        code ≠ 0 ∧ code.toNat ≤ 76 ∧
        (∃ before offered count, events =
            before ++ [.write .stdout offered (.returned code count), .exit code] ∧
          (∀ e ∈ before, ∃ offered count, e = .write .stdout offered (.returned 0 count)) ∧
          Offered bytes written.toNat (before ++ [.write .stdout offered (.returned code count)])) ∧
        stdoutTaken events <+: bytes.drop written.toNat ∧
        written.toNat + (stdoutTaken events).length < bytes.length) := by
  induction run with
  | done ended =>
    intro le
    refine ⟨fun value same => ?_, fun _ same => by cases same⟩
    cases same
    exact ⟨fun _ member => (nomatch member), Nat.le_refl _, le, by simp, trivial,
      fun short => absurd short (by omega)⟩
  | spent left =>
    intro le
    refine ⟨fun value same => ?_, fun _ same => by cases same⟩
    cases same
    exact ⟨fun _ member => (nomatch member), Nat.le_refl _, le, by simp, trivial, fun _ => rfl⟩
  | @wrote written count passes offered events outcome left offers within rest ih =>
    intro le
    have sum : (written + count).toNat = written.toNat + count.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨returned, exited⟩ := ih (by omega)
    have first : (Event.write .stdout offered (.returned 0 count)).stdoutTaken =
        (bytes.drop written.toNat).take count.toNat := by
      simp [Event.stdoutTaken, offers]
    have firstLength :
        (Event.write .stdout offered (.returned 0 count)).stdoutTaken.length = count.toNat := by
      rw [first, List.length_take, List.length_drop]
      omega
    have divided : bytes.drop written.toNat =
        (bytes.drop written.toNat).take count.toNat ++ bytes.drop (written + count).toNat := by
      rw [sum, ← List.drop_drop, List.take_append_drop]
    refine ⟨fun value same => ?_, fun code same => ?_⟩
    · obtain ⟨shape, low, high, taken, offeredRest, counted⟩ := returned value same
      refine ⟨fun e member => ?_, by omega, high, ?_, ⟨⟨offered, _, rfl, offers⟩, ?_⟩,
        fun short => by rw [List.length_cons, counted short]⟩
      · rcases List.mem_cons.mp member with rfl | member
        · exact ⟨_, _, rfl⟩
        · exact shape e member
      · rw [stdoutTaken_cons, first, taken, sum, ← List.drop_drop]
        have whole : value.toNat - written.toNat = count.toNat +
            (value.toNat - (written.toNat + count.toNat)) := by omega
        rw [whole, List.take_add]
      · rw [firstLength, ← sum]
        exact offeredRest
    · obtain ⟨nonzero, valid, ⟨before, offered', count', shape, earlier, offeredRest⟩, prefix_,
        bound⟩ := exited code same
      refine ⟨nonzero, valid, ⟨.write .stdout offered (.returned 0 count) :: before, offered',
        count', by rw [shape]; rfl, ?_, ⟨⟨offered, _, rfl, offers⟩, ?_⟩⟩, ?_, ?_⟩
      · intro e member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨_, _, rfl⟩
        · exact earlier e member
      · rw [firstLength, ← sum]
        exact offeredRest
      · obtain ⟨tail, extended⟩ := prefix_
        have whole : (bytes.drop written.toNat).take count.toNat ++ stdoutTaken events <+:
            (bytes.drop written.toNat).take count.toNat ++ bytes.drop (written + count).toNat :=
          ⟨tail, by rw [List.append_assoc, extended]⟩
        rw [← divided] at whole
        rw [stdoutTaken_cons, first]
        exact whole
      · rw [stdoutTaken_cons, first, List.length_append, List.length_take, List.length_drop]
        rw [sum] at bound
        omega
  | @failed written errno count passes offered events outcome left offers nonzero valid ended =>
    intro _
    obtain ⟨_, _, ended⟩ := ended
    refine ⟨fun value same => ?_, fun code same => ?_⟩
    · subst same
      cases ended
    · subst same
      cases ended with
      | exit _ =>
        rw [exitStatus_of_lt (by omega)]
        refine ⟨nonzero, valid, ⟨[], offered, count, rfl, fun _ member => (nomatch member),
          ⟨⟨offered, _, rfl, offers⟩, trivial⟩⟩, ?_, ?_⟩
        · simp [Event.stdoutTaken, nonzero]
        · simp [Event.stdoutTaken, nonzero]
          omega
  | trapped left offers =>
    intro _
    exact ⟨fun _ same => (by cases same), fun _ same => by cases same⟩

/-- The writes of a run of the loop of `writeAll` that returns or exits offer at least one byte
each and number at most its passes, and a run that exits ends with the exit after them. -/
theorem WriteAllRun.shape {World : Type} {host : Host World} {bytes : List UInt8}
    {written : UInt64} {passes : Nat} {events : List Event} {outcome : Outcome UInt64}
    (run : WriteAllRun host bytes written passes events outcome) :
    (∀ v, outcome = .returned v → events.length ≤ passes ∧ ∀ e ∈ events, WroteSome e) ∧
    (∀ code, outcome = .exited code → ∃ writes, events = writes ++ [.exit code] ∧
      writes.length ≤ passes ∧ ∀ e ∈ writes, WroteSome e) := by
  induction run with
  | done _ => exact ⟨fun _ _ => ⟨Nat.zero_le _, fun _ h => nomatch h⟩, fun _ e => nomatch e⟩
  | spent _ => exact ⟨fun _ _ => ⟨Nat.zero_le _, fun _ h => nomatch h⟩, fun _ e => nomatch e⟩
  | @wrote written count passes offered events outcome left offers within rest ih =>
    have some : WroteSome (.write .stdout offered (.returned 0 count)) := by
      refine ⟨offered, _, rfl, fun e => ?_⟩
      have := congrArg List.length offers
      simp [e] at this
      omega
    refine ⟨fun v e => ?_, fun code e => ?_⟩
    · obtain ⟨hlen, hall⟩ := ih.1 v e
      refine ⟨by simp; omega, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact some
      · exact hall x hx
    · obtain ⟨writes, rfl, hlen, hall⟩ := ih.2 code e
      refine ⟨_ :: writes, rfl, by simp; omega, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact some
      · exact hall x hx
  | @failed written errno count passes offered events outcome left offers nonzero valid ended =>
    obtain ⟨_, _, ended⟩ := ended
    have some : WroteSome (.write .stdout offered (.returned errno count)) := by
      refine ⟨offered, _, rfl, fun e => ?_⟩
      have := congrArg List.length offers
      simp [e] at this
      omega
    refine ⟨fun v e => ?_, fun code e => ?_⟩
    · subst e
      cases ended
    · subst e
      cases ended with
      | exit _ =>
        refine ⟨[.write .stdout offered (.returned errno count)], rfl, by simp, fun x hx => ?_⟩
        rw [List.mem_singleton.mp hx]
        exact some
  | trapped _ _ => exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩

/-- A run of the loop of `writeAll` that traps under a host that rejects no exit status below 126
has a trapped write to standard output. -/
theorem WriteAllRun.trapped_write {World : Type} {host : Host World}
    (accepts : ∀ {world code message final}, host.exitTrap world code message final →
      126 ≤ code.toNat)
    {bytes : List UInt8} {written : UInt64} {passes : Nat} {events : List Event}
    {outcome : Outcome UInt64} (run : WriteAllRun host bytes written passes events outcome) :
    ∀ message, outcome = .trapped message →
      ∃ offered committed, Event.write .stdout offered (.trapped message committed) ∈ events := by
  induction run with
  | done => exact fun _ same => by cases same
  | spent => exact fun _ same => by cases same
  | wrote _ _ _ _ ih =>
    intro message same
    obtain ⟨offered, committed, member⟩ := ih message same
    exact ⟨offered, committed, List.mem_cons_of_mem _ member⟩
  | failed _ _ _ valid ended =>
    intro message same
    subst same
    obtain ⟨_, _, ended⟩ := ended
    cases ended with
    | exitTrap rejected =>
      have high := accepts rejected
      simp only [exitStatus_toNat] at high
      omega
  | trapped => exact fun _ same => by cases same; exact ⟨_, _, List.mem_singleton_self _⟩

end LeanExe.Wasi
