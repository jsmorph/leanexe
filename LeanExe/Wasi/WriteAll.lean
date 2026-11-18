import LeanExe.Wasi.Semantics

/-! `writeAll bytes` writes `bytes` to standard output with a loop of at most `bytes.size + 1`
passes.  Each pass that finds bytes left offers them, `suffix bytes written`, and adds the count
that the write returned to `written`, so a short write is followed by a write of the rest.  A
write that returns an errno ends the run with the exit of that errno.  The loop returns the number
of bytes that the writes took, which falls short of `bytes.size` only when the passes run out,
which takes a write that took no byte.

`WriteAllRun host bytes written passes events outcome` states the events and the outcome of every
run of the loop under `host` from `written` bytes taken with `passes` passes left, and
`writeAll_run` proves it of every run of `writeAll bytes`, from 0 with `bytes.size + 1` passes.
`stdoutTaken` collects the bytes that the writes of a trace to standard output took when they
returned errno 0.  `WriteAllRun.taken` states that a run that returns `value` took, in writes
that each returned errno 0, the bytes from `written` up to `value`, and that a run that exits
does so with the errno, from 1 to 76, of its last write, after taking fewer than the bytes from
`written` on.  `WriteAllRun.trapped_write` states that a run that traps under a host that accepts every
status below 126 has a trapped write. -/

namespace LeanExe.Wasi

/-- The bytes of `bytes` from `start` on. -/
def suffix (bytes : Bytes) (start : UInt64) : Bytes :=
  Bytes.build (bytes.size - start) fun i => bytes.get (start + i)

/-- Writes `bytes` to stdout, continuing after short writes, and exits with the errno of a write
that fails. -/
def writeAll (bytes : Bytes) : Action UInt64 :=
  loop (bytes.size + 1) 0 (fun _ written => written < bytes.size) fun _ written => do
    let reply ← writeStdoutSome (suffix bytes written)
    if reply.errno != 0 then exit reply.errno else pure (written + reply.count)

/-- The count of bytes of `suffix bytes start`: those of `bytes` from `start` on. -/
theorem suffix_count {bytes : Bytes} {start : UInt64} (small : bytes.data.size < 2 ^ 64)
    (le : start.toNat ≤ bytes.data.size) :
    (bytes.size - start).toNat = bytes.data.size - start.toNat := by
  have wide : bytes.size.toNat = bytes.data.size := by
    simp only [Bytes.size, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt small
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, wide]; exact le), wide]

/-- The bytes of `suffix bytes start` are those of `bytes` from `start` on. -/
theorem suffix_toList {bytes : Bytes} {start : UInt64} (small : bytes.data.size < 2 ^ 64)
    (le : start.toNat ≤ bytes.data.size) :
    (suffix bytes start).data.data.toList = bytes.data.data.toList.drop start.toNat := by
  have count := suffix_count small le
  apply List.ext_getElem
  · simp [suffix, count]
  · intro i inside _
    have below : i < bytes.data.size - start.toNat := by
      simpa [suffix, count] using inside
    have inRange : start.toNat + i < bytes.data.size := by omega
    have mod : (start.toNat + i) % 18446744073709551616 = start.toNat + i :=
      Nat.mod_eq_of_lt (by omega)
    simp [suffix, Bytes.build, Bytes.get, mod, inRange, ByteArray.getElem_eq_getElem_data]

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

/-- Every run of the loop of `writeAll bytes` from `written` bytes taken, at most `bytes`'s size,
meets `WriteAllRun`. -/
theorem writeAll_loop_run {World : Type} {host : Host World} (bytes : Bytes)
    (small : bytes.data.size < 2 ^ 64) {test : UInt64 → UInt64 → Bool}
    {step : UInt64 → UInt64 → Action UInt64}
    (tested : ∀ index written, test index written = decide (written < bytes.size))
    (stepped : ∀ index written, step index written =
      .write .stdout (suffix bytes written) fun reply =>
        if reply.errno != 0 then exit reply.errno else .pure (written + reply.count)) :
    ∀ (remaining index : Nat) (written : UInt64) {world trace outcome final},
      written.toNat ≤ bytes.data.size →
      LoopExec host remaining index written test step .pure world trace outcome final →
      WriteAllRun host bytes.data.data.toList written remaining trace outcome
  | 0, _, written, _, _, _, _, _, execution => by
    cases execution with
    | zero next =>
      cases next
      by_cases ended : bytes.data.data.toList.length ≤ written.toNat
      · exact .done ended
      · exact .spent (by omega)
  | remaining + 1, index, written, _, _, _, _, le, execution => by
    have wide : bytes.size.toNat = bytes.data.size := by
      simp only [Bytes.size, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt small
    have length : bytes.data.data.toList.length = bytes.data.size := by simp
    have offers := suffix_toList small le
    have offered : (suffix bytes written).data.size = bytes.data.size - written.toNat := by
      have := congrArg List.length offers
      simpa using this
    cases execution with
    | stop test next =>
      cases next
      rw [tested] at test
      refine .done ?_
      simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, wide] at test
      omega
    | next test step rest =>
      rw [tested] at test
      have left : written.toNat < bytes.data.size := by
        simpa [UInt64.lt_iff_toNat_lt, wide] using test
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
            (writeAll_loop_run bytes small tested stepped remaining (index + 1)
              (written + committed) (by omega) rest)
        · have failing : ((writeResult errno committed).errno != 0) = true := by
            simp [writeResult, zero]
          dsimp only at next
          rw [ite_eq_left failing] at next
          cases next
    | exit test step =>
      rw [tested] at test
      have left : written.toNat < bytes.data.size := by
        simpa [UInt64.lt_iff_toNat_lt, wide] using test
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
      have left : written.toNat < bytes.data.size := by
        simpa [UInt64.lt_iff_toNat_lt, wide] using test
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

/-- Every run of `writeAll bytes` meets `WriteAllRun` from 0 bytes taken with `bytes.size + 1`
passes. -/
theorem writeAll_run {World : Type} {host : Host World} {bytes : Bytes}
    (small : bytes.data.size + 1 < 2 ^ 64) {world : World} {trace : List Event}
    {outcome : Outcome UInt64} {final : World}
    (execution : Exec host (writeAll bytes) world trace outcome final) :
    WriteAllRun host bytes.data.data.toList 0 (bytes.data.size + 1) trace outcome := by
  have wide : bytes.size.toNat = bytes.data.size := by
    simp only [Bytes.size, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have passes : (bytes.size + 1).toNat = bytes.data.size + 1 := by
    rw [UInt64.toNat_add, wide, UInt64.toNat_one]
    exact Nat.mod_eq_of_lt small
  change Exec host (.loop (bytes.size + 1) 0 _ _ .pure) world trace outcome final at execution
  cases execution with
  | loop run =>
    rw [passes] at run
    exact writeAll_loop_run bytes (by omega) (fun _ _ => rfl) (fun _ _ => rfl) _ 0 0 (by simp) run

theorem exitStatus_of_lt {code : UInt64} (small : code.toNat < 2 ^ 32) :
    exitStatus code = code := by
  apply UInt64.toNat_inj.mp
  simp only [exitStatus_toNat]
  omega

/-- A run of the loop of `writeAll` over `bytes` from `written` bytes taken, at most `bytes`'s
length, that returns `value` took, in writes to standard output that each returned errno 0, the
bytes from `written` up to `value`, at most `bytes`'s length.  A run that exits does so with a
status `code` from 1 to 76 after events that end with a write that returned the errno `code` and
the exit, every write before which returned errno 0, and the bytes that the writes took form a
prefix of the bytes from `written` on that leaves at least one byte. -/
theorem WriteAllRun.taken {World : Type} {host : Host World} {bytes : List UInt8}
    (small : bytes.length < 2 ^ 64) {written : UInt64} {passes : Nat} {events : List Event}
    {outcome : Outcome UInt64} (run : WriteAllRun host bytes written passes events outcome) :
    written.toNat ≤ bytes.length →
      (∀ value, outcome = .returned value →
        (∀ e ∈ events, ∃ offered count, e = .write .stdout offered (.returned 0 count)) ∧
        written.toNat ≤ value.toNat ∧ value.toNat ≤ bytes.length ∧
        stdoutTaken events = (bytes.drop written.toNat).take (value.toNat - written.toNat)) ∧
      (∀ code, outcome = .exited code →
        code ≠ 0 ∧ code.toNat ≤ 76 ∧
        (∃ before offered count, events =
            before ++ [.write .stdout offered (.returned code count), .exit code] ∧
          ∀ e ∈ before, ∃ offered count, e = .write .stdout offered (.returned 0 count)) ∧
        stdoutTaken events <+: bytes.drop written.toNat ∧
        written.toNat + (stdoutTaken events).length < bytes.length) := by
  induction run with
  | done ended =>
    intro le
    refine ⟨fun value same => ?_, fun _ same => by cases same⟩
    cases same
    exact ⟨fun _ member => (nomatch member), Nat.le_refl _, le, by simp⟩
  | spent left =>
    intro le
    refine ⟨fun value same => ?_, fun _ same => by cases same⟩
    cases same
    exact ⟨fun _ member => (nomatch member), Nat.le_refl _, le, by simp⟩
  | @wrote written count passes offered events outcome left offers within rest ih =>
    intro le
    have sum : (written + count).toNat = written.toNat + count.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨returned, exited⟩ := ih (by omega)
    have first : (Event.write .stdout offered (.returned 0 count)).stdoutTaken =
        (bytes.drop written.toNat).take count.toNat := by
      simp [Event.stdoutTaken, offers]
    have divided : bytes.drop written.toNat =
        (bytes.drop written.toNat).take count.toNat ++ bytes.drop (written + count).toNat := by
      rw [sum, ← List.drop_drop, List.take_append_drop]
    refine ⟨fun value same => ?_, fun code same => ?_⟩
    · obtain ⟨shape, low, high, taken⟩ := returned value same
      refine ⟨fun e member => ?_, by omega, high, ?_⟩
      · rcases List.mem_cons.mp member with rfl | member
        · exact ⟨_, _, rfl⟩
        · exact shape e member
      · rw [stdoutTaken_cons, first, taken, sum, ← List.drop_drop]
        have whole : value.toNat - written.toNat = count.toNat +
            (value.toNat - (written.toNat + count.toNat)) := by omega
        rw [whole, List.take_add]
    · obtain ⟨nonzero, valid, ⟨before, offered', count', shape, earlier⟩, prefix_, bound⟩ :=
        exited code same
      refine ⟨nonzero, valid, ⟨.write .stdout offered (.returned 0 count) :: before, offered',
        count', by rw [shape]; rfl, ?_⟩, ?_, ?_⟩
      · intro e member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨_, _, rfl⟩
        · exact earlier e member
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
    have first : (Event.write .stdout offered (.returned errno count)).stdoutTaken = [] := by
      simp [Event.stdoutTaken, nonzero]
    refine ⟨fun value same => ?_, fun code same => ?_⟩
    · subst same
      cases ended
    · subst same
      cases ended with
      | exit _ =>
        rw [exitStatus_of_lt (by omega)]
        refine ⟨nonzero, valid, ⟨[], offered, count, rfl, fun _ member => (nomatch member)⟩, ?_, ?_⟩
        · simp [Event.stdoutTaken, nonzero]
        · simp [Event.stdoutTaken, nonzero]
          omega
  | trapped left offers =>
    intro _
    exact ⟨fun _ same => (by cases same), fun _ same => by cases same⟩

/-- A run of the loop of `writeAll` that traps under a host that accepts every exit status below
126 has a trapped write to standard output. -/
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
