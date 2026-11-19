import Verified.Examples.WasiReadAllShim
import Verified.Shim.Images

/-!
readAll's message corollary at the shim's specification level.  Under `linuxHost`, a run of
`main` and its exit whose layer events hold no `read` that fails and no `write` that fails or
returns 0 exits with the status `statusOf` of the bytes that its reads of descriptor 0 returned:
0 when they number at most `limit`, 1,000,000, and 1 otherwise.  Its layer events meet `Copies`:
reads of 4,096 bytes from descriptor 0, each but the last returning bytes, at most `limit` bytes
before the last read and `limit + 4096` in all, the last read returning none unless the bytes
exceed `limit`, followed by writes of descriptor 1 that took the bytes that the reads returned.
Writes of count 0 are excluded because they can use up `writeAll`'s passes with bytes unwritten,
two of them for an input of one byte, while the run still exits with `statusOf` of the input.

`exec_message` proves these facts over the WASI trace, for every host that rejects only statuses
of 126 or more.  `linux_exec_succeeded` carries them to the layer events of an `Exec` run under
`linuxHost` and the `Images` of its trace when the WASI events meet `Succeeded`, and
`linux_exec_message` when the layer events meet `ReadsSucceed` and `WritesAdvance`, predicates
over the events in the form of `LeanExe/Linux/Replies.lean`.  Neither takes another premise, so
both apply to every run of a footprint that ends in an accepted exit, a rejected exit, or a trap
of the shim, a binding's footprint of a native run among them.  A footprint that admits a guest
trap after a prefix gives no `Exec` run for that case.  Excluding the trap takes a footprint
without guest traps, which holds for a reply sequence that meets the budget premise below at the
footprint's memory cap.

`linux_message` composes `linux_exec_message` with the command's `start` theorem without guest
traps.  For every reply sequence and every budget that fits between the heap's start at byte 4,096
and the end of the module's 65,535 pages and bounds every typed resource prefix of `main` under
those replies, every run of `_start` with enough fuel traps, and when the final layer events meet
the two predicates, the trap is the accepted exit with that status.  The budget is the resource
model's.  `writeAll` writes windows of the input in place and charges nothing, so the block of
`readAll`'s buffer bounds every prefix under every reply sequence, as `budget_bounded` of
`Verified/Examples/WasiReadAllSteady.lean` states.
-/

namespace Verified.Examples.WasiReadAll

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim

/-- Every `read` of `tr` returns a count of at most its length. -/
def ReadsSucceed (tr : List Linux.Event) : Prop :=
  ∀ e ∈ tr, e.call = Linux.readCall → e.ret.toNat ≤ (Linux.arg e.args 2).toNat

/-- Every `write` of `tr` returns a positive count of at most its length. -/
def WritesAdvance (tr : List Linux.Event) : Prop :=
  ∀ e ∈ tr, e.call = Linux.writeCall →
    0 < e.ret.toNat ∧ e.ret.toNat ≤ (Linux.arg e.args 2).toNat

/-- A read that returned errno 0, or a write that returned errno 0 and a positive count; every
event of another kind qualifies. -/
def Succeeded : Wasi.Event → Prop
  | .read _ (.returned errno _) => errno = 0
  | .read _ (.trapped _ _) => False
  | .write _ _ (.returned errno count) => errno = 0 ∧ count ≠ 0
  | .write _ _ (.trapped _ _) => False
  | _ => True

/-- The status of `main` for the input `input`: 1 when it holds more than `limit` bytes, and 0
otherwise. -/
def statusOf (input : List UInt8) : UInt64 := if limit.toNat < input.length then 1 else 0

/-- The layer events `ls` are reads of 4,096 bytes from descriptor 0 followed by writes of
descriptor 1.  Each read but the last returned bytes, those reads returned at most `limit` bytes,
and the last read returned none unless the reads returned more than `limit` bytes in all, at most
`limit + 4096`.  The writes took the bytes that the reads returned. -/
def Copies (ls : List Linux.Event) : Prop :=
  Linux.writeData 1 ls = Linux.readData 0 ls ∧
    (Linux.readData 0 ls).length ≤ limit.toNat + 4096 ∧
    ∃ before last writes, ls = before ++ last :: writes ∧
      (∀ e ∈ before ++ [last], e.call = Linux.readCall ∧ Linux.arg e.args 0 = 0 ∧
        Linux.arg e.args 2 = 4096) ∧
      (∀ e ∈ before, e.readBytes 0 ≠ []) ∧
      (Linux.readData 0 before).length ≤ limit.toNat ∧
      (last.readBytes 0 = [] ∨ limit.toNat < (Linux.readData 0 ls).length) ∧
      (∀ e ∈ writes, e.call = Linux.writeCall ∧ Linux.arg e.args 0 = 1)

/-! ## The layer's replies and the WASI replies -/

theorem image_succeeded {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {e : Wasi.Event} {l : List Linux.Event} (image : Image F L I events e l)
    (reads : ReadsSucceed l) (writes : WritesAdvance l) : Succeeded e := by
  cases e with
  | read count reply =>
    obtain ⟨x, a, rfl, call, args, _, rfl⟩ := image
    have within := reads x (List.mem_singleton_self x) call
    simp only [args, Linux.arg, List.getD_cons_succ, List.getD_cons_zero] at within
    simp only [Shim.readReply, within, ↓reduceIte, Succeeded]
  | write output bytes reply =>
    obtain ⟨x, a, rfl, call, args, _, _, _, rfl⟩ := image
    obtain ⟨positive, within⟩ := writes x (List.mem_singleton_self x) call
    simp only [args, Linux.arg, List.getD_cons_succ, List.getD_cons_zero] at within
    simp only [writeReply, within, ↓reduceIte, Succeeded]
    exact ⟨trivial, fun zero => by simp [zero] at positive⟩
  | exit | exitTrap | sys => trivial

/-- The WASI events of images whose reads succeed and whose writes return positive counts within
their lengths meet `Succeeded`. -/
theorem images_succeeded {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {trace : List Wasi.Event} {ls : List Linux.Event}
    (images : Images F L I events trace ls) (reads : ReadsSucceed ls) (writes : WritesAdvance ls) :
    ∀ e ∈ trace, Succeeded e := by
  induction images with
  | nil => intro e member; cases member
  | cons image _ ih =>
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact image_succeeded image (fun x m => reads x (List.mem_append_left _ m))
        (fun x m => writes x (List.mem_append_left _ m))
    · exact ih (fun x m => reads x (List.mem_append_right _ m))
        (fun x m => writes x (List.mem_append_right _ m)) e member

theorem images_reads {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {trace : List Wasi.Event} {ls : List Linux.Event}
    (images : Images F L I events trace ls)
    (shape : ∀ e ∈ trace, ∃ reply, e = .read 4096 reply) :
    ∀ x ∈ ls, x.call = Linux.readCall ∧ Linux.arg x.args 0 = 0 ∧ Linux.arg x.args 2 = 4096 := by
  induction images with
  | nil => intro x member; cases member
  | @cons _ e _ _ _ image _ ih =>
    intro x member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨reply, rfl⟩ := shape e (List.mem_cons_self ..)
      obtain ⟨y, a, rfl, call, args, _⟩ := image
      obtain rfl := List.mem_singleton.mp member
      exact ⟨call, by simp [args, Linux.arg]⟩
    · exact ih (fun e m => shape e (List.mem_cons_of_mem _ m)) x member

theorem images_writes {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {trace : List Wasi.Event} {ls : List Linux.Event}
    (images : Images F L I events trace ls)
    (shape : ∀ e ∈ trace, ∃ offered reply, e = .write .stdout offered reply) :
    ∀ x ∈ ls, x.call = Linux.writeCall ∧ Linux.arg x.args 0 = 1 := by
  induction images with
  | nil => intro x member; cases member
  | @cons _ e _ _ _ image _ ih =>
    intro x member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨offered, reply, rfl⟩ := shape e (List.mem_cons_self ..)
      obtain ⟨y, a, rfl, call, args, _⟩ := image
      obtain rfl := List.mem_singleton.mp member
      exact ⟨call, by simp [args, Linux.arg, Output.fd]⟩
    · exact ih (fun e m => shape e (List.mem_cons_of_mem _ m)) x member

/-- The images of reads that returned bytes returned bytes. -/
theorem images_nonempty {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {events : List Linux.Event} {trace : List Wasi.Event} {ls : List Linux.Event}
    (images : Images F L I events trace ls)
    (shape : ∀ e ∈ trace, ∃ committed, e = .read 4096 (.returned 0 committed) ∧
      committed.data.size ≠ 0) :
    ∀ x ∈ ls, x.readBytes 0 ≠ [] := by
  induction images with
  | nil => intro x member; cases member
  | @cons _ e _ _ _ image _ ih =>
    intro x member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨committed, rfl, nonzero⟩ := shape e (List.mem_cons_self ..)
      have bytes := image_readData 0 image
      obtain ⟨y, a, rfl, _⟩ := image
      obtain rfl := List.mem_singleton.mp member
      simp only [Linux.readData, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        eventReads, ↓reduceIte, Transfer.committed] at bytes
      rw [bytes]
      intro none
      exact nonzero (by simpa using congrArg List.length none)
    · exact ih (fun e m => shape e (List.mem_cons_of_mem _ m)) x member

/-! ## The runs of `main` -/

theorem readAll_ended {World : Type} {host : Host World} {state : ReadAllState}
    (done : state.done = true) :
    ∀ {remaining index world trace outcome final},
      LoopExec host remaining index state readAllTest (readAllRead limit) readAllResult world
        trace outcome final → trace = [] ∧ outcome = .returned ⟨state.errno, state.held⟩
  | 0, _, _, _, _, _, execution => by
    cases execution with
    | zero next =>
      cases next
      exact ⟨rfl, rfl⟩
  | _ + 1, _, _, _, _, _, execution => by
    cases execution with
    | stop _ next =>
      cases next
      exact ⟨rfl, rfl⟩
    | next test => simp [readAllTest, done] at test
    | exit test => simp [readAllTest, done] at test
    | trap test => simp [readAllTest, done] at test

/-- A run of the loop of `readAll limit` from at most `limit` bytes held, with more passes left than
the bytes that `limit` admits beyond them, whose reads succeed returns errno 0 and the bytes held
followed by those that its reads returned.  Its events are reads of 4,096 bytes, each but the last
returning bytes, which with the bytes held number at most `limit`, and the last read returned no
bytes unless the bytes returned exceed `limit`. -/
theorem readAll_loop {World : Type} {host : Host World} :
    ∀ (remaining index : Nat) (held : Bytes) {world trace outcome final},
      held.data.size ≤ limit.toNat → limit.toNat < held.data.size + remaining →
      LoopExec host remaining index (⟨0, held, false⟩ : ReadAllState) readAllTest
        (readAllRead limit) readAllResult world trace outcome final →
      (∀ e ∈ trace, Succeeded e) →
      ∃ bytes : Bytes, outcome = .returned ⟨0, bytes⟩ ∧
        bytes.data.data.toList = held.data.data.toList ++ committedReads 0 trace ∧
        ∃ before last, trace = before ++ [.read 4096 (.returned 0 last)] ∧
          (∀ e ∈ before, ∃ committed, e = .read 4096 (.returned 0 committed) ∧
            committed.data.size ≠ 0) ∧
          held.data.size + (committedReads 0 before).length ≤ limit.toNat ∧
          (last.data.size = 0 ∨ limit.toNat < bytes.data.size)
  | 0, _, _, _, _, _, _, low, enough, _, _ => absurd enough (by omega)
  | remaining + 1, index, held, _, _, _, _, low, enough, execution, ok => by
    cases execution with
    | stop test => simp [readAllTest] at test
    | next _ step rest =>
      change Exec host (.read 4096 fun reply =>
        .pure (readAllStep limit ⟨0, held, false⟩ ⟨reply.errno, reply.bytes⟩)) _ _ _ _ at step
      cases step with
      | read_reject capacity => exact absurd capacity (by decide)
      | @read_return _ _ _ _ _ _ _ _ errno committed _ _ reply _ _ next =>
        cases next
        rw [readAllStep_reply] at rest
        have zero : errno = 0 := ok (.read 4096 (.returned errno committed)) (by simp)
        subst zero
        by_cases empty : committed.data.size = 0
        · rw [readAllStep_ended empty] at rest
          obtain ⟨rfl, rfl⟩ := readAll_ended rfl rest
          have none : committed.data.data.toList = [] :=
            List.length_eq_zero_iff.mp (by simpa using empty)
          refine ⟨held, rfl, ?_, [], committed, rfl, by simp, by simpa [committedReads] using low,
            .inl empty⟩
          simp [committedReads, eventReads, Transfer.committed, none]
        · rw [readAllStep_appended empty] at rest
          by_cases above : limit.toNat < held.data.size + committed.data.size
          · simp only [above, decide_true] at rest
            obtain ⟨rfl, rfl⟩ := readAll_ended rfl rest
            refine ⟨appendBytes held committed, rfl, ?_, [], committed, rfl, by simp,
              by simpa [committedReads] using low, .inr (by simpa using above)⟩
            simp [committedReads, eventReads, Transfer.committed, appendBytes]
          · simp only [above, decide_false] at rest
            obtain ⟨bytes, same, list, before, last, rfl, nonempty, bound, ends⟩ :=
              readAll_loop remaining (index + 1) (appendBytes held committed)
                (by simp only [appendBytes_size]; omega) (by simp only [appendBytes_size]; omega)
                rest (fun e m => ok e (List.mem_append_right _ m))
            refine ⟨bytes, same, ?_, .read 4096 (.returned 0 committed) :: before, last,
              by simp, ?_, ?_, ends⟩
            · rw [list]
              simp [committedReads, eventReads, Transfer.committed, appendBytes]
            · intro e member
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨committed, rfl, empty⟩
              · exact nonempty e member
            · simp only [appendBytes_size] at bound
              simp only [committedReads, List.flatMap_cons, eventReads, ↓reduceIte,
                Transfer.committed, List.length_append, Array.length_toList,
                ByteArray.size_data] at bound ⊢
              omega
    | exit _ step =>
      change Exec host (.read 4096 fun reply =>
        .pure (readAllStep limit ⟨0, held, false⟩ ⟨reply.errno, reply.bytes⟩)) _ _ _ _ at step
      cases step with
      | read_reject capacity => exact absurd capacity (by decide)
      | read_return _ _ _ _ next => cases next
    | trap _ step =>
      change Exec host (.read 4096 fun reply =>
        .pure (readAllStep limit ⟨0, held, false⟩ ⟨reply.errno, reply.bytes⟩)) _ _ _ _ at step
      cases step with
      | read_reject capacity => exact absurd capacity (by decide)
      | read_return _ _ _ _ next => cases next
      | read_trap _ _ => exact False.elim (ok _ (List.mem_singleton_self _))

/-- A run of `writeAll`'s loop from `written` bytes taken whose writes succeed, with more passes
left than bytes, returns after writes to standard output that took the bytes from `written` on. -/
theorem succeeded_run {World : Type} {host : Host World} {bytes : List UInt8}
    (small : bytes.length < 2 ^ 64) {written : UInt64} {passes : Nat} {trace : List Wasi.Event}
    {outcome : Outcome UInt64} (run : WriteAllRun host bytes written passes trace outcome) :
    written.toNat ≤ bytes.length → bytes.length - written.toNat < passes →
      (∀ e ∈ trace, Succeeded e) →
      (∃ value, outcome = .returned value) ∧ committedWrites 1 trace = bytes.drop written.toNat ∧
        ∀ e ∈ trace, ∃ offered reply, e = .write .stdout offered reply := by
  induction run with
  | done ended =>
    intro _ _ _
    exact ⟨⟨_, rfl⟩, by simp [committedWrites, List.drop_eq_nil_of_le ended], by simp⟩
  | spent _ =>
    intro _ enough _
    omega
  | @wrote written count passes offered events outcome left offers within rest ih =>
    intro le enough ok
    obtain ⟨_, positive⟩ : (0 : UInt64) = 0 ∧ count ≠ 0 := ok _ (List.mem_cons_self ..)
    have nonzero : 0 < count.toNat := by
      rcases Nat.eq_zero_or_pos count.toNat with same | pos
      · exact absurd (UInt64.toNat_inj.mp (by simpa using same)) positive
      · exact pos
    have sum : (written + count).toNat = written.toNat + count.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨returned, writes, shape⟩ := ih (by omega) (by omega)
      (fun e m => ok e (List.mem_cons_of_mem _ m))
    refine ⟨returned, ?_, ?_⟩
    · simp only [committedWrites, List.flatMap_cons] at writes ⊢
      rw [writes, sum, ← List.drop_drop]
      simp only [eventWrites, Output.fd, ↓reduceIte, Transfer.committed, offers,
        List.take_append_drop]
    · intro e member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, rfl⟩
      · exact shape e member
  | failed _ _ nonzero =>
    intro _ _ ok
    exact absurd (ok _ (List.mem_cons_self ..)).1 nonzero
  | trapped =>
    intro _ _ ok
    exact (ok _ (List.mem_singleton_self _)).elim

theorem committedReads_append (fd : UInt64) (first rest : List Wasi.Event) :
    committedReads fd (first ++ rest) = committedReads fd first ++ committedReads fd rest := by
  simp [committedReads]

theorem committedWrites_append (fd : UInt64) (first rest : List Wasi.Event) :
    committedWrites fd (first ++ rest) = committedWrites fd first ++ committedWrites fd rest := by
  simp [committedWrites]

theorem committedReads_writes {trace : List Wasi.Event}
    (shape : ∀ e ∈ trace, ∃ offered reply, e = .write .stdout offered reply) :
    committedReads 0 trace = [] := by
  simp only [committedReads, List.flatMap_eq_nil_iff]
  intro e member
  obtain ⟨_, _, rfl⟩ := shape e member
  rfl

theorem committedWrites_reads {trace : List Wasi.Event}
    (shape : ∀ e ∈ trace, ∃ reply, e = .read 4096 reply) :
    committedWrites 1 trace = [] := by
  simp only [committedWrites, List.flatMap_eq_nil_iff]
  intro e member
  obtain ⟨_, rfl⟩ := shape e member
  rfl

theorem exitStatus_statusOf (input : List UInt8) :
    exitStatus (statusOf input) = statusOf input := by
  unfold statusOf
  split <;> rfl

/-- Under a host that rejects only statuses of 126 or more, every run of `main` and its exit whose
reads succeed and whose writes return errno 0 and positive counts exits with `statusOf` of the
bytes that its reads returned, at most `limit + 4096` of them, and its writes to standard output
took those bytes.  Its events are reads of 4,096 bytes, then writes to standard output, then the
exit.  Each read but the last returned bytes, at most `limit` bytes in all, and the last read
returned none unless the bytes exceed `limit`. -/
theorem exec_message {World : Type} {host : Host World}
    (accepts : ∀ {world code message final}, host.exitTrap world code message final →
      126 ≤ code.toNat)
    {world final : World} {trace : List Wasi.Event} {outcome : Outcome Unit}
    (execution : Exec host (main.bind fun status => Action.exit status) world trace outcome final)
    (ok : ∀ e ∈ trace, Succeeded e) :
    outcome = .exited (statusOf (committedReads 0 trace)) ∧
      committedWrites 1 trace = committedReads 0 trace ∧
      (committedReads 0 trace).length ≤ limit.toNat + 4096 ∧
      ∃ before last writes code,
        trace = before ++ [.read 4096 (.returned 0 last)] ++ writes ++ [.exit code] ∧
        (∀ e ∈ before, ∃ committed, e = .read 4096 (.returned 0 committed) ∧
          committed.data.size ≠ 0) ∧
        (committedReads 0 before).length ≤ limit.toNat ∧
        (last.data.size = 0 ∨ limit.toNat < (committedReads 0 trace).length) ∧
        (∀ e ∈ writes, ∃ offered reply, e = .write .stdout offered reply) := by
  obtain ⟨_, _, middle, last, mainRun, exitRun, rfl⟩ := Exec.unbind main execution
  obtain ⟨_, readTrace, input, _, readRun, restRun, rfl⟩ := Exec.unbind (readAll limit) mainRun
  have readRun' := readRun
  unfold readAll at readRun
  simp only [show limit.toNat < 4294963200 by decide, ↓reduceIte] at readRun
  cases readRun with
  | loop loopRun =>
  obtain ⟨bytes, rfl, readBytes, before, last, readTraceEq, nonempty, beforeBound, ends⟩ :=
    readAll_loop _ 0 Bytes.empty (by decide) (by decide) loopRun (fun e m => ok e (by simp [m]))
  simp only [Bytes.empty, ByteArray.data_empty, Array.toList_empty, List.nil_append] at readBytes
  simp only [Bytes.empty, ByteArray.size_empty, Nat.zero_add] at beforeBound
  have readShape : ∀ e ∈ readTrace, ∃ reply, e = .read 4096 reply := by
    intro e member
    rw [readTraceEq] at member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨_, rfl, _⟩ := nonempty e member
      exact ⟨_, rfl⟩
    · exact ⟨_, List.mem_singleton.mp member⟩
  have size : bytes.data.size ≤ limit.toNat + 4096 := readAll_size readRun'
  have limitValue : limit.toNat = 1000000 := rfl
  have wide : bytes.size.toNat = bytes.data.size := by
    simp only [Bytes.size, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have length : bytes.data.data.toList.length = bytes.data.size := by simp
  change Exec host (if (0 : UInt64) != 0 then _ else _) _ _ _ _ at restRun
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at restRun
  obtain ⟨_, writeTrace, written, finishTrace, writeRun, finishRun, rfl⟩ :=
    Exec.unbind (writeAll bytes 0 bytes.size) restRun
  obtain ⟨⟨_, rfl⟩, writeBytes, writeShape⟩ := succeeded_run (by omega)
    (writeAll_run_whole (by omega) writeRun) (by simp) (by rw [length, UInt64.toNat_zero]; omega)
    (fun e m => ok e (by simp [m]))
  simp only [UInt64.toNat_zero, List.drop_zero] at writeBytes
  have finish : (if limit < bytes.size then (Action.pure 1 : Action UInt64) else .pure 0) =
      .pure (statusOf bytes.data.data.toList) := by
    unfold statusOf
    rw [length]
    by_cases above : limit.toNat < bytes.data.size
    · have lt : limit < bytes.size := by rw [UInt64.lt_iff_toNat_lt, wide]; exact above
      simp only [lt, above, ↓reduceIte]
    · have notLt : ¬limit < bytes.size := by rw [UInt64.lt_iff_toNat_lt, wide]; exact above
      simp only [notLt, above, ↓reduceIte]
  change Exec host (if limit < bytes.size then .pure 1 else .pure 0) _ _ _ _ at finishRun
  rw [finish] at finishRun
  cases finishRun
  change Exec host (Action.exit (statusOf bytes.data.data.toList)) _ _ _ _ at exitRun
  cases exitRun with
  | exit _ =>
    have reads : committedReads 0 (readTrace ++ (writeTrace ++ []) ++
        [.exit (exitStatus (statusOf bytes.data.data.toList))]) = bytes.data.data.toList := by
      rw [committedReads_append, committedReads_append, committedReads_append,
        committedReads_writes writeShape, readBytes]
      simp [committedReads, eventReads]
    have writes : committedWrites 1 (readTrace ++ (writeTrace ++ []) ++
        [.exit (exitStatus (statusOf bytes.data.data.toList))]) = bytes.data.data.toList := by
      rw [committedWrites_append, committedWrites_append, committedWrites_append,
        committedWrites_reads readShape, writeBytes]
      simp [committedWrites, eventWrites]
    rw [reads, writes, exitStatus_statusOf]
    exact ⟨rfl, rfl, by rw [length]; exact size, before, last, writeTrace, _,
      by rw [readTraceEq, List.append_nil], nonempty, beforeBound,
      ends.imp_right fun exceeds => by rw [length]; exact exceeds, writeShape⟩
  | exitTrap rejected =>
    have high := accepts rejected
    rw [exitStatus_statusOf] at high
    unfold statusOf at high
    split at high <;> simp at high

/-- Under the shim's host, every run of `main` and its exit whose WASI events meet `Succeeded`
exits with `statusOf` of the bytes that the reads of descriptor 0 in the images `ls` of its events
returned, and `ls` meets `Copies`. -/
theorem linux_exec_succeeded {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {replies : Linux.Replies} {world final : LinuxWorld} {trace : List Wasi.Event}
    {outcome : Outcome Unit} {ls : List Linux.Event}
    (execution : Exec (linuxHost F L I replies) (main.bind fun status => Action.exit status)
      world trace outcome final)
    (images : Images F L I world.events trace ls) (ok : ∀ e ∈ trace, Succeeded e) :
    outcome = .exited (statusOf (Linux.readData 0 ls)) ∧ Copies ls := by
  have readEq := images.readData 0
  have writeEq := images.writeData 1
  obtain ⟨exited, copied, size, before, last, writeTrace, code, rfl, nonempty, beforeBound, ends,
    writeShape⟩ := exec_message (host := linuxHost F L I replies) (fun rejected => rejected.1)
      execution ok
  refine ⟨by rw [readEq]; exact exited, ?_⟩
  unfold Copies
  refine ⟨by rw [readEq, writeEq]; exact copied, by rw [readEq]; exact size, ?_⟩
  obtain ⟨l, lx, rfl, front, exitImages⟩ := images_split images
  obtain ⟨lr, lw, rfl, readImages, writeImages⟩ := images_split front
  have readsShape := images_reads readImages fun e member => by
    rcases List.mem_append.mp member with member | member
    · obtain ⟨_, rfl, _⟩ := nonempty e member
      exact ⟨_, rfl⟩
    · exact ⟨_, List.mem_singleton.mp member⟩
  obtain ⟨lb, ll, rfl, beforeImages, lastImages⟩ := images_split readImages
  cases exitImages with
  | cons image tail =>
    cases tail
    cases image
    cases lastImages with
    | cons image tail =>
      cases tail
      have lastBytes := image_readData 0 image
      obtain ⟨y, a, rfl, _⟩ := image
      simp only [Linux.readData, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        eventReads, ↓reduceIte, Transfer.committed] at lastBytes
      refine ⟨lb, y, lw, by simp, fun e member => readsShape e (by simpa using member),
        images_nonempty beforeImages nonempty, by rw [beforeImages.readData 0]; exact beforeBound,
        ?_, images_writes writeImages writeShape⟩
      rcases ends with empty | exceeds
      · exact .inl (by rw [lastBytes]; exact List.length_eq_zero_iff.mp (by simpa using empty))
      · exact .inr (by rw [readEq]; exact exceeds)

/-- Under the shim's host, every run of `main` and its exit whose layer events, the images of its
WASI events, hold no `read` that fails and no `write` that fails or returns 0 exits with
`statusOf` of the bytes that its reads of descriptor 0 returned, and its layer events meet
`Copies`. -/
theorem linux_exec_message {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {replies : Linux.Replies} {world final : LinuxWorld} {trace : List Wasi.Event}
    {outcome : Outcome Unit} {ls : List Linux.Event}
    (execution : Exec (linuxHost F L I replies) (main.bind fun status => Action.exit status)
      world trace outcome final)
    (images : Images F L I world.events trace ls) (reads : ReadsSucceed ls)
    (writes : WritesAdvance ls) :
    outcome = .exited (statusOf (Linux.readData 0 ls)) ∧ Copies ls :=
  linux_exec_succeeded execution images (images_succeeded images reads writes)

/-- The footprint of `linux_footprint` without a guest trap, for a budget that fits between the
heap's start at byte 4,096 and the end of the module's 65,535 pages and bounds the heap that every
prefix of `main` allocates under the shim's host with the replies `replies`. -/
theorem linux_footprint_bounded (F : OpenFlags) (L : ShimLayout) (I : Launch)
    (replies : Linux.Replies) {budget : Nat}
    (room : 4096 + budget ≤ 65536 * 65535)
    (bounded : Resource.CallPrefixBound (observedHost (linuxHost F L I replies))
      (.ofProg command.pure.program command.pure.funs) command.program
      .here 0 .nil linuxStart budget) :
    ∃ bound, ∀ fuel ≥ bound,
      Footprint F L I replies (main.bind fun status => Action.exit status) linuxStart false
        (run fuel command.module (Wrappers.effectIndex command.pure.module 2) linuxInitial []
          (linuxEnv F L I replies [])) := by
  have initialized := command.initial linuxStart
  obtain ⟨bound, results⟩ := command.start (host := linuxHost F L I replies) (aborts := false)
    (budget := budget) (linuxEnv_satisfies F L I replies [] (fun _ member => nomatch member) _
      (by simp [compile_imports, ABI.imports_length]))
    initialized.1 rfl Separate.nil ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
    (fun _ membership => nomatch membership) initialized.2.1
    (fun _ => ⟨by change 4096 + budget ≤ 65536 * 65535; exact room, bounded⟩)
  exact ⟨bound, fun fuel enough => footprint_of_result F L I replies (results fuel enough)⟩

/-- A footprint without a guest trap from `linuxStart` is a trap.  When its layer events hold no
`read` that fails and no `write` that fails or returns 0, the trap is the accepted exit with
`statusOf` of the bytes that the reads of descriptor 0 returned, and the events meet `Copies`. -/
theorem footprint_message {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {replies : Linux.Replies} {result : Result (Observed LinuxWorld)}
    (footprint : Footprint F L I replies (main.bind fun status => Action.exit status) linuxStart
      false result) :
    ∃ final message, result = .Trap final message ∧
      (ReadsSucceed final.host.world.events → WritesAdvance final.host.world.events →
        message = exitTrap ∧
          final.host.world.exited = some (statusOf (Linux.readData 0 final.host.world.events)) ∧
          Copies final.host.world.events) := by
  cases result with
  | Trap final message =>
    refine ⟨final, message, rfl, fun reads writes => ?_⟩
    obtain ⟨trace, ls, grown, images, _, _, _, classified⟩ := footprint
    change final.host.world.events = [] ++ ls at grown
    rw [List.nil_append] at grown
    rw [grown] at reads writes ⊢
    rcases classified with ⟨code, rfl, execution⟩ | ⟨_, execution⟩ | ⟨_, execution⟩ |
      ⟨impossible, _⟩
    · obtain ⟨exited, copies⟩ := linux_exec_message execution images reads writes
      obtain rfl := Outcome.exited.inj exited
      refine ⟨rfl, ?_, copies⟩
      exact execution.exited_marker
    · cases (linux_exec_message execution images reads writes).1
    · cases (linux_exec_message execution images reads writes).1
    · cases impossible
  | _ => exact footprint.elim

/-- readAll's message corollary at the shim's specification level.  For all open flags `F`,
layouts `L`, launches `I`, and reply sequences `replies`, and every budget that fits between the
heap's start at byte 4,096 and the end of the module's 65,535 pages and bounds the heap that every
prefix of `main` allocates under `linuxHost F L I replies`, every Talos run of `_start` from the
command's initial store with enough fuel traps with a final world.  When that world's layer
events hold no `read` that fails and no `write` that fails or returns 0, the trap is the accepted
exit with status `statusOf (Linux.readData 0 events)`, 0 when the reads of descriptor 0 returned
at most `limit` bytes and 1 otherwise, and the events meet `Copies`: reads of 4,096 bytes from
descriptor 0, each but the last returning bytes, at most `limit` bytes before the last read and
`limit + 4096` in all, the last read returning none unless the bytes exceed `limit`, followed by
writes of descriptor 1 that took the bytes that the reads returned.  The module's docstring
states what the budget premise excludes. -/
theorem linux_message (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    {budget : Nat}
    (room : 4096 + budget ≤ 65536 * 65535)
    (bounded : Resource.CallPrefixBound (observedHost (linuxHost F L I replies))
      (.ofProg command.pure.program command.pure.funs) command.program
      .here 0 .nil linuxStart budget) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final message,
      run fuel command.module (Wrappers.effectIndex command.pure.module 2) linuxInitial []
          (linuxEnv F L I replies []) = .Trap final message ∧
        (ReadsSucceed final.host.world.events → WritesAdvance final.host.world.events →
          message = exitTrap ∧
            final.host.world.exited = some (statusOf (Linux.readData 0 final.host.world.events)) ∧
            Copies final.host.world.events) := by
  obtain ⟨bound, footprints⟩ := linux_footprint_bounded F L I replies room bounded
  exact ⟨bound, fun fuel enough => footprint_message (footprints fuel enough)⟩

end Verified.Examples.WasiReadAll

#print axioms Verified.Examples.WasiReadAll.exec_message
#print axioms Verified.Examples.WasiReadAll.linux_exec_message
#print axioms Verified.Examples.WasiReadAll.linux_message
