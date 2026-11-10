import LeanExe.Wasi.Semantics

/-! `readAll limit` reads the standard input into one byte string until a read returns an errno
or no bytes, or until the string holds more than `limit` bytes.  It is a bounded loop of reads of
capacity 4,096 through `readSome`, so `Exec`, `Prefix`, and the native interpreter give it the
meaning of those reads, and its definition unfolds to one `loop` node whatever the limit.  The
verified compiler compiles it to one buffer of `limit + 4,096` bytes whose unused tail receives
each read. -/

namespace LeanExe.Wasi

/-- The bytes of `first` followed by those of `second`. -/
def appendBytes (first second : Bytes) : Bytes := ⟨first.data ++ second.data⟩

@[simp] theorem appendBytes_size (first second : Bytes) :
    (appendBytes first second).data.size = first.data.size + second.data.size :=
  ByteArray.size_append

theorem appendBytes_get_left {first second : Bytes} {i : Nat}
    (hi : i < (appendBytes first second).data.size) (left : i < first.data.size) :
    (appendBytes first second).data[i] = first.data[i] :=
  ByteArray.getElem_append_left left

theorem appendBytes_get_right {first second : Bytes} {i : Nat}
    (hi : i < (appendBytes first second).data.size) (right : first.data.size ≤ i) :
    (appendBytes first second).data[i] =
      second.data[i - first.data.size]'(by simp only [appendBytes_size] at hi; omega) :=
  ByteArray.getElem_append_right right

/-- The state of the loop of `readAll`: the errno of a read that failed, the bytes read, and
whether the loop has ended. -/
structure ReadAllState where
  errno : UInt64
  held : Bytes
  done : Bool

/-- The state after a read that returned `reply`: an errno or a read of no bytes ends the loop
with the bytes held, and other bytes are appended, ending the loop when they exceed `limit`. -/
def readAllStep (limit : UInt64) (state : ReadAllState) (reply : ReadResult) : ReadAllState :=
  if reply.errno ≠ 0 then ⟨reply.errno, state.held, true⟩
  else if reply.bytes.data.size = 0 then ⟨0, state.held, true⟩
  else
    let held := appendBytes state.held reply.bytes
    ⟨0, held, decide (limit.toNat < held.data.size)⟩

def readAllTest (_ : UInt64) (state : ReadAllState) : Bool := !state.done

def readAllRead (limit : UInt64) (_ : UInt64) (state : ReadAllState) : Action ReadAllState :=
  Action.bind (readSome 4096) fun reply => .pure (readAllStep limit state reply)

def readAllResult (state : ReadAllState) : Action ReadResult := .pure ⟨state.errno, state.held⟩

/-- The standard input in one byte string: the errno of a read that failed, or 0, with the bytes
read before it.  The bytes exceed `limit` only when the input does, and then by less than 4,096.
Each read that continues the loop adds a byte, so its `limit + 2` passes always suffice.  A limit
of `2 ^ 32 - 4096` or more returns errno 61 (overflow) and no bytes before any read. -/
def readAll (limit : UInt64) : Action ReadResult :=
  if limit.toNat < 4294963200 then
    .loop (UInt64.ofNat (limit.toNat + 2)) ⟨0, Bytes.empty, false⟩ readAllTest
      (readAllRead limit) readAllResult
  else .pure ⟨61, Bytes.empty⟩

theorem readAllRead_returned {World : Type} {host : Host World} {limit index : UInt64}
    {state : ReadAllState} {world after : World} {errno : UInt64} {committed : Bytes}
    (reply : host.read world 4096 (.returned errno committed) after) :
    Exec host (readAllRead limit index state) world [.read 4096 (.returned errno committed)]
      (.returned (readAllStep limit state (readResult errno committed))) after :=
  .read_return (by decide) reply (.pure after _)

theorem readAllRead_trapped {World : Type} {host : Host World} {limit index : UInt64}
    {state : ReadAllState} {world after : World} {message : String} {committed : Bytes}
    (reply : host.read world 4096 (.trapped message committed) after) :
    Exec host (readAllRead limit index state) world [.read 4096 (.trapped message committed)]
      (.trapped message) after :=
  .read_trap (by decide) reply

/-- A loop whose state has ended returns the state's errno and bytes. -/
theorem readAll_finish {World : Type} {host : Host World} {limit : UInt64} {world : World}
    {state : ReadAllState} (done : state.done = true) :
    ∀ remaining index, LoopExec host remaining index state readAllTest (readAllRead limit)
      readAllResult world [] (.returned ⟨state.errno, state.held⟩) world
  | 0, _ => .zero (.pure world _)
  | _ + 1, _ => .stop (by simp only [readAllTest, done, Bool.not_true]) (.pure world _)

theorem readAllStep_failed {limit errno : UInt64} {state : ReadAllState} {committed : Bytes}
    (failure : errno ≠ 0) :
    readAllStep limit state (readResult errno committed) = ⟨errno, state.held, true⟩ := by
  simp only [readAllStep, readResult, ne_eq, failure, not_false_eq_true, ↓reduceIte]

theorem readAllStep_ended {limit : UInt64} {state : ReadAllState} {committed : Bytes}
    (empty : committed.data.size = 0) :
    readAllStep limit state (readResult 0 committed) = ⟨0, state.held, true⟩ := by
  simp only [readAllStep, readResult, ne_eq, not_true_eq_false, ↓reduceIte, empty]

theorem readAllStep_appended {limit : UInt64} {state : ReadAllState} {committed : Bytes}
    (nonempty : committed.data.size ≠ 0) :
    readAllStep limit state (readResult 0 committed) =
      ⟨0, appendBytes state.held committed,
        decide (limit.toNat < state.held.data.size + committed.data.size)⟩ := by
  simp only [readAllStep, readResult, ne_eq, not_true_eq_false, ↓reduceIte, nonempty,
    appendBytes_size]

private theorem readAllLoop_size {World : Type} {host : Host World} {limit : UInt64} :
    ∀ (remaining index : Nat) (state : ReadAllState),
      state.held.data.size ≤ limit.toNat + 4096 →
      (state.done = false → state.held.data.size ≤ limit.toNat) →
      ∀ {world trace result final},
      LoopExec host remaining index state readAllTest (readAllRead limit) readAllResult world
        trace (.returned result) final →
      result.bytes.data.size ≤ limit.toNat + 4096
  | 0, _, state, bound, _, _, _, _, _, execution => by
    cases execution with
    | zero next => cases next; exact bound
  | remaining + 1, index, state, bound, open_, _, _, _, _, execution => by
    cases execution with
    | stop _ next => cases next; exact bound
    | next test step rest =>
      have small := open_ (by simpa only [readAllTest, Bool.not_eq_true'] using test)
      change Exec host (.read 4096 fun reply => .pure (readAllStep limit state reply))
        _ _ _ _ at step
      cases step with
      | read_reject capacity _ => exact absurd capacity (by decide)
      | @read_return _ _ _ _ _ _ _ _ errno committed _ reply next =>
        have size := (host.read_bound reply).1
        simp only [Transfer.committed, UInt64.reduceToNat] at size
        cases next
        refine readAllLoop_size remaining (index + 1) _ ?_ ?_ rest
        · by_cases failure : errno = 0
          · subst failure
            by_cases empty : committed.data.size = 0
            · rw [readAllStep_ended empty]
              dsimp only
              omega
            · rw [readAllStep_appended empty]
              dsimp only
              simp only [appendBytes_size]
              omega
          · rw [readAllStep_failed failure]
            dsimp only
            omega
        · intro open'
          by_cases failure : errno = 0
          · subst failure
            by_cases empty : committed.data.size = 0
            · rw [readAllStep_ended empty]
              dsimp only
              exact small
            · rw [readAllStep_appended empty] at open' ⊢
              dsimp only at open' ⊢
              simp only [appendBytes_size]
              simp only [decide_eq_false_iff_not] at open'
              omega
          · rw [readAllStep_failed failure] at open'
            simp at open'

/-- Every returned string holds at most `limit + 4,096` bytes. -/
theorem readAll_size {World : Type} {host : Host World} {limit : UInt64}
    {world trace result final}
    (execution : Exec host (readAll limit) world trace (.returned result) final) :
    result.bytes.data.size ≤ limit.toNat + 4096 := by
  unfold readAll at execution
  split at execution
  · cases execution with
    | loop execution =>
      exact readAllLoop_size _ 0 _ (Nat.zero_le _) (fun _ => Nat.zero_le _) execution
  · cases execution
    exact Nat.zero_le _

/-- Every run of the loop of `readAll limit` from `remaining` passes, the pass `index`, the
bytes `held`, and `world` extends the events `prior` to a run of `readAll limit` from `start`. -/
def ReadAllRest {World : Type} (host : Host World) (limit : UInt64) (start : World)
    (prior : List Event) (remaining index : Nat) (held : Bytes) (world : World) : Prop :=
  ∀ trace outcome final,
    LoopExec host remaining index (⟨0, held, false⟩ : ReadAllState) readAllTest
      (readAllRead limit) readAllResult world trace outcome final →
    Exec host (readAll limit) start (prior ++ trace) outcome final

namespace ReadAllRest

variable {World : Type} {host : Host World} {limit : UInt64} {start world after : World}
  {prior : List Event} {remaining index : Nat} {held committed : Bytes}

theorem initial (world : World) (small : limit.toNat < 4294963200) :
    ReadAllRest host limit world [] (limit.toNat + 2) 0 Bytes.empty world := by
  intro trace outcome final execution
  have count : (UInt64.ofNat (limit.toNat + 2)).toNat = limit.toNat + 2 :=
    UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  simp only [readAll, small, ↓reduceIte, List.nil_append]
  exact .loop (by rw [count]; exact execution)

private theorem open_test : readAllTest (UInt64.ofNat index) ⟨0, held, false⟩ = true := rfl

/-- A read that returns an errno ends the run with that errno and the bytes held. -/
theorem failed {errno : UInt64} (rest : ReadAllRest host limit start prior (remaining + 1) index
      held world)
    (reply : host.read world 4096 (.returned errno committed) after) (failure : errno ≠ 0) :
    Exec host (readAll limit) start (prior ++ [.read 4096 (.returned errno committed)])
      (.returned ⟨errno, held⟩) after := by
  have finish := readAll_finish (host := host) (limit := limit) (world := after)
    (state := ⟨errno, held, true⟩) rfl remaining (index + 1)
  have run := LoopExec.next (remaining := remaining) open_test
    (readAllRead_returned (limit := limit) (state := ⟨0, held, false⟩) reply)
    (by rw [readAllStep_failed failure]; exact finish)
  simpa only [List.append_nil] using rest _ _ _ run

/-- A read that returns no bytes ends the run with the bytes held. -/
theorem ended (rest : ReadAllRest host limit start prior (remaining + 1) index held world)
    (reply : host.read world 4096 (.returned 0 committed) after)
    (empty : committed.data.size = 0) :
    Exec host (readAll limit) start (prior ++ [.read 4096 (.returned 0 committed)])
      (.returned ⟨0, held⟩) after := by
  have finish := readAll_finish (host := host) (limit := limit) (world := after)
    (state := ⟨0, held, true⟩) rfl remaining (index + 1)
  have run := LoopExec.next (remaining := remaining) open_test
    (readAllRead_returned (limit := limit) (state := ⟨0, held, false⟩) reply)
    (by rw [readAllStep_ended empty]; exact finish)
  simpa only [List.append_nil] using rest _ _ _ run

/-- A read that brings the bytes above the limit ends the run with them. -/
theorem over (rest : ReadAllRest host limit start prior (remaining + 1) index held world)
    (reply : host.read world 4096 (.returned 0 committed) after)
    (nonempty : committed.data.size ≠ 0)
    (above : limit.toNat < held.data.size + committed.data.size) :
    Exec host (readAll limit) start (prior ++ [.read 4096 (.returned 0 committed)])
      (.returned ⟨0, appendBytes held committed⟩) after := by
  have finish := readAll_finish (host := host) (limit := limit) (world := after)
    (state := ⟨0, appendBytes held committed, true⟩) rfl remaining (index + 1)
  have run := LoopExec.next (remaining := remaining) open_test
    (readAllRead_returned (limit := limit) (state := ⟨0, held, false⟩) reply)
    (by
      rw [readAllStep_appended nonempty]
      simp only [above, decide_true]
      exact finish)
  simpa only [List.append_nil] using rest _ _ _ run

/-- Any other successful read continues the run with its bytes appended. -/
theorem next (rest : ReadAllRest host limit start prior (remaining + 1) index held world)
    (reply : host.read world 4096 (.returned 0 committed) after)
    (nonempty : committed.data.size ≠ 0)
    (within : ¬limit.toNat < held.data.size + committed.data.size) :
    ReadAllRest host limit start (prior ++ [.read 4096 (.returned 0 committed)]) remaining
      (index + 1) (appendBytes held committed) after := by
  intro trace outcome final execution
  have run := LoopExec.next (remaining := remaining) open_test
    (readAllRead_returned (limit := limit) (state := ⟨0, held, false⟩) reply)
    (by
      rw [readAllStep_appended nonempty]
      simp only [within, decide_false]
      exact execution)
  simpa only [List.append_assoc, List.singleton_append] using rest _ _ _ run

/-- A read that the host traps ends the run with the trap. -/
theorem trapped {message : String}
    (rest : ReadAllRest host limit start prior (remaining + 1) index held world)
    (reply : host.read world 4096 (.trapped message committed) after) :
    Exec host (readAll limit) start (prior ++ [.read 4096 (.trapped message committed)])
      (.trapped message) after :=
  rest _ _ _ (LoopExec.trap open_test (readAllRead_trapped reply))

end ReadAllRest

end LeanExe.Wasi
