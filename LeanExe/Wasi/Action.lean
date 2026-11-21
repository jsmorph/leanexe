import LeanExe.Wasi.Calls
import LeanExe.Wasi.Window

namespace LeanExe.Wasi

structure ReadResult where
  errno : UInt64
  bytes : Bytes

/-- What a read of standard input passes to its continuation: the errno, the bytes read, empty
after an errno, and the bytes that the read's region holds after the call, its range, which begin
with the bytes read after a success. -/
structure ReadReply where
  errno : UInt64
  bytes : Bytes
  range : Bytes

structure WriteResult where
  errno : UInt64
  count : UInt64

inductive Output where
  | stdout
  | stderr
  deriving Repr, DecidableEq

def Output.fd : Output → UInt64
  | .stdout => 1
  | .stderr => 2

inductive Action : Type → Type 1 where
  | pure {α : Type} (value : α) : Action α
  | read {α : Type} (capacity : UInt64) (next : ReadReply → Action α) : Action α
  | write {α : Type} (output : Output) (bytes : Bytes)
      (next : WriteResult → Action α) : Action α
  | exit {α : Type} (code : UInt64) : Action α
  | loop {α σ : Type} (count : UInt64) (init : σ) (test : UInt64 → σ → Bool)
      (step : UInt64 → σ → Action σ) (next : σ → Action α) : Action α
  | sys {α : Type} (call : Call) (args : List Arg) (next : Reply → Action α) : Action α

namespace Action

def bind {α β : Type} (action : Action α) (next : α → Action β) : Action β :=
  match action with
  | .pure value => next value
  | .read capacity continuation => .read capacity fun result => bind (continuation result) next
  | .write output bytes continuation =>
    .write output bytes fun result => bind (continuation result) next
  | .exit code => .exit code
  | .loop count init test step continuation =>
    .loop count init test step fun state => bind (continuation state) next
  | .sys call args continuation => .sys call args fun reply => bind (continuation reply) next

instance : Monad Action where
  pure := Action.pure
  bind := Action.bind

theorem bind_pure : {α : Type} → (action : Action α) → bind action Action.pure = action
  | _, .pure _ => rfl
  | _, .read capacity next => by
    simp only [bind]
    congr
    funext result
    exact bind_pure (next result)
  | _, .write output bytes next => by
    simp only [bind]
    congr
    funext result
    exact bind_pure (next result)
  | _, .exit _ => rfl
  | _, .loop count init test step next => by
    simp only [bind]
    congr
    funext state
    exact bind_pure (next state)
  | _, .sys call args next => by
    simp only [bind]
    congr
    funext reply
    exact bind_pure (next reply)

theorem bind_assoc {α β γ : Type} (action : Action α) (next : α → Action β)
    (last : β → Action γ) :
    bind (bind action next) last = bind action (fun value => bind (next value) last) := by
  match action with
  | .pure _ => rfl
  | .read capacity continuation =>
    simp only [bind]
    congr
    funext result
    exact bind_assoc (continuation result) next last
  | .write output bytes continuation =>
    simp only [bind]
    congr
    funext result
    exact bind_assoc (continuation result) next last
  | .exit _ => rfl
  | .loop count init test step continuation =>
    simp only [bind]
    congr
    funext state
    exact bind_assoc (continuation state) next last
  | .sys call args continuation =>
    simp only [bind]
    congr
    funext reply
    exact bind_assoc (continuation reply) next last

instance : LawfulMonad Action :=
  LawfulMonad.mk' Action
    (fun action => bind_pure action)
    (fun _ _ => rfl)
    (fun action next last => bind_assoc action next last)

end Action

/-- The result of a call that fills a window of a caller's buffer: the errno, the number of bytes
that the call placed from the window's start, and the buffer.  After an errno the count is 0 and the
window's bytes are 0. -/
structure FillResult where
  errno : UInt64
  count : UInt64
  buffer : Bytes

/-- The result of a call that filled the window of `buffer` that `start` and `count` name: on
errno 0 the count `used` and `buffer` with the window's bytes replaced by `bytes`, the bytes of the
whole window after the call, and after an errno the count 0 and `buffer` with the window's bytes
set to 0. -/
def FillResult.of (buffer : Bytes) (start count errno used : UInt64) (bytes : Bytes) :
    FillResult :=
  if errno = 0 then ⟨0, used, buffer.splice (buffer.window start count).1 bytes⟩
  else ⟨errno, 0, buffer.clear start count⟩

/-- Calls `fd_read` once for stdin into the window of `buffer` that `start` and `count` name.  For a
window of `2^32` bytes or more, `Exec`'s rule `read_reject` gives the read errno 61 without a call.
On errno 0 the result holds the number of bytes read and `buffer` with the window's bytes replaced
by the read's range, whose first bytes are those read, and after an errno the count 0 and `buffer`
with the window's bytes set to 0. -/
def readStdin (buffer : Bytes) (start count : UInt64) : Action FillResult :=
  .read (buffer.windowLength start count) fun reply =>
    .pure (FillResult.of buffer start count reply.errno reply.bytes.size reply.range)

/-- Calls `fd_write` once for stdout with the bytes of the window of `buffer` that `start` and
`count` name. -/
def writeStdout (buffer : Bytes) (start count : UInt64) : Action WriteResult :=
  .write .stdout (buffer.range start count) .pure

/-- Calls `fd_write` once for stderr with the bytes of the window of `buffer` that `start` and
`count` name. -/
def writeStderr (buffer : Bytes) (start count : UInt64) : Action WriteResult :=
  .write .stderr (buffer.range start count) .pure

def exit (code : UInt64) : Action α := .exit code

def loop (count : UInt64) (init : σ) (test : UInt64 → σ → Bool)
    (step : UInt64 → σ → Action σ) : Action σ :=
  .loop count init test step .pure

def exitStatus (code : UInt64) : UInt64 := code.toUInt32.toUInt64

@[simp] theorem exitStatus_toNat (code : UInt64) :
    (exitStatus code).toNat = code.toNat % 2 ^ 32 := by
  simp [exitStatus]

end LeanExe.Wasi
