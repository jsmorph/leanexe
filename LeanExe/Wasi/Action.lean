import LeanExe.Dialect.Bytes

namespace LeanExe.Wasi

structure ReadResult where
  errno : UInt64
  bytes : Bytes

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
  | read {α : Type} (capacity : UInt64) (next : ReadResult → Action α) : Action α
  | write {α : Type} (output : Output) (bytes : Bytes)
      (next : WriteResult → Action α) : Action α
  | exit {α : Type} (code : UInt64) : Action α
  | loop {α σ : Type} (count : UInt64) (init : σ) (test : UInt64 → σ → Bool)
      (step : UInt64 → σ → Action σ) (next : σ → Action α) : Action α

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

instance : LawfulMonad Action :=
  LawfulMonad.mk' Action
    (fun action => bind_pure action)
    (fun _ _ => rfl)
    (fun action next last => bind_assoc action next last)

end Action

def readSome (capacity : UInt64) : Action ReadResult := .read capacity .pure

def writeStdoutSome (bytes : Bytes) : Action WriteResult := .write .stdout bytes .pure

def writeStderrSome (bytes : Bytes) : Action WriteResult := .write .stderr bytes .pure

def exit (code : UInt64) : Action α := .exit code

def loop (count : UInt64) (init : σ) (test : UInt64 → σ → Bool)
    (step : UInt64 → σ → Action σ) : Action σ :=
  .loop count init test step .pure

def exitStatus (code : UInt64) : UInt64 := code.toUInt32.toUInt64

@[simp] theorem exitStatus_toNat (code : UInt64) :
    (exitStatus code).toNat = code.toNat % 2 ^ 32 := by
  simp [exitStatus]

end LeanExe.Wasi
