import LeanExe.Wasi.Semantics

namespace LeanExe.Wasi

structure NativeHost where
  read : UInt64 → IO (Transfer Bytes)
  write : Output → Bytes → IO (Transfer UInt64)
  exit : UInt64 → IO (Except String Unit)

namespace NativeHost

/-- Reads report errno zero and the stream's bytes.  Writes report full success after flushing.
Stream exceptions remain `IO.Error`s, without a claim about syscall progress during the failed
operation.  Exit returns a terminal outcome without terminating the Lean process. -/
def ofStreams (stdin stdout stderr : IO.FS.Stream) : NativeHost where
  read capacity := do
    let bytes ← stdin.read capacity.toUSize
    pure (.returned 0 ⟨bytes⟩)
  write output bytes := do
    let stream := match output with
      | .stdout => stdout
      | .stderr => stderr
    stream.write bytes.data
    stream.flush
    pure (.returned 0 bytes.size)
  exit _ := pure (.ok ())

def stdio : BaseIO NativeHost := do
  return ofStreams (← IO.getStdin) (← IO.getStdout) (← IO.getStderr)

end NativeHost

namespace Action

private instance {α : Type} (reply : Transfer α) : Decidable reply.validErrno :=
  match reply with
  | .returned errno _ => inferInstanceAs (Decidable (errno.toNat ≤ 76))
  | .trapped _ _ => isTrue trivial

private def runLoop (remaining index : UInt64) (state : σ)
    (test : UInt64 → σ → Bool) (step : UInt64 → σ → IO (Outcome σ)) :
    IO (Outcome σ) := do
  if h : remaining = 0 then
    return .returned state
  if !test index state then
    return .returned state
  match ← step index state with
  | .returned state' => runLoop (remaining - 1) (index + 1) state' test step
  | .exited code => return .exited code
  | .trapped message => return .trapped message
termination_by remaining.toNat
decreasing_by
  have hNat : remaining.toNat ≠ 0 := by
    intro hZero
    apply h
    apply UInt64.toNat_inj.mp
    simpa only [UInt64.toNat_zero] using hZero
  have hOne : (1 : UInt64) ≤ remaining := by
    apply UInt64.le_iff_toNat_le.mpr
    change 1 ≤ remaining.toNat
    omega
  rw [UInt64.toNat_sub_of_le _ _ hOne]
  change remaining.toNat - 1 < remaining.toNat
  omega

/-- Execute callbacks in source order.  Explicit host traps and exits are terminal.  An IO
exception propagates to the caller, without executing the action's continuation. -/
def run {α : Type} (action : Action α) (host : NativeHost) : IO (Outcome α) :=
  match action with
  | .pure value => Pure.pure (.returned value)
  | .read capacity next => do
    if capacity ≥ 4294967296 then
      return ← run (next ⟨61, Bytes.empty⟩) host
    let reply ← host.read capacity
    if reply.committed.data.size > capacity.toNat ∨ ¬reply.validErrno then
      throw (IO.userError "WASI native host returned an invalid read reply")
    match reply with
    | .returned errno committed => run (next (readResult errno committed)) host
    | .trapped message _ => Pure.pure (.trapped message)
  | .write output bytes next => do
    let reply ← host.write output bytes
    if reply.committed.toNat > bytes.data.size ∨ ¬reply.validErrno then
      throw (IO.userError "WASI native host returned an invalid write reply")
    match reply with
    | .returned errno committed => run (next (writeResult errno committed)) host
    | .trapped message _ => Pure.pure (.trapped message)
  | .exit code => do
    let status := exitStatus code
    match ← host.exit status with
    | .ok () => Pure.pure (.exited status)
    | .error message => Pure.pure (.trapped message)
  | .loop count init test step next => do
    match ← runLoop count 0 init test (fun index state => run (step index state) host) with
    | .returned state => run (next state) host
    | .exited code => Pure.pure (.exited code)
    | .trapped message => Pure.pure (.trapped message)
termination_by structural action

def runStdio (action : Action α) : IO (Outcome α) := do
  action.run (← NativeHost.stdio)

end Action

end LeanExe.Wasi
