import LeanExe.Wasi.Semantics

namespace Verified.Wasi.ScriptHost

open LeanExe LeanExe.Wasi

inductive Resource where
  | first
  | second
  | third
  deriving DecidableEq, Inhabited

structure Queues where
  first : List UInt8 := []
  second : List UInt8 := []
  third : List UInt8 := []
  deriving Inhabited

def Queues.get (queues : Queues) : Resource → List UInt8
  | .first => queues.first
  | .second => queues.second
  | .third => queues.third

def Queues.set (queues : Queues) (resource : Resource) (bytes : List UInt8) : Queues :=
  match resource with
  | .first => { queues with first := bytes }
  | .second => { queues with second := bytes }
  | .third => { queues with third := bytes }

structure Links where
  stdin : Resource := .first
  stdout : Resource := .second
  stderr : Resource := .third
  deriving Inhabited

def Links.output (links : Links) : Output → Resource
  | .stdout => links.stdout
  | .stderr => links.stderr

inductive Policy where
  | returned (errno : UInt64) (valid : errno.toNat ≤ 76) (limit : UInt64)
  | trapped (message : String) (limit : UInt64)

def Policy.limit : Policy → UInt64
  | .returned _ _ limit | .trapped _ limit => limit

def Policy.transfer (policy : Policy) (committed : α) : Transfer α :=
  match policy with
  | .returned errno _ _ => .returned errno committed
  | .trapped message _ => .trapped message committed

@[simp] theorem Policy.committed (policy : Policy) (value : α) :
    (policy.transfer value).committed = value := by cases policy <;> rfl

theorem Policy.validErrno (policy : Policy) (value : α) :
    (policy.transfer value).validErrno := by
  cases policy with
  | returned errno valid limit => exact valid
  | trapped message limit => trivial

inductive ExitPolicy where
  | accepted
  | rejected (message : String)

inductive Request where
  | read (policy : Policy)
  | write (output : Output) (policy : Policy)
  | exit (policy : ExitPolicy)

structure World where
  queues : Queues := {}
  links : Links := {}
  script : List Request := []
  exited : Option UInt64 := none
  deriving Inhabited

def readPolicy : List Request → Policy × List Request
  | .read policy :: rest => (policy, rest)
  | requests => (.trapped "script: unexpected fd_read" 0, requests)

def writePolicy (output : Output) : List Request → Policy × List Request
  | .write expected policy :: rest =>
      if output = expected then (policy, rest)
      else (.trapped "script: unexpected output descriptor" 0, .write expected policy :: rest)
  | requests => (.trapped "script: unexpected fd_write" 0, requests)

def exitPolicy : List Request → ExitPolicy × List Request
  | .exit policy :: rest => (policy, rest)
  | requests => (.rejected "script: unexpected proc_exit", requests)

def bytesOfList (bytes : List UInt8) : Bytes := ⟨⟨bytes.toArray⟩⟩

def readData (world : World) (capacity : UInt64) : List UInt8 :=
  (world.queues.get world.links.stdin).take
    (min capacity.toNat (readPolicy world.script).1.limit.toNat)

def writeData (world : World) (output : Output) (bytes : Bytes) : List UInt8 :=
  bytes.data.data.toList.take (writePolicy output world.script).1.limit.toNat

def readStep (world : World) (capacity : UInt64) : Transfer Bytes × World :=
  let selected := readPolicy world.script
  let data := readData world capacity
  (selected.1.transfer (bytesOfList data),
    { world with
      script := selected.2
      queues := world.queues.set world.links.stdin
        ((world.queues.get world.links.stdin).drop data.length) })

def writeStep (world : World) (output : Output) (bytes : Bytes) : Transfer UInt64 × World :=
  let selected := writePolicy output world.script
  let data := writeData world output bytes
  let resource := world.links.output output
  (selected.1.transfer (UInt64.ofNat data.length),
    { world with
      script := selected.2
      queues := world.queues.set resource ((world.queues.get resource) ++ data) })

def exitStep (world : World) (code : UInt64) : Option String × World :=
  let selected := exitPolicy world.script
  match selected.1 with
  | .accepted => (none, { world with script := selected.2, exited := some code })
  | .rejected message => (some message, { world with script := selected.2 })

theorem readData_bound (world : World) (capacity : UInt64) :
    (readData world capacity).length ≤ capacity.toNat := by
  simp only [readData, List.length_take]
  exact Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_left _ _)

theorem writeData_bound (world : World) (output : Output) (bytes : Bytes) :
    (writeData world output bytes).length ≤ bytes.data.size := by
  simp only [writeData, List.length_take, Array.length_toList, ByteArray.size]
  exact Nat.min_le_right _ _

theorem writeData_toNat (world : World) (output : Output) (bytes : Bytes) :
    (UInt64.ofNat (writeData world output bytes).length).toNat =
      (writeData world output bytes).length := by
  apply UInt64.toNat_ofNat_of_lt'
  have bound : (writeData world output bytes).length ≤
      (writePolicy output world.script).1.limit.toNat := by
    simp only [writeData, List.length_take]
    exact Nat.min_le_left _ _
  exact Nat.lt_of_le_of_lt bound (Policy.limit (writePolicy output world.script).1).toNat_lt

theorem readStep_bound (world : World) (capacity : UInt64) :
    (readStep world capacity).1.committed.data.size ≤ capacity.toNat ∧
      (readStep world capacity).1.validErrno := by
  constructor
  · simpa only [readStep, Policy.committed, bytesOfList, ByteArray.size, List.size_toArray] using
      readData_bound world capacity
  · exact Policy.validErrno _ _

theorem writeStep_bound (world : World) (output : Output) (bytes : Bytes) :
    (writeStep world output bytes).1.committed.toNat ≤ bytes.data.size ∧
      (writeStep world output bytes).1.validErrno := by
  constructor
  · simpa only [writeStep, Policy.committed, writeData_toNat] using
      writeData_bound world output bytes
  · exact Policy.validErrno _ _

theorem exitStep_recorded {world after : World} {code : UInt64}
    (step : exitStep world code = (none, after)) : after.exited = some code := by
  cases policy : (exitPolicy world.script).1 with
  | accepted =>
      simp only [exitStep, policy] at step
      cases step
      rfl
  | rejected message =>
      simp only [exitStep, policy, Prod.mk.injEq, Option.some_ne_none, false_and] at step

theorem exitStep_rejected {world after : World} {code : UInt64} {message : String}
    (step : exitStep world code = (some message, after)) : after.exited = world.exited := by
  cases policy : (exitPolicy world.script).1 with
  | accepted =>
      simp only [exitStep, policy, Prod.mk.injEq] at step
      cases step.1
  | rejected cause =>
      simp only [exitStep, policy, Prod.mk.injEq, Option.some.injEq] at step
      obtain ⟨_, rfl⟩ := step
      rfl

def sourceHost : Host World where
  exited := World.exited
  read world capacity reply after := readStep world capacity = (reply, after)
  write world output bytes reply after := writeStep world output bytes = (reply, after)
  exit world code after := exitStep world code = (none, after)
  exitTrap world code message after := exitStep world code = (some message, after)
  read_bound := by
    intro world capacity reply after step
    have bound := readStep_bound world capacity
    rw [step] at bound
    exact bound
  write_bound := by
    intro world output bytes reply after step
    have bound := writeStep_bound world output bytes
    rw [step] at bound
    exact bound
  read_exited := by
    intro world capacity reply after step
    have same := congrArg (fun result : Transfer Bytes × World => result.2.exited) step
    exact same.symm
  write_exited := by
    intro world output bytes reply after step
    have same := congrArg (fun result : Transfer UInt64 × World => result.2.exited) step
    exact same.symm
  exit_recorded := exitStep_recorded
  exitTrap_exited := exitStep_rejected

end Verified.Wasi.ScriptHost
