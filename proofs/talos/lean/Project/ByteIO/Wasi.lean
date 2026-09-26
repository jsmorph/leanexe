import Project.ByteIO.Host

namespace Project.ByteIO
open Wasm

def flagsUpdate (w : World) (fd : UInt32) : World :=
  if fd = 0 then { w with stdinNonblocking := true }
  else { w with stdoutNonblocking := true }

def flagsCall (choose : World → UInt32 → UInt32) (st : Store World)
    (fd flags : UInt32) : HostResult World :=
  if 1 < fd then returnErr st 8 else
  if flags ≠ 4 then returnErr st 58 else
  let e := choose st.host fd
  if e ≠ 0 then returnErr st e else
  .Return [.i32 0] { st with host := flagsUpdate st.host fd }

def FlagsOutcome (st : Store World) (fd flags : UInt32) (result : HostResult World) : Prop :=
  (∃ e : UInt32, e ≠ 0 ∧ result = .Return [.i32 e] st) ∨
  (fd ≤ 1 ∧ flags = 4 ∧
    result = .Return [.i32 0] { st with host := flagsUpdate st.host fd })

theorem flagsCall_contract (choose : World → UInt32 → UInt32) (st : Store World)
    (fd flags : UInt32) : FlagsOutcome st fd flags (flagsCall choose st fd flags) := by
  unfold flagsCall
  split
  · exact Or.inl ⟨8, by decide, rfl⟩
  · split
    · exact Or.inl ⟨58, by decide, rfl⟩
    · dsimp only
      split
      · exact Or.inl ⟨choose st.host fd, ‹choose st.host fd ≠ 0›, rfl⟩
      · exact Or.inr ⟨by simpa [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le] using ‹¬1 < fd›, by simpa using ‹¬ flags ≠ 4›, rfl⟩

theorem flagsUpdate_streams (w : World) (fd : UInt32) :
    (flagsUpdate w fd).input = w.input ∧ (flagsUpdate w fd).output = w.output := by
  unfold flagsUpdate; split <;> exact ⟨rfl, rfl⟩

theorem flagsUpdate_nonblocking (w : World) (fd : UInt32) :
    (fd = 0 → (flagsUpdate w fd).stdinNonblocking = true) ∧
    (fd = 1 → (flagsUpdate w fd).stdoutNonblocking = true) := by
  constructor <;> intro hfd <;> subst fd <;> simp [flagsUpdate]

theorem u64_le_max_left (a b : UInt64) : a ≤ max a b := by
  change a ≤ (if a ≤ b then b else a)
  split <;> simp_all [UInt64.le_iff_toNat_le]

theorem u64_le_max_right (a b : UInt64) : b ≤ max a b := by
  change b ≤ (if a ≤ b then b else a)
  split <;> simp_all [UInt64.le_iff_toNat_le] <;> omega

abbrev ClockOracle := World → Except UInt32 UInt64

def clockCall (choose : ClockOracle) (st : Store World)
    (id out : UInt32) : HostResult World :=
  if id ≠ 1 then returnErr st 28 else
  if ¬ inBounds st.mem out.toNat 8 then returnErr st 21 else
  match choose st.host with
  | .error e => returnErr st (errno e)
  | .ok proposed =>
      let now := max st.host.now proposed
      .Return [.i32 0] { st with
        mem := st.mem.write64 out now
        host := { st.host with now } }

def ClockOutcome (st : Store World) (id out : UInt32) (result : HostResult World) : Prop :=
  (∃ e : UInt32, e ≠ 0 ∧ result = .Return [.i32 e] st) ∨
  (id = 1 ∧ inBounds st.mem out.toNat 8 ∧ ∃ now : UInt64, st.host.now ≤ now ∧
    result = .Return [.i32 0]
      { st with mem := st.mem.write64 out now, host := { st.host with now } })

theorem clockCall_contract (choose : ClockOracle) (st : Store World) (id out : UInt32) :
    ClockOutcome st id out (clockCall choose st id out) := by
  unfold clockCall
  split
  · exact Or.inl ⟨28, by decide, rfl⟩
  · split
    · exact Or.inl ⟨21, by decide, rfl⟩
    · split
      · exact Or.inl ⟨_, errno_ne_zero _, rfl⟩
      · exact Or.inr ⟨by simpa using ‹¬ id ≠ 1›, by simpa using ‹¬ ¬ _›,
          _, u64_le_max_left _ _, rfl⟩

structure PollDecision where
  now : UInt64
  ready : Bool
  fdError : UInt16 := 0
  hangup : Bool := false
  deriving Repr, DecidableEq

structure Event where
  userdata : UInt64
  error : UInt16
  kind : UInt8
  bytes : UInt64 := 0
  hangup : Bool := false
  deriving Repr, DecidableEq

def encodeEvent (event : Event) : Bytes :=
  let mem := (Mem.empty 1).write64 0 event.userdata
  let mem := (mem.write16 8 event.error.toUInt32).write8 10 event.kind
  let mem := (mem.write64 16 event.bytes).write16 24 (if event.hangup then 1 else 0)
  readBytes mem 0 32

@[simp] theorem encodeEvent_length (event : Event) : (encodeEvent event).length = 32 := by
  simp [encodeEvent]

/-- The compiler submits an absolute monotonic deadline followed by one
descriptor subscription. A returning poll either reports readiness or has
reached that deadline. Blocking inside the host is abstracted by this choice.
The native host may report both events; deadline expiry has priority in wait. -/
def pollTime (old deadline : UInt64) (decision : PollDecision) : UInt64 :=
  if decision.ready then max old decision.now else max deadline (max old decision.now)

def pollEvents (old deadline clockData fdData : UInt64) (kind : UInt8)
    (decision : PollDecision) : List Event :=
  (if deadline ≤ pollTime old deadline decision then
    [{ userdata := clockData, error := 0, kind := 0 }] else []) ++
  (if decision.ready then [{ userdata := fdData, error := decision.fdError, kind, bytes := 1, hangup := decision.hangup }] else [])

theorem pollTime_monotone (old deadline : UInt64) (decision : PollDecision) :
    old ≤ pollTime old deadline decision := by
  unfold pollTime
  split
  · exact u64_le_max_left _ _
  · exact UInt64.le_trans (u64_le_max_left _ _) (u64_le_max_right _ _)

theorem pollEvents_count (old deadline clockData fdData : UInt64) (kind : UInt8)
    (decision : PollDecision) :
    1 ≤ (pollEvents old deadline clockData fdData kind decision).length ∧
    (pollEvents old deadline clockData fdData kind decision).length ≤ 2 := by
  unfold pollEvents
  by_cases hr : decision.ready = true
  · simp [hr]; split <;> simp
  · have ht : deadline ≤ pollTime old deadline decision := by
      simpa [pollTime, hr] using u64_le_max_left deadline (max old decision.now)
    simp [hr, ht]

theorem poll_before_deadline_ready (old deadline : UInt64) (decision : PollDecision)
    (h : pollTime old deadline decision < deadline) : decision.ready = true := by
  by_contra hn
  have : deadline ≤ pollTime old deadline decision := by
    simpa [pollTime, hn] using u64_le_max_left deadline (max old decision.now)
  rw [UInt64.lt_iff_toNat_lt] at h
  rw [UInt64.le_iff_toNat_le] at this
  omega

def commitPoll (st : Store World) (out countPtr : UInt32) (now : UInt64)
    (events : List Event) : Store World :=
  { st with
    mem := (writeBytes st.mem out.toNat (events.flatMap encodeEvent)).write32 countPtr
      (UInt32.ofNat events.length)
    host := { st.host with now } }

theorem commitPoll_frame (st : Store World) (out countPtr : UInt32) (now : UInt64)
    (events : List Event) (a : Nat)
    (he : a < out.toNat ∨ out.toNat + 32 * events.length ≤ a)
    (hc : a < countPtr.toNat ∨ countPtr.toNat + 4 ≤ a) :
    (commitPoll st out countPtr now events).mem.bytes a = st.mem.bytes a := by
  have hlen : (events.flatMap encodeEvent).length = 32 * events.length := by
    induction events with
    | nil => simp
    | cons e es ih => simp [ih]; omega
  simp only [commitPoll]
  rw [write32_frame _ _ _ _ hc]
  apply writeBytes_frame
  simpa [hlen] using he

theorem commitPoll_streams (st : Store World) (out countPtr : UInt32) (now : UInt64)
    (events : List Event) :
    (commitPoll st out countPtr now events).host.input = st.host.input ∧
    (commitPoll st out countPtr now events).host.output = st.host.output := ⟨rfl, rfl⟩

def exitHost : HostFn World where
  params := [.i32]
  results := []
  invoke st args := match args with
    | [.i32 code] => .Trap { st with host := { st.host with exited := some code } } "proc_exit"
    | _ => .Trap st "proc_exit: invalid arguments"

theorem exit_records_status (st : Store World) (code : UInt32) :
    exitHost.invoke st [.i32 code] =
      .Trap { st with host := { st.host with exited := some code } } "proc_exit" := rfl

abbrev PollOracle := World → UInt64 → Except UInt32 PollDecision

def canonicalPoll (mem : Mem) (input : UInt32) : Prop :=
  mem.read8 (input + 8) = 0 ∧ mem.read32 (input + 16) = 1 ∧
  mem.read16 (input + 40) = 1 ∧
  (mem.read8 (input + 56) = 1 ∨ mem.read8 (input + 56) = 2) ∧
  mem.read32 (input + 64) = (mem.read8 (input + 56)).toUInt32 - 1

instance (mem : Mem) (input : UInt32) : Decidable (canonicalPoll mem input) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def pollCall (choose : PollOracle) (st : Store World)
    (input out count countPtr : UInt32) : HostResult World :=
  if count ≠ 2 then returnErr st 28 else
  if ¬ (inBounds st.mem input.toNat 96 ∧ inBounds st.mem out.toNat 64 ∧
      inBounds st.mem countPtr.toNat 4) then returnErr st 21 else
  if ¬ canonicalPoll st.mem input then returnErr st 28 else
  let deadline := st.mem.read64 (input + 24)
  match choose st.host deadline with
  | .error e => returnErr st (errno e)
  | .ok choice =>
      .Return [.i32 0] (commitPoll st out countPtr (pollTime st.host.now deadline choice)
        (pollEvents st.host.now deadline (st.mem.read64 input) (st.mem.read64 (input + 48))
          (st.mem.read8 (input + 56)) choice))

/-- This contract covers the two-subscription form used by every generated
ByteIO wait. Single-subscription and relative-deadline native-host calls are
outside this generated-program profile. -/
def PollOutcome (st : Store World) (input out count countPtr : UInt32)
    (result : HostResult World) : Prop :=
  (∃ e : UInt32, e ≠ 0 ∧ result = .Return [.i32 e] st) ∨
  (count = 2 ∧ inBounds st.mem input.toNat 96 ∧ inBounds st.mem out.toNat 64 ∧
    inBounds st.mem countPtr.toNat 4 ∧ canonicalPoll st.mem input ∧
    ∃ choice,
      let deadline := st.mem.read64 (input + 24)
      let now := pollTime st.host.now deadline choice
      let events := pollEvents st.host.now deadline (st.mem.read64 input)
        (st.mem.read64 (input + 48)) (st.mem.read8 (input + 56)) choice
      st.host.now ≤ now ∧ 1 ≤ events.length ∧ events.length ≤ 2 ∧
      (now < deadline → choice.ready = true) ∧
      result = .Return [.i32 0] (commitPoll st out countPtr now events))

theorem pollCall_contract (choose : PollOracle) (st : Store World)
    (input out count countPtr : UInt32) :
    PollOutcome st input out count countPtr (pollCall choose st input out count countPtr) := by
  unfold pollCall
  split
  · exact Or.inl ⟨28, by decide, rfl⟩
  · split
    · exact Or.inl ⟨21, by decide, rfl⟩
    · split
      · exact Or.inl ⟨28, by decide, rfl⟩
      · dsimp only
        split
        · exact Or.inl ⟨_, errno_ne_zero _, rfl⟩
        · right
          simp only [not_not] at *
          refine ⟨‹count = 2›, ‹_ ∧ _ ∧ _›.1, ‹_ ∧ _ ∧ _›.2.1,
            ‹_ ∧ _ ∧ _›.2.2, ‹canonicalPoll _ _›, _, pollTime_monotone _ _ _,
            (pollEvents_count _ _ _ _ _ _).1, (pollEvents_count _ _ _ _ _ _).2,
            poll_before_deadline_ready _ _ _, rfl⟩

def flagsHost (choose : World → UInt32 → UInt32) : HostFn World where
  params := [.i32, .i32]
  results := [.i32]
  invoke st args := match args with
    | [.i32 fd, .i32 flags] => flagsCall choose st fd flags
    | _ => .Trap st "fd_fdstat_set_flags: invalid arguments"

def clockHost (choose : ClockOracle) : HostFn World where
  params := [.i32, .i64, .i32]
  results := [.i32]
  invoke st args := match args with
    | [.i32 id, .i64 _, .i32 out] => clockCall choose st id out
    | _ => .Trap st "clock_time_get: invalid arguments"

def pollHost (choose : PollOracle) : HostFn World where
  params := [.i32, .i32, .i32, .i32]
  results := [.i32]
  invoke st args := match args with
    | [.i32 input, .i32 out, .i32 count, .i32 countPtr] => pollCall choose st input out count countPtr
    | _ => .Trap st "poll_oneoff: invalid arguments"

def flagsContract : HostContract World := fun st args result => match args with
  | [.i32 fd, .i32 flags] => FlagsOutcome st fd flags result
  | _ => result = .Trap st "fd_fdstat_set_flags: invalid arguments"

def clockContract : HostContract World := fun st args result => match args with
  | [.i32 id, .i64 _, .i32 out] => ClockOutcome st id out result
  | _ => result = .Trap st "clock_time_get: invalid arguments"

def pollContract : HostContract World := fun st args result => match args with
  | [.i32 input, .i32 out, .i32 count, .i32 countPtr] => PollOutcome st input out count countPtr result
  | _ => result = .Trap st "poll_oneoff: invalid arguments"

def exitContract : HostContract World := fun st args result => match args with
  | [.i32 code] => result = .Trap { st with host := { st.host with exited := some code } } "proc_exit"
  | _ => result = .Trap st "proc_exit: invalid arguments"

theorem flagsHost_contract (choose : World → UInt32 → UInt32) (st : Store World) (args : List Value) :
    flagsContract st args ((flagsHost choose).invoke st args) := by
  unfold flagsContract flagsHost
  dsimp only
  split
  · exact flagsCall_contract choose st _ _
  · split <;> simp_all

theorem clockHost_contract (choose : ClockOracle) (st : Store World) (args : List Value) :
    clockContract st args ((clockHost choose).invoke st args) := by
  unfold clockContract clockHost
  dsimp only
  split
  · exact clockCall_contract choose st _ _
  · split <;> simp_all

theorem pollHost_contract (choose : PollOracle) (st : Store World) (args : List Value) :
    pollContract st args ((pollHost choose).invoke st args) := by
  unfold pollContract pollHost
  dsimp only
  split
  · exact pollCall_contract choose st _ _ _ _
  · split <;> simp_all
    rename_i input out count countPtr h
    exact (h input out count countPtr rfl rfl rfl rfl).elim

theorem exitHost_contract (st : Store World) (args : List Value) :
    exitContract st args (exitHost.invoke st args) := by
  unfold exitContract exitHost
  dsimp only
  split
  · rfl
  · split <;> simp_all

def wasiImports : List ImportDecl :=
  [{ module := "wasi_snapshot_preview1", name := "fd_read", params := [.i32, .i32, .i32, .i32], results := [.i32] },
   { module := "wasi_snapshot_preview1", name := "fd_write", params := [.i32, .i32, .i32, .i32], results := [.i32] },
   { module := "wasi_snapshot_preview1", name := "fd_fdstat_set_flags", params := [.i32, .i32], results := [.i32] },
   { module := "wasi_snapshot_preview1", name := "clock_time_get", params := [.i32, .i64, .i32], results := [.i32] },
   { module := "wasi_snapshot_preview1", name := "poll_oneoff", params := [.i32, .i32, .i32, .i32], results := [.i32] },
   { module := "wasi_snapshot_preview1", name := "proc_exit", params := [.i32], results := [] }]

def wasiSpec : HostSpec World :=
  { contracts := [readContract, writeContract, flagsContract, clockContract, pollContract, exitContract] }

def wasiEnv (read write : TransferOracle) (flags : World → UInt32 → UInt32)
    (clock : ClockOracle) (poll : PollOracle) : HostEnv World :=
  { funcs := [readHost read, writeHost write, flagsHost flags, clockHost clock, pollHost poll, exitHost] }

theorem wasiEnv_satisfies (read write : TransferOracle) (flags : World → UInt32 → UInt32)
    (clock : ClockOracle) (poll : PollOracle) (m : Wasm.Module) (hm : m.imports = wasiImports) :
    (wasiEnv read write flags clock poll).Satisfies m wasiSpec := by
  intro i hi
  rw [hm] at hi
  change i < 6 at hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, rfl, rfl, readHost_contract read⟩
  · exact ⟨_, _, rfl, rfl, writeHost_contract write⟩
  · exact ⟨_, _, rfl, rfl, flagsHost_contract flags⟩
  · exact ⟨_, _, rfl, rfl, clockHost_contract clock⟩
  · exact ⟨_, _, rfl, rfl, pollHost_contract poll⟩
  · exact ⟨_, _, rfl, rfl, exitHost_contract⟩

#print axioms wasiEnv_satisfies
#print axioms pollCall_contract

#print axioms flagsCall_contract
#print axioms clockCall_contract
#print axioms pollTime_monotone
#print axioms pollEvents_count
#print axioms poll_before_deadline_ready
#print axioms commitPoll_frame
#print axioms exit_records_status

end Project.ByteIO
