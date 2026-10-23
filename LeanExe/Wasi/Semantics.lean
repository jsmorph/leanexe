import LeanExe.Wasi.Action

namespace LeanExe.Wasi

inductive Transfer (α : Type) where
  | returned (errno : UInt64) (committed : α)
  | trapped (message : String) (committed : α)

def Transfer.committed : Transfer α → α
  | .returned _ value | .trapped _ value => value

def Transfer.validErrno : Transfer α → Prop
  | .returned errno _ => errno.toNat ≤ 76
  | .trapped _ _ => True

inductive Event where
  | read (capacity : UInt64) (reply : Transfer Bytes)
  | write (output : Output) (offered : Bytes) (reply : Transfer UInt64)
  | exit (code : UInt64)
  | exitTrap (code : UInt64) (message : String)

structure Host (World : Type) where
  exited : World → Option UInt64
  read : World → UInt64 → Transfer Bytes → World → Prop
  write : World → Output → Bytes → Transfer UInt64 → World → Prop
  exit : World → UInt64 → World → Prop
  exitTrap : World → UInt64 → String → World → Prop
  read_bound : ∀ {world capacity reply world'}, read world capacity reply world' →
    reply.committed.data.size ≤ capacity.toNat ∧ reply.validErrno
  write_bound : ∀ {world output bytes reply world'}, write world output bytes reply world' →
    reply.committed.toNat ≤ bytes.data.size ∧ reply.validErrno
  read_exited : ∀ {world capacity reply world'}, read world capacity reply world' →
    exited world' = exited world
  write_exited : ∀ {world output bytes reply world'}, write world output bytes reply world' →
    exited world' = exited world
  exit_recorded : ∀ {world code world'}, exit world code world' →
    exited world' = some code
  exitTrap_exited : ∀ {world code message world'}, exitTrap world code message world' →
    exited world' = exited world

inductive Outcome (α : Type) where
  | returned (value : α)
  | exited (code : UInt64)
  | trapped (message : String)

def Outcome.exitMarker (outcome : Outcome α) (initial : Option UInt64) : Option UInt64 :=
  match outcome with
  | .exited code => some code
  | .returned _ | .trapped _ => initial

def readResult (errno : UInt64) (committed : Bytes) : ReadResult :=
  ⟨errno, if errno = 0 then committed else Bytes.empty⟩

def writeResult (errno committed : UInt64) : WriteResult :=
  ⟨errno, if errno = 0 then committed else 0⟩

mutual

inductive Exec {World : Type} (host : Host World) :
    {α : Type} → Action α → World → List Event → Outcome α → World → Prop where
  | pure (world : World) (value : α) :
      Exec host (.pure value) world [] (.returned value) world
  | read_reject {capacity : UInt64} {next : ReadResult → Action α} {world final trace outcome}
      (hCapacity : 2 ^ 32 ≤ capacity.toNat)
      (hNext : Exec host (next ⟨61, Bytes.empty⟩) world trace outcome final) :
      Exec host (.read capacity next) world trace outcome final
  | read_return {capacity : UInt64} {next : ReadResult → Action α}
      {world after final trace outcome errno committed}
      (hCapacity : capacity.toNat < 2 ^ 32)
      (hHost : host.read world capacity (.returned errno committed) after)
      (hNext : Exec host (next (readResult errno committed)) after trace outcome final) :
      Exec host (.read capacity next) world
        (.read capacity (.returned errno committed) :: trace) outcome final
  | read_trap {capacity : UInt64} {next : ReadResult → Action α}
      {world after message committed}
      (hCapacity : capacity.toNat < 2 ^ 32)
      (hHost : host.read world capacity (.trapped message committed) after) :
      Exec host (.read capacity next) world
        [.read capacity (.trapped message committed)] (.trapped message) after
  | write_return {output : Output} {bytes : Bytes} {next : WriteResult → Action α}
      {world after final trace outcome errno committed}
      (hHost : host.write world output bytes (.returned errno committed) after)
      (hNext : Exec host (next (writeResult errno committed)) after trace outcome final) :
      Exec host (.write output bytes next) world
        (.write output bytes (.returned errno committed) :: trace) outcome final
  | write_trap {output : Output} {bytes : Bytes} {next : WriteResult → Action α}
      {world after message committed}
      (hHost : host.write world output bytes (.trapped message committed) after) :
      Exec host (.write output bytes next) world
        [.write output bytes (.trapped message committed)] (.trapped message) after
  | exit {code : UInt64} {world final}
      (hHost : host.exit world (exitStatus code) final) :
      Exec host (Action.exit (α := α) code) world [.exit (exitStatus code)]
        (.exited (exitStatus code)) final
  | exitTrap {code : UInt64} {world final message}
      (hHost : host.exitTrap world (exitStatus code) message final) :
      Exec host (Action.exit (α := α) code) world [.exitTrap (exitStatus code) message]
        (.trapped message) final
  | loop {count : UInt64} {init : σ} {test : UInt64 → σ → Bool}
      {step : UInt64 → σ → Action σ} {next : σ → Action α} {world final trace outcome}
      (hLoop : LoopExec host count.toNat 0 init test step next world trace outcome final) :
      Exec host (.loop count init test step next) world trace outcome final

inductive LoopExec {World : Type} (host : Host World) :
    {α σ : Type} → Nat → Nat → σ → (UInt64 → σ → Bool) →
      (UInt64 → σ → Action σ) → (σ → Action α) →
      World → List Event → Outcome α → World → Prop where
  | zero {index : Nat} {state : σ} {test step} {next : σ → Action α}
      {world final trace outcome}
      (hNext : Exec host (next state) world trace outcome final) :
      LoopExec host 0 index state test step next world trace outcome final
  | stop {remaining index : Nat} {state : σ} {test step} {next : σ → Action α}
      {world final trace outcome}
      (hTest : test (UInt64.ofNat index) state = false)
      (hNext : Exec host (next state) world trace outcome final) :
      LoopExec host (remaining + 1) index state test step next world trace outcome final
  | next {remaining index : Nat} {state state' : σ} {test step} {next : σ → Action α}
      {world after final first rest outcome}
      (hTest : test (UInt64.ofNat index) state = true)
      (hStep : Exec host (step (UInt64.ofNat index) state) world first (.returned state') after)
      (hRest : LoopExec host remaining (index + 1) state' test step next
        after rest outcome final) :
      LoopExec host (remaining + 1) index state test step next world (first ++ rest) outcome final
  | exit {remaining index : Nat} {state : σ} {test step} {next : σ → Action α}
      {world final trace code}
      (hTest : test (UInt64.ofNat index) state = true)
      (hStep : Exec host (step (UInt64.ofNat index) state) world trace (.exited code) final) :
      LoopExec host (remaining + 1) index state test step next world trace (.exited code) final
  | trap {remaining index : Nat} {state : σ} {test step} {next : σ → Action α}
      {world final trace message}
      (hTest : test (UInt64.ofNat index) state = true)
      (hStep : Exec host (step (UInt64.ofNat index) state) world trace (.trapped message) final) :
      LoopExec host (remaining + 1) index state test step next world trace (.trapped message) final

end

def Continue {World : Type} (host : Host World) (next : α → Action β) (world : World) :
    Outcome α → List Event → Outcome β → World → Prop
  | .returned value, trace, outcome, final => Exec host (next value) world trace outcome final
  | .exited code, trace, outcome, final =>
      trace = [] ∧ outcome = .exited code ∧ final = world
  | .trapped message, trace, outcome, final =>
      trace = [] ∧ outcome = .trapped message ∧ final = world

theorem Exec.bind {World : Type} {host : Host World} {action : Action α}
    {world after first outcome} (hRun : Exec host action world first outcome after) :
    ∀ {β : Type} {rest : List Event} {result : Outcome β} {final : World}
      {next : α → Action β}, Continue host next after outcome rest result final →
      Exec host (Action.bind action next) world (first ++ rest) result final := by
  refine Exec.rec
    (motive_1 := fun {α} action world first outcome after _ =>
      ∀ {β : Type} {rest : List Event} {result : Outcome β} {final : World}
        {next : α → Action β}, Continue host next after outcome rest result final →
        Exec host (Action.bind action next) world (first ++ rest) result final)
    (motive_2 := fun {α σ} remaining index (state : σ) test step continuation
      world first outcome after _ =>
      ∀ {β : Type} {rest : List Event} {result : Outcome β} {final : World}
        {next : α → Action β}, Continue host next after outcome rest result final →
        LoopExec host remaining index state test step
          (fun value => Action.bind (continuation value) next)
          world (first ++ rest) result final)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hRun
  · intro α world value β rest result final next hNext
    exact hNext
  · intro α capacity continuation world after trace outcome hCapacity _ ih
    intro β rest result final next hNext
    exact .read_reject hCapacity (ih hNext)
  · intro α capacity continuation world after final trace outcome errno committed
      hCapacity hHost _ ih
    intro β rest result final next hNext
    exact .read_return hCapacity hHost (ih hNext)
  · intro α capacity continuation world after message committed hCapacity hHost
    intro β rest result final next hNext
    rcases hNext with ⟨rfl, rfl, rfl⟩
    exact .read_trap hCapacity hHost
  · intro α output bytes continuation world after final trace outcome errno committed hHost _ ih
    intro β rest result final next hNext
    exact .write_return hHost (ih hNext)
  · intro α output bytes continuation world after message committed hHost
    intro β rest result final next hNext
    rcases hNext with ⟨rfl, rfl, rfl⟩
    exact .write_trap hHost
  · intro α code world after hHost β rest result final next hNext
    rcases hNext with ⟨rfl, rfl, rfl⟩
    exact .exit hHost
  · intro α code world after message hHost β rest result final next hNext
    rcases hNext with ⟨rfl, rfl, rfl⟩
    exact .exitTrap hHost
  · intro σ α count init test step continuation world after trace outcome _ ih
    intro β rest result final next hNext
    exact .loop (ih hNext)
  · intro σ α index state test step continuation world after trace outcome _ ih
    intro β rest result final next hNext
    exact .zero (ih hNext)
  · intro σ α remaining index state test step continuation world after trace outcome hTest _ ih
    intro β rest result final next hNext
    exact .stop hTest (ih hNext)
  · intro σ α remaining index state state' test step continuation world after final first trace
      outcome hTest hStep _ _ ih
    intro β rest result final next hNext
    rw [List.append_assoc]
    exact .next hTest hStep (ih hNext)
  · intro σ α remaining index state test step continuation world after trace code hTest hStep _
    intro β rest result final next hNext
    rcases hNext with ⟨rfl, rfl, rfl⟩
    simp only [List.append_nil]
    exact .exit hTest hStep
  · intro σ α remaining index state test step continuation world after trace message hTest hStep _
    intro β rest result final next hNext
    rcases hNext with ⟨rfl, rfl, rfl⟩
    simp only [List.append_nil]
    exact .trap hTest hStep

theorem Exec.exited_marker {World : Type} {host : Host World} {action : Action α}
    {world final trace outcome} (h : Exec host action world trace outcome final) :
    host.exited final = outcome.exitMarker (host.exited world) := by
  refine Exec.rec
    (motive_1 := fun {α} action world trace outcome final _ =>
      host.exited final = outcome.exitMarker (host.exited world))
    (motive_2 := fun {α σ} remaining index (state : σ) test step next
      world trace outcome final _ =>
      host.exited final = outcome.exitMarker (host.exited world))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro α world value; rfl
  · intro α capacity next world final trace outcome hCapacity hNext ih
    exact ih
  · intro α capacity next world after final trace outcome errno committed hCapacity hHost hNext ih
    rw [host.read_exited hHost] at ih
    exact ih
  · intro α capacity next world after message committed hCapacity hHost
    exact host.read_exited hHost
  · intro α output bytes next world after final trace outcome errno committed hHost hNext ih
    rw [host.write_exited hHost] at ih
    exact ih
  · intro α output bytes next world after message committed hHost
    exact host.write_exited hHost
  · intro α code world final hHost
    exact host.exit_recorded hHost
  · intro α code world final message hHost
    exact host.exitTrap_exited hHost
  · intro σ α count init test step next world final trace outcome hLoop ih
    exact ih
  · intro σ α index state test step next world final trace outcome hNext ih
    exact ih
  · intro σ α remaining index state test step next world final trace outcome hTest hNext ih
    exact ih
  · intro σ α remaining index state state' test step next world after final first rest outcome
      hTest hStep hRest ihStep ihRest
    dsimp only [Outcome.exitMarker] at ihStep
    rw [ihStep] at ihRest
    exact ihRest
  · intro σ α remaining index state test step next world final trace code hTest hStep ih
    exact ih
  · intro σ α remaining index state test step next world final trace message hTest hStep ih
    exact ih

theorem readSome_overflow {World : Type} (host : Host World) (world : World) (capacity : UInt64)
    (h : 2 ^ 32 ≤ capacity.toNat) :
    Exec host (readSome capacity) world [] (.returned ⟨61, Bytes.empty⟩) world :=
  .read_reject h (.pure world _)

theorem loop_zero {World : Type} (host : Host World) (world : World) (init : σ)
    (test : UInt64 → σ → Bool) (step : UInt64 → σ → Action σ) :
    Exec host (loop 0 init test step) world [] (.returned init) world :=
  .loop (.zero (.pure world init))

theorem Host.read_zero {World : Type} {host : Host World} {world final : World}
    {reply : Transfer Bytes} (h : host.read world 0 reply final) :
    reply.committed.data = ByteArray.empty := by
  apply ByteArray.size_eq_zero_iff.mp
  have := (host.read_bound h).1
  simp only [UInt64.toNat_zero] at this
  omega

end LeanExe.Wasi
