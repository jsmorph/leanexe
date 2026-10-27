import Demos.RunningSum.Charges
import Demos.RunningSum.StreamCorrect
import Demos.RunningSum.TerminationTarget

namespace Demos.RunningSum

open Wasm Verified Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep stdoutWords)

/-- Charges for a run: `beginCharge` bounds the allocation of `begin`, `charge` bounds that of
the step from each reached running state where `Inv` holds, and the heap has room for each charge
with the copies of the state before and after it.  The process compacts the state after `begin`
and after each step, so the heap holds the literal pool and one state between steps. -/
structure RunCharges {World : Type} (host : Host World) (initial : Store (Observed World))
    (heap : Heap) (rep : StreamPosition → World → Prop) (Inv : State → StreamPosition → Prop) where
  charge : ProcessStep State → StreamPosition → Nat
  beginCharge : Nat
  beginRoom : heap.top.toNat + beginCharge +
      stateTy.copyCost (sourceState Demos.RunningSum.initial) ≤
    65536 * (PureTransport.erase initial).memoryCap io.pure.module 0
  beginBounded : Resource.CallPrefixBound (observedHost host)
    (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program entry.begin 0 .nil
    initial.host beginCharge
  stepBounded : ∀ (native : ProcessStep State) position (world : Observed World),
    Termination.Safe native.state → observedStreamRep rep position world →
    native.running = true → Inv native.state position →
    heap.top.toNat + stateTy.copyCost (sourceState native.state) + charge native position ≤
        65536 * (PureTransport.erase initial).memoryCap io.pure.module 0 ∧
      Resource.CallPrefixBound (observedHost host)
        (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program entry.step 0
        (.cons (sourceState native.state) .nil) world (charge native position)
  stepRoom : ∀ (native : ProcessStep State) position (world : Observed World),
    Termination.Safe native.state → observedStreamRep rep position world →
    native.running = true → Inv native.state position → ∀ trace next final nextPosition,
    LeanExe.Wasi.Exec (observedHost host) (step native.state) world trace (.returned next) final →
    observedStreamRep rep nextPosition final →
    heap.top.toNat + stateTy.copyCost (sourceState native.state) + charge native position +
        stateTy.copyCost (sourceState next.state) ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0

def ExitAccepted {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) : Prop :=
  ∀ position world, observedStreamRep rep position world → ∀ status,
    status = 0 ∨ status = 28 → ∀ message final,
    (observedHost host).exitTrap world (exitStatus status) message final → False

theorem result_integer {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : Observed World}
    (represented : rep position world.world) (events : world.events = [])
    (empty : position.output = []) (bounds : InputBounds position.input) {values : List Int}
    {status : UInt64} (lineValues : InputValues position.input values status)
    (accepted : ExitAccepted host rep) {final : Store (Observed World)} {message : String}
    (total : Termination.TargetTerminated host (.Trap final message))
    (native : ProcessEntryRunResult (observedHost host) begin process world (.Trap final message)) :
    stdoutWords final.host.events = cumulativeOutput values ∧
      host.exited final.host.world = some status := by
  change ProcessEntryResult (observedHost host) begin process world (.Trap final message) at native
  cases native with
  | terminal final trace outcome message execution terminal =>
      obtain ⟨output, before, nextPosition, nextRep, _, finished⟩ :=
        command_integer streams represented events empty bounds lineValues execution
      rcases finished with ⟨returned, operation⟩ | ⟨error, trapped, operation⟩
      · exact ⟨output, host.exit_recorded operation.1⟩
      · rw [← lineValues.exitStatus] at operation
        exact False.elim (accepted nextPosition before nextRep status
          (StreamFold.Model.LineValues.status lineValues) error _ operation)
  | resource final trace residual progress =>
      have impossible : ("unreachable" : String) = exitTrap := total.1
      exact False.elim ((by decide : ("unreachable" : String) ≠ exitTrap) impossible)

theorem terminates_integer {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (bounds : InputBounds position.input)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (Inv : State → StreamPosition → Prop) (initialInv : Inv Demos.RunningSum.initial position)
    (advances : Termination.StepAdvances (observedHost host) (observedStreamRep rep)
      (fun position => position.input.length) StreamPosition.zeroWrites Inv)
    (charges : RunCharges host initial heap rep Inv) (accepted : ExitAccepted host rep) :
    ∃ values status, InputValues position.input values status ∧
      ∃ bound, ∀ fuel ≥ bound, ∃ final,
        run fuel module startIndex initial [] targetHost = .Trap final exitTrap ∧
          stdoutWords final.host.events = cumulativeOutput values ∧
          host.exited final.host.world = some status := by
  have observed : observedStreamRep rep position initial.host :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  obtain ⟨values, status, lineValues⟩ := inputValues_exist bounds
  obtain ⟨bound, executions⟩ := Termination.target_terminates host targetHost initial heap
    (observedStreamRep rep) (fun position => position.input.length) StreamPosition.zeroWrites
    streams.observed.progress Inv advances observed initialInv valid at_ free static cap
    charges.charge charges.beginCharge
    charges.beginRoom charges.beginBounded charges.stepBounded charges.stepRoom accepted
  refine ⟨values, status, lineValues, bound, fun fuel enough => ?_⟩
  obtain ⟨total, native⟩ := executions fuel enough
  generalize executed : run fuel module startIndex initial [] targetHost = result at total native ⊢
  cases result with
  | Trap final message =>
      have messageEq := total.1
      have mathematical := result_integer streams represented events empty bounds lineValues
        accepted total native
      exact ⟨final, by simp [messageEq], mathematical⟩
  | _ => exact total.elim

/-- The bytes above the heap's initial top that a run within the limits `L` and `D` needs: room
for the copies of the state before and after a step and for the step's charge. -/
def limitMemory (L D : Nat) : Nat := 220 * (L + D) + 1010000

theorem limitMemory_room (L D : Nat) : 2 * copyLimit L D + stepCharge L D ≤ limitMemory L D := by
  unfold copyLimit stepCharge limitMemory
  omega

theorem limitMemory_small {L D top cap : Nat} (capBound : cap ≤ 65535)
    (room : top + limitMemory L D ≤ 65536 * cap) : L + D + 4100 < UInt64.size := by
  have size : UInt64.size = 18446744073709551616 := rfl
  unfold limitMemory at room
  omega

theorem memoryCap_pure {α : Type} (store : Store α) :
    store.memoryCap module 0 = store.memoryCap io.pure.module 0 :=
  PureTransport.memoryCap_zero_eq rfl store

/-- The charges of a run within the limits, when the memory above the heap's top holds
`limitMemory L D` bytes. -/
def limitCharges {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {initial : Store (Observed World)} {heap : Heap} {L D : Nat}
    (cap : (PureTransport.erase initial).memoryCap io.pure.module 0 ≤ 65535)
    (room : heap.top.toNat + limitMemory L D ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0) :
    RunCharges host initial heap rep (LimitInv L D) where
  charge := fun _ _ => stepCharge L D
  beginCharge := beginCharge
  beginRoom := by
    have copy : stateTy.copyCost (sourceState Demos.RunningSum.initial) ≤ copyLimit L D :=
      Sized.copyCost ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
    have begin := beginCharge_le
    have total := limitMemory_room L D
    unfold copyLimit at copy total
    omega
  beginBounded := begin_prefix_bound (observedHost host) initial.host
  stepBounded := fun native position world _ _ _ invariant => by
    have small := limitMemory_small cap room
    have sized := invariant.sized (by omega)
    refine ⟨?_, step_prefix_bound (observedHost host) small sized world⟩
    have copy := sized.copyCost
    have total := limitMemory_room L D
    omega
  stepRoom := fun native position world _ represented _ invariant _ next final _ execution _ => by
    have small := limitMemory_small cap room
    have copy := (invariant.sized (by omega)).copyCost
    have nextCopy := (step_sized streams (by omega) invariant represented execution).copyCost
    have total := limitMemory_room L D
    omega

/-- For every input within the size bounds and the limits `L` and `D`, when the memory above the
heap's top holds `limitMemory L D` bytes, the compiled command exits with status 0 when every line
is a decimal integer and with status 28 at the first line that is not, after writing the
cumulative totals of the lines before it. -/
theorem terminates_limits {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (bounds : InputBounds position.input) {L D : Nat} (limits : InputLimits L D position.input)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (room : heap.top.toNat + limitMemory L D ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0)
    (accepted : ExitAccepted host rep) :
    ∃ values status, InputValues position.input values status ∧
      ∃ bound, ∀ fuel ≥ bound, ∃ final,
        run fuel module startIndex initial [] targetHost = .Trap final exitTrap ∧
          stdoutWords final.host.events = cumulativeOutput values ∧
          host.exited final.host.world = some status :=
  terminates_integer host targetHost initial heap rep streams represented events empty bounds valid
    at_ free static cap (LimitInv L D) (limitInv_initial L D position empty bounds limits)
    (limit_advances streams L D)
    (limitCharges streams (by rw [← memoryCap_pure]; exact cap) room) accepted

theorem initial_memoryCap {World : Type} (world : Observed World) :
    (PureTransport.erase (initialStore world)).memoryCap io.pure.module 0 = 65535 := by
  show (module.initialStore : Store Unit).memoryCap io.pure.module 0 = 65535
  decide +kernel

theorem initial_top : (initialStaticHeap io.literalPool).top.toNat = 4104 := by
  decide +kernel

/-- For every input within the size bounds and the limits `L` and `D`, when `limitMemory L D`
bytes fit in the module's memory of 65,535 pages above the literal pool, which ends at 4,104
bytes, the compiled command exits with status 0 when every line is a decimal integer and with
status 28 at the first line that is not, after writing the cumulative totals of the lines before
it. -/
theorem initial_terminates_integer {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (bounds : InputBounds position.input) {L D : Nat} (limits : InputLimits L D position.input)
    (valid : targetHost.Satisfies module (hostSpec host))
    (room : 4104 + limitMemory L D ≤ 65536 * 65535) (accepted : ExitAccepted host rep) :
    ∃ values status, InputValues position.input values status ∧
      ∃ bound, ∀ fuel ≥ bound, ∃ final,
        run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
          stdoutWords final.host.events = cumulativeOutput values ∧
          host.exited final.host.world = some status :=
  terminates_limits host targetHost (initialStore world) (initialStaticHeap io.literalPool)
    rep streams represented events empty bounds limits valid
    (initialState world).1 rfl (initialState world).2.2 (initialState world).2.1
    (by rw [initial_top, initial_memoryCap]; exact room) accepted

/-- For every input within the size bounds whose lines up to the first line without an integer
have at most 9,000,000 bytes and whose totals have at most 9,000,000 digits, the compiled command
exits with status 0 when every line is a decimal integer and with status 28 at the first line that
is not, after writing the cumulative totals of the lines before it. -/
theorem initial_terminates_integer_9000000 {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (bounds : InputBounds position.input) (limits : InputLimits 9000000 9000000 position.input)
    (valid : targetHost.Satisfies module (hostSpec host)) (accepted : ExitAccepted host rep) :
    ∃ values status, InputValues position.input values status ∧
      ∃ bound, ∀ fuel ≥ bound, ∃ final,
        run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
          stdoutWords final.host.events = cumulativeOutput values ∧
          host.exited final.host.world = some status :=
  initial_terminates_integer host targetHost world rep streams represented events empty bounds
    limits valid (by unfold limitMemory; omega) accepted

theorem integer_bytes : ∃ bytes,
    Encoding.encode module = .ok bytes ∧ Encoding.decode bytes = .ok module ∧
      Encoding.ValidBinary bytes ∧ (type_of% @initial_terminates_integer) := by
  obtain ⟨bytes, encoded, decoded, valid, _⟩ := command.bytes
  exact ⟨bytes, encoded, decoded, valid, @initial_terminates_integer⟩

end Demos.RunningSum
