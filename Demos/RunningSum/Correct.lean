import Demos.RunningSum.StreamCorrect
import Demos.RunningSum.TerminationTarget

namespace Demos.RunningSum

open Wasm Verified Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep stdoutWords)

/-- Charges for a run: `beginCharge` bounds the allocation of `begin`, `charge` bounds that of
the step from each reached running state, and the heap has room for each charge with the copies
of the state before and after it.  The process compacts the state after `begin` and after each
step, so the heap holds the literal pool and one state between steps.  A later theorem derives
these charges from limits on line length and total size. -/
structure RunCharges {World : Type} (host : Host World) (initial : Store (Observed World))
    (heap : Heap) (rep : StreamPosition → World → Prop) where
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
    native.running = true →
    heap.top.toNat + stateTy.copyCost (sourceState native.state) + charge native position ≤
        65536 * (PureTransport.erase initial).memoryCap io.pure.module 0 ∧
      Resource.CallPrefixBound (observedHost host)
        (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program entry.step 0
        (.cons (sourceState native.state) .nil) world (charge native position)
  stepRoom : ∀ (native : ProcessStep State) position (world : Observed World),
    Termination.Safe native.state → observedStreamRep rep position world →
    native.running = true → ∀ trace next final nextPosition,
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
    (charges : RunCharges host initial heap rep) (accepted : ExitAccepted host rep) :
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
    streams.observed.progress observed valid at_ free static cap charges.charge charges.beginCharge
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

/-- For every input within the size bounds, the compiled command exits with status 0 when every
line is a decimal integer and with status 28 at the first line that is not, after writing the
cumulative totals of the lines before it. -/
theorem initial_terminates_integer {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (bounds : InputBounds position.input)
    (valid : targetHost.Satisfies module (hostSpec host))
    (charges : RunCharges host (initialStore world) (initialStaticHeap io.literalPool) rep)
    (accepted : ExitAccepted host rep) :
    ∃ values status, InputValues position.input values status ∧
      ∃ bound, ∀ fuel ≥ bound, ∃ final,
        run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
          stdoutWords final.host.events = cumulativeOutput values ∧
          host.exited final.host.world = some status :=
  terminates_integer host targetHost (initialStore world) (initialStaticHeap io.literalPool)
    rep streams represented events empty bounds valid
    (initialState world).1 rfl (initialState world).2.2 (initialState world).2.1 charges accepted

theorem integer_bytes : ∃ bytes,
    Encoding.encode module = .ok bytes ∧ Encoding.decode bytes = .ok module ∧
      Encoding.ValidBinary bytes ∧ (type_of% @initial_terminates_integer) := by
  obtain ⟨bytes, encoded, decoded, valid, _⟩ := command.bytes
  exact ⟨bytes, encoded, decoded, valid, @initial_terminates_integer⟩

end Demos.RunningSum
