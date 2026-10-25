import Demos.RunningSumFp.StreamCorrect
import Demos.RunningSumFp.TerminationTarget

namespace Demos.RunningSumFp

open Wasm Verified Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime
open Library.Numerics.Decimal.Shared.StrconvGrammar
open Demos.RunningSum (StreamPosition StreamHost observedStreamRep stdoutWords)

structure RunResources {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) : Prop where
  beginCall : ∃ budget, heap.Within (PureTransport.erase initial) io.pure.module budget ∧
    Resource.CallPrefixBound (observedHost host)
      (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program entry.begin 0 .nil
      initial.host budget
  stepCall : ∀ (native : ProcessStep State) position (store : Store (Observed World))
    locals heap words,
    ProcessReachable io.pure.module module entry initial
      ((entry.function io.pure.module (effectTypeIndex io.pure.module 4)).toLocals [])
      targetHost store locals →
    Termination.Safe native.state → observedStreamRep rep position store.host →
    native.running = true →
    ProcessMemory stateTy io.literalPool heap (PureTransport.erase store) words
      (sourceState native.state) →
    LocalsHold locals 2 stateTy.types words →
    ∃ budget, heap.Within (PureTransport.erase store) io.pure.module budget ∧
      Resource.CallPrefixBound (observedHost host)
        (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program entry.step 0
        (.cons (sourceState native.state) .nil) store.host budget

def ExitAccepted {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) : Prop :=
  ∀ position world, observedStreamRep rep position world → ∀ status,
    status = 0 ∨ status = 28 → ∀ message final,
    (observedHost host).exitTrap world (exitStatus status) message final → False

theorem result_fp {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : Observed World}
    (represented : rep position world.world) (events : world.events = [])
    (empty : position.output = []) (numbers : List Num)
    (inputValid : ValidInput position.input numbers) (accepted : ExitAccepted host rep)
    {final : Store (Observed World)} {message : String}
    (total : Termination.TargetTerminated host (.Trap final message))
    (native : ProcessEntryRunResult (observedHost host) begin process world (.Trap final message)) :
    stdoutWords final.host.events = cumulativeOutput numbers ∧ host.exited final.host.world = some 0 := by
  change ProcessEntryResult (observedHost host) begin process world (.Trap final message) at native
  cases native with
  | terminal final trace outcome message execution terminal =>
      obtain ⟨output, before, nextPosition, nextRep, _, finished⟩ :=
        command_fp streams represented events empty numbers inputValid execution
      rcases finished with ⟨returned, operation⟩ | ⟨error, trapped, operation⟩
      · exact ⟨output, host.exit_recorded operation.1⟩
      · exact False.elim (accepted nextPosition before nextRep 0 (Or.inl rfl) error _ operation)
  | resource final trace residual progress =>
      have impossible : ("unreachable" : String) = exitTrap := total.1
      exact False.elim ((by decide : ("unreachable" : String) ≠ exitTrap) impossible)

theorem terminates_fp {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (numbers : List Num) (inputValid : ValidInput position.input numbers)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial))
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (resources : RunResources host targetHost initial heap rep) (accepted : ExitAccepted host rep) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex initial [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = cumulativeOutput numbers ∧
        host.exited final.host.world = some 0 := by
  have observed : observedStreamRep rep position initial.host :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  obtain ⟨bound, executions⟩ := Termination.target_terminates host targetHost initial heap
    (observedStreamRep rep) (fun position => position.input.length) StreamPosition.zeroWrites
    streams.observed.progress observed valid at_ static cap resources.beginCall resources.stepCall accepted
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨total, native⟩ := executions fuel enough
  generalize executed : run fuel module startIndex initial [] targetHost = result at total native ⊢
  cases result with
  | Trap final message =>
      have messageEq := total.1
      have mathematical := result_fp streams represented events empty numbers inputValid
        accepted total native
      exact ⟨final, by simp [messageEq], mathematical⟩
  | _ => exact total.elim

theorem initial_terminates_fp {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (numbers : List Num) (inputValid : ValidInput position.input numbers)
    (valid : targetHost.Satisfies module (hostSpec host))
    (resources : RunResources host targetHost (initialStore world)
      (initialStaticHeap io.literalPool) rep) (accepted : ExitAccepted host rep) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = cumulativeOutput numbers ∧
        host.exited final.host.world = some 0 :=
  terminates_fp host targetHost (initialStore world) (initialStaticHeap io.literalPool)
    rep streams represented events empty numbers inputValid valid
    (initialState world).1 (initialState world).2.2 (initialState world).2.1 resources accepted

theorem fp_bytes : ∃ bytes,
    Encoding.encode module = .ok bytes ∧ Encoding.decode bytes = .ok module ∧
      Encoding.ValidBinary bytes ∧ (type_of% @initial_terminates_fp) := by
  obtain ⟨bytes, encoded, decoded, valid, _⟩ := command.bytes
  exact ⟨bytes, encoded, decoded, valid, @initial_terminates_fp⟩

end Demos.RunningSumFp
