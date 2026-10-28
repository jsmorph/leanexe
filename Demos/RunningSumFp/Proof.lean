import Demos.RunningSumFp.Module
import Verified.Wasi.ProcessCorrect
import Verified.Wasi.ProcessNative

namespace Demos.RunningSumFp

open Wasm Verified Verified.Wasi LeanExe.Wasi

def sourceState (state : State) : stateTy.denote :=
  (state.total, state.line, state.input, state.cursor,
    state.output, state.written, state.eof)

def sourceProcess : Process stateTy.denote :=
  ⟨sourceState initial, entry.action (io.program.funs io.pure.funs)⟩

def startIndex : Nat := entry.startIndex io.pure.module

theorem compactable : stateTy.compactable = true := by decide

theorem compactForm : Encoding.ProgramForm (processCompaction stateTy) :=
  Encoding.checkProgramForm_sound (by decide +kernel)

theorem compactClosed :
    Relocation.programClosed io.pure.module.funcs.length (processCompaction stateTy) = true := by
  decide +kernel

private def sourceResult (value : ProcessStep State) : (processResultTy stateTy).denote :=
  processValue stateTy ⟨value.running, value.status, sourceState value.state⟩

private theorem relatedResult {native : Action (ProcessStep State)}
    {source : Action (processResultTy stateTy).denote}
    (reflected : Action.Rel (fun native flat => flat = sourceResult native) native source) :
    Action.Rel (ProcessStep.Rel (fun native flat => flat = sourceState native)) native
      (source.bind fun value => .pure (processNative stateTy value)) := by
  have related := reflected.bind
    (results := ProcessStep.Rel (fun native flat => flat = sourceState native))
    (leftNext := Action.pure) (rightNext := fun value => .pure (processNative stateTy value))
    (fun native flat same => by
      subst flat
      exact .pure (by simp only [sourceResult, processNative_value]; exact ⟨rfl, rfl, rfl⟩))
  simpa only [Action.bind_pure] using related

theorem step_related : Process.Rel (fun native flat => flat = sourceState native)
    process sourceProcess := by
  intro state flat same
  subst flat
  have reflected : Action.Rel (fun native flat => flat = sourceResult native) (step state)
      ((io.program.funs io.pure.funs).get entry.step (.cons (sourceState state) .nil)) :=
    io.step.related state
  exact relatedResult reflected

theorem begin_related : Action.Rel (ProcessStep.Rel (fun native flat => flat = sourceState native))
    begin (entry.beginAction (io.program.funs io.pure.funs)) := by
  have reflected : Action.Rel (fun native flat => flat = sourceResult native) begin
      ((io.program.funs io.pure.funs).get entry.begin .nil) := io.begin.related
  exact relatedResult reflected

def initialStore {World : Type} (world : Observed World) : Store (Observed World) :=
  PureTransport.restore world (module.initialStore : Store Unit)

theorem initialState {World : Type} (world : Observed World) :
    let store := PureTransport.erase (initialStore world)
    (initialStaticHeap io.literalPool).At store ∧ store.memoryCap module 0 ≤ 65535 ∧
      io.literalPool.Static (initialStaticHeap io.literalPool) store :=
  compileProcess_initialStore io.pure.program io.pure.tables io.pure.wrappers io.literalPool
    io.program entry world (by decide +kernel) (by decide +kernel)

theorem source_run {World : Type} (host : Host World) (targetHost : HostEnv (Observed World))
    (initial : Store (Observed World)) (heap : LeanExe.Pipeline.Heap) (fuel : Nat)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (completed : run fuel module startIndex initial [] targetHost ≠ .OutOfFuel) :
    ProcessEntryRunResult (observedHost host) (entry.beginAction (io.program.funs io.pure.funs))
      sourceProcess initial.host
      (run fuel module startIndex initial [] targetHost) :=
  compiled_process_run io.program entry io.literalPool calls
    (compileWith_runtime io.pure.program io.pure.tables io.pure.wrappers io.literalPool)
    io.profile compactable compactForm compactClosed (fun _ => rfl)
    valid at_ free static io.pool_apart cap completed

theorem implements {World : Type} (host : Host World) (targetHost : HostEnv (Observed World))
    (initial : Store (Observed World)) (heap : LeanExe.Pipeline.Heap) (fuel : Nat)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (completed : run fuel module startIndex initial [] targetHost ≠ .OutOfFuel) :
    ProcessEntryRunResult (observedHost host) begin process initial.host
      (run fuel module startIndex initial [] targetHost) :=
  (source_run host targetHost initial heap fuel valid at_ free static cap completed).transport_back
    step_related begin_related

theorem exported : ({ name := "_start", funcIdx := startIndex } : Export) ∈ module.exports :=
  compileProcess_export io.pure.module io.program entry io.literalPool

theorem run_initial {World : Type} (host : Host World) (targetHost : HostEnv (Observed World))
    (world : Observed World) (fuel : Nat)
    (valid : targetHost.Satisfies module (hostSpec host))
    (completed : run fuel module startIndex (initialStore world) [] targetHost ≠ .OutOfFuel) :
    ProcessEntryRunResult (observedHost host) begin process world
      (run fuel module startIndex (initialStore world) [] targetHost) :=
  implements host targetHost (initialStore world) (initialStaticHeap io.literalPool) fuel valid
    (initialState world).1 rfl (initialState world).2.2 (initialState world).2.1 completed

theorem bytes : ∃ bytes, Encoding.encode module = .ok bytes ∧ Encoding.decode bytes = .ok module ∧
    Encoding.ValidBinary bytes ∧ (type_of% @implements) := by
  obtain ⟨bytes, encoded, decoded, valid, _⟩ := command.bytes
  exact ⟨bytes, encoded, decoded, valid, @implements⟩

end Demos.RunningSumFp
