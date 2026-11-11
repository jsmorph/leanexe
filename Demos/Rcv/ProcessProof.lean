import Demos.Rcv.ProcessModule
import Demos.Rcv.ProcessRun

/-! The refinement of [the process](Process.lean) by its compiled module.  `step_related` and
`begin_related` relate the reflected `step` and `begin` to the native ones on the state's tuple,
and `compiledProcess` bundles them with the compiled program as the `Compiled` of
[the runs of a compiled tabulator's process](ProcessRun.lean).  `implements` states that every
modeled run of the module that completes without exhausting Talos fuel matches the native process,
including runs that stop at an I/O error, a host trap, or a rejected exit, and `run_initial` states
the same from the module's initial store.  `bytes` combines `implements` with the encoding, exact
decoding, and binary validity of the module. -/

namespace Demos.Rcv.Process

open Wasm Verified Verified.Wasi LeanExe.Wasi

def sourceProcess : Process stateTy.denote :=
  ⟨sourceState initial, entry.action (io.program.funs io.pure.funs)⟩

def startIndex : Nat := entry.startIndex io.pure.module

theorem compactClosed :
    Relocation.programClosed io.pure.module.funcs.length (processCompaction stateTy) = true := by
  decide +kernel

theorem step_related : Process.Rel (fun native flat => flat = sourceState native)
    process sourceProcess := by
  intro s flat same
  subst flat
  have reflected : Action.Rel (fun native flat => flat = sourceResult native) (step s)
      ((io.program.funs io.pure.funs).get entry.step (.cons (sourceState s) .nil)) :=
    io.step.related s
  exact relatedResult reflected

theorem begin_related : Action.Rel (ProcessStep.Rel (fun native flat => flat = sourceState native))
    begin (entry.beginAction (io.program.funs io.pure.funs)) := by
  have reflected : Action.Rel (fun native flat => flat = sourceResult native) begin
      ((io.program.funs io.pure.funs).get entry.begin .nil) := io.begin.related
  exact relatedResult reflected

/-- The compiled process with the facts that `Compiled` bundles. -/
def compiledProcess : Compiled begin where
  pureSigs := _
  effectSigs := _
  source := io.pure.module
  pure := Resource.PureContext.ofProg io.pure.program io.pure.funs
  program := io.program
  beginVar := io.begin.callee
  stepVar := io.step.callee
  pool := io.literalPool
  calls := calls
  runtime := compileWith_runtime io.pure.program io.pure.tables io.pure.wrappers io.literalPool
  profile := io.profile
  compactClosed := compactClosed
  poolScratch := io.pool_apart
  beginRelated := begin_related
  stepRelated := step_related

def initialStore {World : Type} (world : Observed World) : Store (Observed World) :=
  PureTransport.restore world (module.initialStore : Store Unit)

theorem initialState {World : Type} (world : Observed World) :
    let store := PureTransport.erase (initialStore world)
    (initialStaticHeap io.literalPool).At store ∧ store.memoryCap module 0 ≤ 65535 ∧
      io.literalPool.Static (initialStaticHeap io.literalPool) store :=
  compileProcess_initialStore io.pure.program io.pure.tables io.pure.wrappers io.literalPool
    io.program entry world (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
/-- Every modeled run of the module from a store with an allocator at `heap`, the literal pool,
and a memory cap of at most 65,535 pages, under a host that satisfies `hostSpec host`, that
completes without exhausting its fuel, matches a run of the native process from `initial`. -/
theorem implements {World : Type} (host : Host World) (targetHost : HostEnv (Observed World))
    (initial : Store (Observed World)) (heap : LeanExe.Pipeline.Heap) (fuel : Nat)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (completed : run fuel module startIndex initial [] targetHost ≠ .OutOfFuel) :
    ProcessEntryRunResult (observedHost host) begin process initial.host
      (run fuel module startIndex initial [] targetHost) :=
  compiledProcess.implements host targetHost initial heap fuel valid at_ free static cap completed

theorem exported : ({ name := "_start", funcIdx := startIndex } : Export) ∈ module.exports :=
  compileProcess_export io.pure.module io.program entry io.literalPool

/-- `implements` from the module's initial store. -/
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

end Demos.Rcv.Process
