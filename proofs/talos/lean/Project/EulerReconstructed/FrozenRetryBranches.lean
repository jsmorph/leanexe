import Project.EulerReconstructed.FrozenRetryTrial

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm Project.Runtime
open Project.EulerRiemann.Frozen
open Project.EulerRiemann.Frozen.Execution (boolWord Heap)

def retryAcceptBody : Wasm.Program :=
  match (retryStepBody[37]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def retryRejectBody : Wasm.Program :=
  match (retryStepBody[37]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

theorem retry_trial_branches_shape : retryStepBody = retryStepBody.take 30 ++
    [.localGet 35, .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
      .constI64 0, .eqI64, .eqz, .iff 0 0 retryAcceptBody retryRejectBody] := rfl

def retryAcceptedFrame (frame : Locals) (dt root : UInt64) : Locals :=
  let locals := frame.locals.set 1 (.i64 0)
  let locals := locals.set 2 (.i64 dt)
  let locals := locals.set 3 (.i64 root)
  let locals := locals.set 4 (.i64 root)
  let locals := locals.set 5 (.i64 1)
  { frame with locals, values := [] }

def retryRejectedFrame (frame : Locals) (fuel : UInt64) (n : Nat)
    (trials time dt alpha source frees : UInt64) : Locals :=
  let half := IEEE64.mul 0x3FE0000000000000 dt
  let locals := frame.locals.set 28 (.i64 frees)
  let locals := locals.set 29 (.i64 (UInt64.ofNat n))
  let locals := locals.set 30 (.i64 trials)
  let locals := locals.set 31 (.i64 time)
  let locals := locals.set 32 (.i64 half)
  let locals := locals.set 33 (.i64 alpha)
  let locals := locals.set 34 (.i64 source)
  let locals := locals.set 35 (.i64 source)
  let locals := locals.set 36 (.i64 (UInt64.ofNat n))
  let locals := locals.set 37 (.i64 trials)
  let locals := locals.set 38 (.i64 time)
  let locals := locals.set 39 (.i64 half)
  let locals := locals.set 40 (.i64 alpha)
  let locals := locals.set 41 (.i64 source)
  let locals := locals.set 42 (.i64 source)
  let locals := locals.set 43 (.i64 0)
  let locals := locals.set 0 (.i64 0)
  { params := [.i64 (fuel - 1), .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
      .i64 half, .i64 alpha, .i64 source, .i64 source]
    locals
    values := [] }

theorem RetryFrameAt.accept {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done)
    (result : UInt64) :
    RetryFrameAt (retryAcceptedFrame frame dt result) fuel n trials time dt alpha source dt result true := by
  cases h
  constructor <;> simp_all [retryAcceptedFrame, boolWord]

theorem RetryFrameAt.reject {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done) (frees : UInt64) :
    RetryFrameAt (retryRejectedFrame frame fuel n trials time dt alpha source frees)
      (fuel - 1) n trials time (IEEE64.mul 0x3FE0000000000000 dt) alpha source
        outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryRejectedFrame]

theorem RetryScratch.reject {frame : Locals} (h : RetryScratch frame)
    (fuel : UInt64) (n : Nat) (trials time dt alpha source frees : UInt64) :
    RetryScratch (retryRejectedFrame frame fuel n trials time dt alpha source frees) := by
  unfold RetryScratch retryRejectedFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem retry_accept_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n : Nat) (fuel trials time dt alpha source ratio result : UInt64)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
      .i64 dt, .i64 alpha, .i64 source, .i64 source])
    (hLocals : frame.locals.length = 77) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q store
      (retryAcceptedFrame (retryTrialFrame frame n trials ratio source result true) dt result) env) :
    wp Project.EulerReconstructed.Frozen.«module» (retryAcceptBody ++ rest) Q store
      (retryTrialFrame frame n trials ratio source result true) env := by
  unfold retryAcceptBody retryStepBody retryTrial retryLoop func125
  dsimp only
  wp_run [retryTrialFrame, List.cons_append, List.nil_append, List.length_set,
    List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, hParams, hLocals]
  simpa [retryAcceptedFrame, retryTrialFrame, hParams] using hNext

theorem retry_reject_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (n : Nat) (fuel trials time dt alpha source ratio : UInt64)
    (result : FreeNode) (grid : Array Project.EulerRiemann.Frozen.Traversal.Cell)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
      .i64 dt, .i64 alpha, .i64 source, .i64 source])
    (hLocals : frame.locals.length = 77) (hTracker : frame.locals[0]? = some (.i64 0))
    (hSource : source ≠ 0) (hHeap : heap.At store) (hOwner : heap.Owns store result grid)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q (heap.releaseStore store result)
      (retryRejectedFrame (retryTrialFrame frame n trials ratio source result.root false)
        fuel n trials time dt alpha source (heap.frees + 1)) env) :
    wp Project.EulerReconstructed.Frozen.«module» (retryRejectBody ++ rest) Q store
      (retryTrialFrame frame n trials ratio source result.root false) env := by
  obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
  unfold retryRejectBody retryStepBody retryTrial retryLoop func125
  dsimp only
  wp_run [retryTrialFrame, List.cons_append, List.nil_append, List.length_set,
    List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    Nat.reduceEqDiff, hParams, hLocals]
  refine wp_call_tw (release_owned env store heap result grid hHeap hOwner) ?_
  rintro final values ⟨rfl, hFinal, hFinalHeap⟩
  subst final
  have hFrees : (heap.releaseStore store result).globals.globals[5]? =
      some (.i64 (heap.frees + 1)) := by rw [hFinalHeap.globals]; rfl
  repeat
    first
    | wp_run [retryTrialFrame, List.cons_append, List.nil_append, List.length_set,
        List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ, f64Mul,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le]
  simpa [retryRejectedFrame, retryTrialFrame, hParams, List.set] using hNext

#print axioms retry_trial_branches_shape
#print axioms RetryFrameAt.accept
#print axioms RetryFrameAt.reject
#print axioms RetryScratch.reject
#print axioms retry_accept_spec
#print axioms retry_reject_spec
end Project.EulerReconstructed.Frozen.Execution
