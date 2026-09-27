import Project.EulerReconstructed.RetryCflReject
import Project.EulerReconstructed.StepReserve

namespace Project.EulerReconstructed.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity
open Project.EulerRiemann
open Project.EulerRiemann.Execution (boolWord Heap stepAllocation)

def retryTrialFrame (frame : Locals) (n : Nat) (trials ratio source result : UInt64)
    (accepted : Bool) : Locals :=
  let locals := frame.locals.set 16 (.i64 (UInt64.ofNat n))
  let locals := locals.set 17 (.i64 trials)
  let locals := locals.set 18 (.i64 ratio)
  let locals := locals.set 19 (.i64 source)
  let locals := locals.set 20 (.i64 source)
  let locals := locals.set 22 (.i64 result)
  let locals := locals.set 21 (.i64 result)
  let locals := locals.set 23 (.i64 result)
  let locals := locals.set 24 (.i64 result)
  let locals := locals.set 25 (.i64 result)
  let locals := locals.set 26 (.i64 result)
  let locals := locals.set 27 (.i64 (boolWord accepted))
  { frame with locals, values := [] }

theorem RetryFrameAt.trial {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done)
    (ratio result : UInt64) (accepted : Bool) :
    RetryFrameAt (retryTrialFrame frame n trials ratio source result accepted)
      fuel n trials time dt alpha source outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryTrialFrame]

theorem RetryScratch.trial {frame : Locals} (h : RetryScratch frame)
    (n : Nat) (trials ratio source result : UInt64) (accepted : Bool) :
    RetryScratch (retryTrialFrame frame n trials ratio source result accepted) := by
  unfold RetryScratch retryTrialFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem retry_trial_pages_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell)
    (n : Nat) (trials time dt alpha ratio : UInt64) (spare limit pageLimit : Nat)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
      .i64 dt, .i64 alpha, .i64 source.root, .i64 source.root])
    (hLocals : frame.locals.length = 77) (hValues : frame.values = [])
    (hRatio : frame.locals[15]? = some (.i64 ratio))
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerReconstructed.«module» 0 * 65536)
    (hLimitPages : limit ≤ pageLimit * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let need := normalizedCapacity (UInt64.ofNat grid.size) 7
      let result := stepAllocation heap need
        (Project.EulerRiemann.Traversal.accepted (Traversal.sweep n trials.toNat false ratio grid))
      ∀ final, result.1.At final → result.1.Owns final result.2 (Traversal.step n trials.toNat ratio grid) →
        final.mem.pages ≤ pageLimit →
        final.memoryCap Project.EulerReconstructed.«module» 0 =
          initial.memoryCap Project.EulerReconstructed.«module» 0 →
        result.1.Reserved need (spare + 1) limit → need ≤ result.2.capacity →
        (∀ (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Traversal.Cell),
          heap.Owns initial saved savedGrid →
          result.1.Owns final saved savedGrid ∧ regionsDisjoint saved.region result.2.region) →
        wp Project.EulerReconstructed.«module» rest Q final
          (retryTrialFrame frame n trials ratio source.root result.2.root
            (Project.EulerRiemann.Traversal.accepted (Traversal.step n trials.toNat ratio grid))) env) :
    wp Project.EulerReconstructed.«module» (retryStepBody.take 30 ++ rest) Q initial frame env := by
  unfold retryStepBody retryTrial retryLoop func125
  dsimp only
  reconstructed_retry_guard_peel
  refine wp_call_tw (step_pages_reserved env initial heap source grid n trials ratio
    spare limit pageLimit hn hIndexed hHeap hOwner hPages hPageLimit
    hReserve hLimit hCap hLimitPages) ?_
  rintro final values ⟨rfl, hFinalHeap, hFinalOwner, hFinalPages, hFinalCap,
    hFinalReserve, hCapacity, hFrame⟩
  reconstructed_retry_guard_peel
  refine wp_call_tw (accepted_exact env final _ _ _ hFinalOwner.buffer.values) ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  reconstructed_retry_guard_peel
  simpa [retryTrialFrame, boolWord, hParams, hValues] using hNext final hFinalHeap hFinalOwner
    hFinalPages hFinalCap hFinalReserve hCapacity hFrame

#print axioms RetryFrameAt.trial
#print axioms RetryScratch.trial
#print axioms retry_trial_pages_spec
end Project.EulerReconstructed.Execution
