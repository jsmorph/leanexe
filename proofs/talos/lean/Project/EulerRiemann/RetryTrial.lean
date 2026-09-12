import Project.EulerRiemann.RetryLoopShape

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

macro "retry_trial_peel" : tactic => `(tactic|
  wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set, List.getElem?_cons_zero,
    List.getElem?_cons_succ, f64Div, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    Nat.reduceEqDiff, *])

theorem retry_trial_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (source : FreeNode) (grid : Array Traversal.Cell)
    (n : Nat) (time dt : UInt64) (spare limit : Nat)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
      .i64 dt, .i64 source.root, .i64 source.root])
    (hLocals : frame.locals.length = 51) (hValues : frame.values = [])
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerRiemann.«module» 0 * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let ratio := IEEE64.div dt (Time.spacing n)
      let need := normalizedCapacity (UInt64.ofNat grid.size) 7
      let result := stepAllocation heap need (Traversal.accepted (Traversal.sweep n false ratio grid))
      ∀ final, result.1.At final → result.1.Owns final result.2 (Traversal.step n ratio grid) →
        final.mem.pages ≤ 65536 →
        final.memoryCap Project.EulerRiemann.«module» 0 = initial.memoryCap Project.EulerRiemann.«module» 0 →
        result.1.Reserved need (spare + 1) limit → need ≤ result.2.capacity →
        (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          result.1.Owns final saved savedGrid ∧ regionsDisjoint saved.region result.2.region) →
        wp Project.EulerRiemann.«module» rest Q final
          (retryTrialFrame frame n ratio source.root result.2.root
            (Traversal.accepted (Traversal.step n ratio grid))) env) :
    wp Project.EulerRiemann.«module» (retryTrial.take 35 ++ rest) Q initial frame env := by
  unfold retryTrial retryLoop func74
  dsimp only
  retry_trial_peel
  refine wp_call_tw ((spacing_exact env initial n hn.2).append_args rfl rfl rfl [.f64 dt]) ?_
  rintro current values ⟨out, rfl, hCurrent, rfl⟩
  subst current
  retry_trial_peel
  refine wp_call_tw (step_reserved env initial heap source grid n
    (IEEE64.div dt (Time.spacing n)) spare limit hn hIndexed hHeap hOwner hPages
    hReserve hLimit hCap) ?_
  rintro final values ⟨rfl, hFinalHeap, hFinalOwner, hFinalPages, hFinalCap,
    hFinalReserve, hCapacity, hFrame⟩
  retry_trial_peel
  refine wp_call_tw (accepted_exact env final _ _ _ hFinalOwner.buffer.values) ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  retry_trial_peel
  simpa [retryTrialFrame, hParams, hValues] using hNext final hFinalHeap hFinalOwner
    hFinalPages hFinalCap hFinalReserve hCapacity hFrame

#print axioms retry_trial_spec

end Project.EulerRiemann.Execution
