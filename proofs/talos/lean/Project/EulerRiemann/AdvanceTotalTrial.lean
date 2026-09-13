import Project.EulerRiemann.AdvanceTrial
import Project.EulerRiemann.ExecutionRetryTotal
import Project.EulerRiemann.ProposalFuel

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

theorem advance_total_trial_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (source : FreeNode) (grid : Array Traversal.Cell)
    (n : Nat) (time alpha : UInt64) (spare limit pageLimit : Nat)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
      .i64 source.root, .i64 source.root])
    (hLocals : frame.locals.length = 45) (hValues : frame.values = [])
    (hAlpha : frame.locals[12]? = some (.i64 alpha))
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hLimitPages : limit ≤ pageLimit * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let dt := Time.proposal n time alpha
      let trial := Control.retry (dt.toNat + 1) n time dt grid
      ∀ final finalHeap result,
        RetryStoreAt initial heap final finalHeap → final.mem.pages ≤ pageLimit → finalHeap.Owns final result trial.grid →
        finalHeap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 1) limit →
        (trial.status = 0 → normalizedCapacity (UInt64.ofNat grid.size) 7 ≤ result.capacity) →
        (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region) →
        wp module rest Q final
          (advanceTrialFrame frame n time source.root alpha dt trial.dt result.root trial.status) env) :
    wp module (advanceTrialBody.take 54 ++ rest) Q initial frame env := by
  let dt := Time.proposal n time alpha
  have hEncoding := Time.proposal_fuel_encoding n time alpha
  have hNoOverflow := hEncoding.2
  have hIncreasing : Time.proposal n time alpha ≤ Time.proposal n time alpha + 1 := by
    simpa only [UInt64.not_lt] using hNoOverflow
  have hRetry := retry_pages_exact env initial heap source grid n (dt + 1) time dt spare limit pageLimit
    hn hIndexed hHeap hOwner hPages hPageLimit hReserve hLimit hCap hLimitPages
  dsimp only at hRetry
  simp only [dt, hEncoding.1] at hRetry
  obtain ⟨hAlphaBound, hAlphaRead⟩ := List.getElem_of_getElem? hAlpha
  unfold advanceTrialBody advanceWorkBody advanceLoop func85
  dsimp only
  advance_trial_peel
  refine wp_call_tw (proposal_exact env initial n time alpha hn.2) ?_
  rintro current values ⟨hCurrent, rfl⟩
  subst current
  advance_trial_peel
  refine wp_call_tw hRetry ?_
  rintro final values ⟨finalHeap, result, rfl, hStore, hFinalPages, hResult, hReserved, hCapacity, hSeparated⟩
  advance_trial_peel
  simpa [advanceTrialFrame, hParams, dt] using
    hNext final finalHeap result hStore hFinalPages hResult hReserved hCapacity hSeparated

#print axioms advance_total_trial_spec

end Project.EulerRiemann.Execution
