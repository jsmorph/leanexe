import Project.EulerRiemann.AdvanceScan

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

macro "advance_trial_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem advance_trial_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (source : FreeNode) (grid : Array Traversal.Cell)
    (n : Nat) (time alpha : UInt64) (spare limit : Nat)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
      .i64 source.root, .i64 source.root])
    (hLocals : frame.locals.length = 45) (hValues : frame.values = [])
    (hAlpha : frame.locals[12]? = some (.i64 alpha))
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerRiemann.«module» 0 * 65536)
    (hSuccess : (Control.retry ((Time.proposal n time alpha).toNat + 1)
      n time (Time.proposal n time alpha) grid).status = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let dt := Time.proposal n time alpha
      let trial := Control.retry (dt.toNat + 1) n time dt grid
      ∀ final finalHeap result,
        RetryStoreAt initial heap final finalHeap → finalHeap.Owns final result trial.grid →
        finalHeap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 1) limit →
        normalizedCapacity (UInt64.ofNat grid.size) 7 ≤ result.capacity →
        (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          regionsDisjoint saved.region result.region) →
        wp Project.EulerRiemann.«module» rest Q final
          (advanceTrialFrame frame n time source.root alpha dt trial.dt result.root) env) :
    wp Project.EulerRiemann.«module» (advanceTrialBody.take 54 ++ rest) Q initial frame env := by
  let dt := Time.proposal n time alpha
  have hEncoding := Control.retry_fuel_encoding n time dt grid hSuccess
  have hNoOverflow := hEncoding.2
  have hIncreasing : Time.proposal n time alpha ≤ Time.proposal n time alpha + 1 := by
    simpa only [UInt64.not_lt] using hNoOverflow
  have hRetry := retry_exact_of_success env initial heap source grid n (dt + 1) time dt spare limit
    hn hIndexed hHeap hOwner hPages hReserve hLimit hCap (by simpa only [hEncoding.1] using hSuccess)
  dsimp only at hRetry
  simp only [hEncoding.1] at hRetry
  obtain ⟨hAlphaBound, hAlphaRead⟩ := List.getElem_of_getElem? hAlpha
  unfold advanceTrialBody advanceWorkBody advanceLoop func78
  dsimp only
  advance_trial_peel
  refine wp_call_tw (proposal_exact env initial n time alpha hn.2) ?_
  rintro current values ⟨hCurrent, rfl⟩
  subst current
  advance_trial_peel
  refine wp_call_tw hRetry ?_
  rintro final values ⟨finalHeap, result, rfl, hStore, hResult, hReserved, hCapacity, hSeparated⟩
  advance_trial_peel
  simpa [advanceTrialFrame, hParams, dt] using
    hNext final finalHeap result hStore hResult hReserved hCapacity hSeparated

#print axioms advance_trial_spec

end Project.EulerRiemann.Execution
