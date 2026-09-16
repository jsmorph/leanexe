import Project.EulerCertificate.SweepReserve
import Project.EulerCertificate.BoundaryExecution
import Project.EulerCertificate.Control
import Project.EulerReconstructed.TraversalSafety

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def AttemptPost (initial : Store Unit) (initialHeap : Heap) (need : UInt64)
    (spare limit pageLimit : Nat) (expected : Option Project.EulerCertificate.Control.Trial)
    (final : Store Unit) (values : List Wasm.Value) : Prop :=
  ∃ heap, RetryStoreAt initial initialHeap final heap ∧ final.mem.pages ≤ pageLimit ∧
    match expected with
    | none => values = List.replicate 15 (.i64 0) ∧ heap.Reserved need (spare + 2) limit
    | some trial => ∃ node,
        values = vectorValues trial.boundary ++ [.i64 node.root, .i64 node.root, .i64 1] ∧
        heap.Owns final node trial.grid ∧ heap.Reserved need (spare + 1) limit ∧
        need ≤ node.capacity ∧
        ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), initialHeap.Owns initial saved savedGrid →
          regionsDisjoint saved.region node.region

macro "certificate_attempt_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func176Def, vectorValues, boundsValues, List.set, List.cons_append,
        List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
        boolWord, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      conv => arg 2; simp [*, -UInt64.ofNat_add])

theorem attempt_pages_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (trials dt ratio : UInt64)
    (spare limit pageLimit : Nat) (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hReserve : heap.Reserved (normalizedCapacity (UInt64.ofNat grid.size) 7) (spare + 2) limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerCertificate.«module» 0 * 65536)
    (hLimitPages : limit ≤ pageLimit * 65536) :
    TerminatesWith env Project.EulerCertificate.«module» 176 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 dt, .i64 trials, .i64 (UInt64.ofNat n)]
      (AttemptPost initial heap (normalizedCapacity (UInt64.ofNat grid.size) 7)
        spare limit pageLimit (Project.EulerCertificate.Control.attempt n trials.toNat dt ratio grid)) := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 7
  let first := allocatedNode heap.top need heap.nodes
  let afterFirst := heap.allocate need
  let middle := Project.EulerReconstructed.Traversal.sweep n trials.toNat false ratio grid
  let next := Project.EulerReconstructed.Traversal.sweep n trials.toNat true ratio middle
  have hAttempt : Project.EulerCertificate.Control.attempt n trials.toNat dt ratio grid =
      if Traversal.accepted middle then
        if Traversal.accepted next then
          some ⟨next, Boundary.physicalStep n trials.toNat dt grid middle⟩
        else none
      else none := rfl
  refine TerminatesWith.of_wp_entry_for (f := func176Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func176 _ initial
    (func176Def.toLocals [.i64 (UInt64.ofNat n), .i64 trials, .i64 dt,
      .i64 ratio, .i64 source.root, .i64 source.root]) env
  unfold func176
  certificate_attempt_peel
  refine wp_call_tw (sweep_pages_reserved env initial heap source grid n trials false ratio
    (spare + 1) limit pageLimit hn hIndexed hHeap hOwner hPages hPageLimit
    (by simpa only [Nat.add_assoc] using hReserve) hLimit hCap hLimitPages) ?_
  rintro firstStore firstValues ⟨rfl, hStore1, hOwner1, hPages1, hReserve1, hCapacity1, hSep1⟩
  certificate_attempt_peel
  refine wp_call_tw (accepted_exact env firstStore first.root first.root middle hOwner1.buffer.values) ?_
  rintro sameStore acceptedValues ⟨hSame, rfl⟩
  subst sameStore
  cases hx : Traversal.accepted middle with
  | false =>
    certificate_attempt_peel
    refine wp_call_tw (release_owned env firstStore afterFirst first middle hStore1.heapState hOwner1) ?_
    rintro final releaseValues ⟨rfl, hFinal, hFinalHeap⟩
    subst final
    have hReleased := hStore1.released first middle hOwner1 hSep1
    have hFrees : (afterFirst.releaseStore firstStore first).globals.globals[5]? =
        some (.i64 (afterFirst.release first).frees) := by rw [hFinalHeap.globals]; rfl
    certificate_attempt_peel
    simp only [AttemptPost]
    exact ⟨afterFirst.release first, hReleased,
      by simpa only [Heap.releaseStore, releasedStore_pages] using hPages1,
      rfl, hReserve1.release first hCapacity1⟩
  | true =>
    have hMiddleIndexed := Project.EulerReconstructed.Traversal.sweep_indexed
      n trials.toNat false ratio grid hIndexed
    have hCap1 : firstStore.memoryCap Project.EulerCertificate.«module» 0 =
        initial.memoryCap Project.EulerCertificate.«module» 0 := hStore1.cap
    have secondCall := sweep_pages_reserved env firstStore afterFirst first middle n trials true ratio
      spare limit pageLimit hn hMiddleIndexed hStore1.heapState hOwner1 hPages1 hPageLimit
      (by simpa only [middle, Project.EulerReconstructed.Traversal.sweep_size] using hReserve1)
      hLimit (by rw [hCap1]; exact hCap) hLimitPages
    simp only [middle, Project.EulerReconstructed.Traversal.sweep_size] at secondCall
    certificate_attempt_peel
    refine wp_call_tw secondCall ?_
    rintro secondStore secondValues ⟨rfl, hStore2, hOwner2, hPages2, hReserve2, hCapacity2, hSep2⟩
    let afterSecond := afterFirst.allocate need
    let second := allocatedNode afterFirst.top need afterFirst.nodes
    have hMiddle2 := hStore2.held first middle hOwner1
    have hSource2 := hStore2.held source grid (hStore1.held source grid hOwner)
    have hBoth : RetryStoreAt initial heap secondStore afterSecond :=
      ⟨hStore2.heapState, hStore2.pages, hStore2.cap.trans hStore1.cap,
        fun saved savedGrid hSaved => hStore2.held saved savedGrid (hStore1.held saved savedGrid hSaved)⟩
    have hNextSep (saved : FreeNode) (savedGrid : Array Traversal.Cell)
        (hSaved : heap.Owns initial saved savedGrid) : regionsDisjoint saved.region second.region :=
      hSep2 saved savedGrid (hStore1.held saved savedGrid hSaved)
    have hAfterRelease := hBoth.released first middle hMiddle2 hSep1
    have hNextAfterRelease := hOwner2.released first hMiddle2.buffer.rootBound
      (by have := hMiddle2.buffer.addressBound; omega)
      (regionsDisjoint_symm (hSep2 first middle hOwner1))
    have hReleasedReserve := hReserve2.release first hCapacity1
    certificate_attempt_peel
    refine wp_call_tw (accepted_exact env secondStore second.root second.root next hOwner2.buffer.values) ?_
    rintro sameStore nextAcceptedValues ⟨hSame, rfl⟩
    subst sameStore
    cases hy : Traversal.accepted next with
    | false =>
      certificate_attempt_peel
      refine wp_call_tw (release_owned env secondStore afterSecond first middle hStore2.heapState hMiddle2) ?_
      rintro released releaseValues ⟨rfl, hReleased, hReleasedHeap⟩
      subst released
      have hFrees : (afterSecond.releaseStore secondStore first).globals.globals[5]? =
          some (.i64 (afterSecond.release first).frees) := by rw [hReleasedHeap.globals]; rfl
      certificate_attempt_peel
      refine wp_call_tw (release_owned env (afterSecond.releaseStore secondStore first)
        (afterSecond.release first) second next hReleasedHeap hNextAfterRelease) ?_
      rintro final releaseValues ⟨rfl, hFinal, hFinalHeap⟩
      subst final
      have hFinalStore := hAfterRelease.released second next hNextAfterRelease hNextSep
      have hFinalFrees : ((afterSecond.release first).releaseStore
          (afterSecond.releaseStore secondStore first) second).globals.globals[5]? =
          some (.i64 ((afterSecond.release first).release second).frees) := by
        rw [hFinalHeap.globals]; rfl
      certificate_attempt_peel
      simp only [AttemptPost]
      exact ⟨(afterSecond.release first).release second, hFinalStore,
        by simpa only [Heap.releaseStore, releasedStore_pages] using hPages2,
        rfl, hReleasedReserve.release second hCapacity2⟩
    | true =>
      have boundaryCall := boundary_physicalStep_exact env secondStore n trials dt
        source.root source.root first.root first.root grid middle hn hIndexed hMiddleIndexed
        hSource2.buffer.values hMiddle2.buffer.values
      generalize hBoundary : Boundary.physicalStep n trials.toNat dt grid middle = boundary at boundaryCall
      certificate_attempt_peel
      refine wp_call_tw boundaryCall ?_
      rintro sameStore boundaryValues ⟨hSame, rfl⟩
      subst sameStore
      certificate_attempt_peel
      refine wp_call_tw (release_owned env secondStore afterSecond first middle hStore2.heapState hMiddle2) ?_
      rintro final releaseValues ⟨rfl, hFinal, hFinalHeap⟩
      subst final
      have hFrees : (afterSecond.releaseStore secondStore first).globals.globals[5]? =
          some (.i64 (afterSecond.release first).frees) := by rw [hFinalHeap.globals]; rfl
      certificate_attempt_peel
      simp only [AttemptPost]
      refine ⟨afterSecond.release first, hAfterRelease,
        by simpa only [Heap.releaseStore, releasedStore_pages] using hPages2,
        second, ?_, hNextAfterRelease, hReleasedReserve, hCapacity2, hNextSep⟩
      rfl

#print axioms attempt_pages_exact
end Project.EulerCertificate.Execution
