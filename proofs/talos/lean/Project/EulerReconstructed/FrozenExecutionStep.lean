import Project.EulerReconstructed.FrozenRetainedMemory
import Project.EulerRiemann.FrozenStepState
import Project.EulerReconstructed.FrozenTraversalHelpers
import Project.EulerReconstructed.FrozenSweepPageBound

namespace Project.EulerReconstructed.Frozen.Execution
open Project.EulerRiemann.Frozen
open Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

macro "reconstructed_step_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func124Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        boolWord, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.not_le])

theorem step_pages_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Frozen.Traversal.Cell) (n : Nat) (fuel ratio : UInt64)
    (pageLimit : Nat)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Frozen.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ pageLimit) (hPageLimit : pageLimit ≤ 65536)
    (hFirst : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) heap.nodes = none →
      heap.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 ∧
      bumpPages heap.top (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
        initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0)
    (hSecond : let need := normalizedCapacity (UInt64.ofNat grid.size) 7
      let afterFirst := heap.allocate need
      takeFirstFitFrom 0 need afterFirst.nodes = none →
        afterFirst.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 ∧
        bumpPages afterFirst.top need ≤ initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0)
    (hFirstPages : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) heap.nodes = none →
      heap.top.toNat + 48 + (normalizedCapacity (UInt64.ofNat grid.size) 7).toNat ≤ pageLimit * 65536)
    (hSecondPages : let need := normalizedCapacity (UInt64.ofNat grid.size) 7
      let afterFirst := heap.allocate need
      takeFirstFitFrom 0 need afterFirst.nodes = none →
        afterFirst.top.toNat + 48 + need.toNat ≤ pageLimit * 65536) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let result := stepAllocation heap need (Project.EulerRiemann.Frozen.Traversal.accepted (Traversal.sweep n fuel.toNat false ratio grid))
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 124 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 fuel, .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 result.2.root, .i64 result.2.root] ∧
        result.1.At final ∧ result.1.Owns final result.2 (Traversal.step n fuel.toNat ratio grid) ∧
        final.mem.pages ≤ pageLimit ∧
        final.memoryCap Project.EulerReconstructed.Frozen.«module» 0 = initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0 ∧
        ∀ (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Frozen.Traversal.Cell), heap.Owns initial saved savedGrid →
          result.1.Owns final saved savedGrid ∧ regionsDisjoint saved.region result.2.region) := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 7
  let first := allocatedNode heap.top need heap.nodes
  let afterFirst := heap.allocate need
  let middle := Traversal.sweep n fuel.toNat false ratio grid
  have hSize : grid.size ≤ 640000 := by
    rw [hIndexed.1]
    exact Nat.mul_le_mul hn.2 hn.2
  have hWord := UInt64.toNat_ofNat_of_lt' hOwner.buffer.values.size_lt
  have hNeed : need.toNat = 8 + grid.size * 56 := by
    simpa only [hWord] using sweep_capacity_toNat (UInt64.ofNat grid.size) (by omega)
  have hFit1 : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := by
    intro hNone
    have := (hFirst hNone).1
    omega
  have hFit2 : takeFirstFitFrom 0 need afterFirst.nodes = none →
      afterFirst.top.toNat + 48 + need.toNat ≤ 4294967296 := by
    intro hNone
    have := (hSecond hNone).1
    change afterFirst.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 at this
    omega
  refine TerminatesWith.of_wp_entry_for (f := func124Def) rfl ?_ (by decide)
  change wp Project.EulerReconstructed.Frozen.«module» func124 _ initial
    (func124Def.toLocals [.i64 (UInt64.ofNat n), .i64 fuel, .i64 ratio, .i64 source.root, .i64 source.root]) env
  unfold func124
  reconstructed_step_peel
  refine wp_call_tw (sweep_pages_owned env initial heap source grid n fuel false ratio pageLimit
    hn hIndexed hHeap hOwner hPages hPageLimit hFirst hFirstPages) ?_
  rintro firstStore firstValues ⟨rfl, hHeap1, _, hOwner1, _, hPages1, hCap1, hWrites1⟩
  have hFrame1 (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Frozen.Traversal.Cell)
      (hSaved : heap.Owns initial saved savedGrid) :
      afterFirst.Owns firstStore saved savedGrid ∧ regionsDisjoint saved.region first.region :=
    ⟨hSaved.swept need grid.size hHeap (by omega) hFit1 hWrites1,
      allocated_region_disjoint heap.top need saved heap.nodes hSaved.buffer.rootBound
        hSaved.separated hSaved.below hFit1⟩
  reconstructed_step_peel
  refine wp_call_tw (accepted_exact env firstStore first.root first.root middle hOwner1.buffer.values) ?_
  rintro sameStore acceptedValues ⟨hSame, rfl⟩
  subst sameStore
  cases hAccepted : Project.EulerRiemann.Frozen.Traversal.accepted middle with
  | false =>
    reconstructed_step_peel
    simpa [stepAllocation, Traversal.step, middle, hAccepted, hPages1, hCap1, afterFirst, first, need] using
      And.intro hHeap1 (And.intro hOwner1 (And.intro hPages1 (And.intro hCap1 hFrame1)))
  | true =>
    have hMiddleIndexed := Traversal.sweep_indexed n fuel.toNat false ratio grid hIndexed
    have hSecondCall := sweep_pages_owned env firstStore afterFirst first middle n fuel true ratio pageLimit
      hn hMiddleIndexed hHeap1 hOwner1 hPages1 hPageLimit (by
        simpa only [middle, Traversal.sweep_size, hCap1] using hSecond)
      (by simpa only [middle, Traversal.sweep_size] using hSecondPages)
    simp only [middle, Traversal.sweep_size] at hSecondCall
    reconstructed_step_peel
    refine wp_call_tw hSecondCall ?_
    rintro secondStore secondValues ⟨rfl, hHeap2, hMiddle2, hOutput2, hDisjoint2, hPages2, hCap2, hWrites2⟩
    let afterSecond := afterFirst.allocate need
    let second := allocatedNode afterFirst.top need afterFirst.nodes
    have hFrame2 (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Frozen.Traversal.Cell)
        (hSaved : heap.Owns initial saved savedGrid) :
        afterSecond.Owns secondStore saved savedGrid ∧
          regionsDisjoint saved.region first.region ∧ regionsDisjoint saved.region second.region := by
      have hSaved1 := hFrame1 saved savedGrid hSaved
      exact ⟨hSaved1.1.swept need grid.size hHeap1 (by omega) hFit2 hWrites2,
        hSaved1.2, allocated_region_disjoint afterFirst.top need saved afterFirst.nodes
          hSaved1.1.buffer.rootBound hSaved1.1.separated hSaved1.1.below hFit2⟩
    reconstructed_step_peel
    refine wp_call_tw (release_owned env secondStore afterSecond first middle hHeap2 hMiddle2) ?_
    rintro final releaseValues ⟨rfl, hFinal, hFinalHeap⟩
    subst final
    have hRoot := hMiddle2.buffer.rootBound
    have hRoot32 : first.root.toNat ≤ 4294967296 := by
      have := hMiddle2.buffer.addressBound
      omega
    have hOutput := hOutput2.released first hRoot hRoot32 (regionsDisjoint_symm hDisjoint2)
    have hFinalFrame (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Frozen.Traversal.Cell)
        (hSaved : heap.Owns initial saved savedGrid) :
        (afterSecond.release first).Owns (afterSecond.releaseStore secondStore first) saved savedGrid ∧
          regionsDisjoint saved.region second.region := by
      have hSaved2 := hFrame2 saved savedGrid hSaved
      exact ⟨hSaved2.1.released first hRoot hRoot32 hSaved2.2.1, hSaved2.2.2⟩
    have hFrees : (afterSecond.releaseStore secondStore first).globals.globals[5]? =
        some (.i64 (afterSecond.release first).frees) := by
      rw [hFinalHeap.globals]
      rfl
    reconstructed_step_peel
    simpa [stepAllocation, Traversal.step, middle, hAccepted, afterFirst, afterSecond, first, second, need, Heap.releaseStore,
      releasedStore_pages, releasedStore_memoryCap] using
      And.intro hFinalHeap (And.intro hOutput (And.intro hPages2 (And.intro (hCap2.trans hCap1) hFinalFrame)))

theorem step_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Frozen.Traversal.Cell) (n : Nat) (fuel ratio : UInt64)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Frozen.Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hFirst : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) heap.nodes = none →
      heap.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 ∧
      bumpPages heap.top (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
        initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0)
    (hSecond : let need := normalizedCapacity (UInt64.ofNat grid.size) 7
      let afterFirst := heap.allocate need
      takeFirstFitFrom 0 need afterFirst.nodes = none →
        afterFirst.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 ∧
        bumpPages afterFirst.top need ≤ initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let result := stepAllocation heap need (Project.EulerRiemann.Frozen.Traversal.accepted (Traversal.sweep n fuel.toNat false ratio grid))
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 124 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 fuel, .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 result.2.root, .i64 result.2.root] ∧
        result.1.At final ∧ result.1.Owns final result.2 (Traversal.step n fuel.toNat ratio grid) ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap Project.EulerReconstructed.Frozen.«module» 0 = initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0 ∧
        ∀ (saved : FreeNode) (savedGrid : Array Project.EulerRiemann.Frozen.Traversal.Cell), heap.Owns initial saved savedGrid →
          result.1.Owns final saved savedGrid ∧ regionsDisjoint saved.region result.2.region) := by
  have hSize : grid.size ≤ 640000 := by
    rw [hIndexed.1]
    exact Nat.mul_le_mul hn.2 hn.2
  have hWord := UInt64.toNat_ofNat_of_lt' hOwner.buffer.values.size_lt
  have hNeed : (normalizedCapacity (UInt64.ofNat grid.size) 7).toNat = 8 + grid.size * 56 := by
    simpa only [hWord] using sweep_capacity_toNat (UInt64.ofNat grid.size) (by omega)
  exact step_pages_exact env initial heap source grid n fuel ratio 65536 hn hIndexed hHeap hOwner
    hPages (by omega) hFirst hSecond
    (fun hNone => by have := (hFirst hNone).1; rw [hNeed]; omega)
    (fun hNone => by have := (hSecond hNone).1; rw [hNeed]; omega)

#print axioms step_pages_exact
#print axioms step_exact

end Project.EulerReconstructed.Frozen.Execution
