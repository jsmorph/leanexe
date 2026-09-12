import Project.EulerRiemann.StepState

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

theorem step_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (ratio : UInt64)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hPages : initial.mem.pages ≤ 65536)
    (hFirst : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) heap.nodes = none →
      heap.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 ∧
      bumpPages heap.top (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
        initial.memoryCap Project.EulerRiemann.«module» 0)
    (hSecond : let need := normalizedCapacity (UInt64.ofNat grid.size) 7
      let afterFirst := heap.allocate need
      takeFirstFitFrom 0 need afterFirst.nodes = none →
        afterFirst.top.toNat + 48 + (8 + grid.size * 56) < 4294967296 ∧
        bumpPages afterFirst.top need ≤ initial.memoryCap Project.EulerRiemann.«module» 0) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let result := stepAllocation heap need (Traversal.accepted (Traversal.sweep n false ratio grid))
    TerminatesWith env Project.EulerRiemann.«module» 73 initial
      [.i64 source.root, .i64 source.root, .i64 ratio, .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 result.2.root, .i64 result.2.root] ∧
        result.1.At final ∧ result.1.Owns final result.2 (Traversal.step n ratio grid) ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap Project.EulerRiemann.«module» 0 = initial.memoryCap Project.EulerRiemann.«module» 0 ∧
        ∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), heap.Owns initial saved savedGrid →
          result.1.Owns final saved savedGrid ∧ regionsDisjoint saved.region result.2.region) := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 7
  let first := allocatedNode heap.top need heap.nodes
  let afterFirst := heap.allocate need
  let middle := Traversal.sweep n false ratio grid
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
  refine TerminatesWith.of_wp_entry_for (f := func73Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func73 _ initial
    (func73Def.toLocals [.i64 (UInt64.ofNat n), .i64 ratio, .i64 source.root, .i64 source.root]) env
  unfold func73
  step_peel
  refine wp_call_tw (sweep_owned env initial heap source grid n false ratio hn hIndexed hHeap hOwner hPages hFirst) ?_
  rintro firstStore firstValues ⟨rfl, hHeap1, _, hOwner1, _, hPages1, hCap1, hWrites1⟩
  have hFrame1 (saved : FreeNode) (savedGrid : Array Traversal.Cell)
      (hSaved : heap.Owns initial saved savedGrid) :
      afterFirst.Owns firstStore saved savedGrid ∧ regionsDisjoint saved.region first.region :=
    ⟨hSaved.swept need grid.size hHeap (by omega) hFit1 hWrites1,
      allocated_region_disjoint heap.top need saved heap.nodes hSaved.buffer.rootBound
        hSaved.separated hSaved.below hFit1⟩
  step_peel
  refine wp_call_tw (accepted_exact env firstStore first.root first.root middle hOwner1.buffer.values) ?_
  rintro sameStore acceptedValues ⟨hSame, rfl⟩
  subst sameStore
  cases hAccepted : Traversal.accepted middle with
  | false =>
    step_peel
    simpa [stepAllocation, Traversal.step, middle, hAccepted, hPages1, hCap1, afterFirst, first, need] using
      And.intro hHeap1 (And.intro hOwner1 (And.intro hPages1 (And.intro hCap1 hFrame1)))
  | true =>
    have hMiddleIndexed := Traversal.sweep_indexed n false ratio grid hIndexed
    have hSecondCall := sweep_owned env firstStore afterFirst first middle n true ratio hn hMiddleIndexed
      hHeap1 hOwner1 hPages1 (by
        simpa only [middle, Traversal.sweep_size, hCap1] using hSecond)
    simp only [middle, Traversal.sweep_size] at hSecondCall
    step_peel
    refine wp_call_tw hSecondCall ?_
    rintro secondStore secondValues ⟨rfl, hHeap2, hMiddle2, hOutput2, hDisjoint2, hPages2, hCap2, hWrites2⟩
    let afterSecond := afterFirst.allocate need
    let second := allocatedNode afterFirst.top need afterFirst.nodes
    have hFrame2 (saved : FreeNode) (savedGrid : Array Traversal.Cell)
        (hSaved : heap.Owns initial saved savedGrid) :
        afterSecond.Owns secondStore saved savedGrid ∧
          regionsDisjoint saved.region first.region ∧ regionsDisjoint saved.region second.region := by
      have hSaved1 := hFrame1 saved savedGrid hSaved
      exact ⟨hSaved1.1.swept need grid.size hHeap1 (by omega) hFit2 hWrites2,
        hSaved1.2, allocated_region_disjoint afterFirst.top need saved afterFirst.nodes
          hSaved1.1.buffer.rootBound hSaved1.1.separated hSaved1.1.below hFit2⟩
    step_peel
    refine wp_call_tw (release_owned env secondStore afterSecond first middle hHeap2 hMiddle2) ?_
    rintro final releaseValues ⟨rfl, hFinal, hFinalHeap⟩
    subst final
    have hRoot := hMiddle2.buffer.rootBound
    have hRoot32 : first.root.toNat ≤ 4294967296 := by
      have := hMiddle2.buffer.addressBound
      omega
    have hOutput := hOutput2.released first hRoot hRoot32 (regionsDisjoint_symm hDisjoint2)
    have hFinalFrame (saved : FreeNode) (savedGrid : Array Traversal.Cell)
        (hSaved : heap.Owns initial saved savedGrid) :
        (afterSecond.release first).Owns (afterSecond.releaseStore secondStore first) saved savedGrid ∧
          regionsDisjoint saved.region second.region := by
      have hSaved2 := hFrame2 saved savedGrid hSaved
      exact ⟨hSaved2.1.released first hRoot hRoot32 hSaved2.2.1, hSaved2.2.2⟩
    have hFrees : (afterSecond.releaseStore secondStore first).globals.globals[5]? =
        some (.i64 (afterSecond.release first).frees) := by
      rw [hFinalHeap.globals]
      rfl
    step_peel
    simpa [stepAllocation, Traversal.step, middle, hAccepted, afterFirst, afterSecond, first, second, need, Heap.releaseStore,
      releasedStore_pages, releasedStore_memoryCap] using
      And.intro hFinalHeap (And.intro hOutput (And.intro hPages2 (And.intro (hCap2.trans hCap1) hFinalFrame)))

#print axioms step_exact

end Project.EulerRiemann.Execution
