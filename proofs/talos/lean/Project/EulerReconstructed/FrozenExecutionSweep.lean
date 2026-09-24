import Project.EulerReconstructed.FrozenSweepSetup
import Project.EulerRiemann.FrozenMemoryLength
import Project.EulerReconstructed.FrozenSweepLoop

namespace Project.EulerReconstructed.Frozen.Execution
open Project.EulerRiemann.Frozen
open Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity Project.ProofKit.FixedArrayResult

theorem sweep_shape : func121 = func121.take 6 ++ (func121.drop 6).take 18 ++
    (func121.drop 24).take 15 ++ (func121.drop 39).take 8 ++
    [.block 0 0 [.loop 0 0 sweepLoop]] ++ func121.drop 48 := rfl

theorem sweep_tail_shape : func121.drop 48 =
    [.localGet 45, .localSet 40, .localGet 40, .localSet 41,
      .localGet 40, .localSet 42, .localGet 41, .localGet 42] := rfl

theorem sweep_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (fuel : UInt64) (axis : Bool) (ratio owner source base count : UInt64)
    (grid : Array Project.EulerRiemann.Frozen.Traversal.Cell) (nodes : List FreeNode) (hn : 2 ≤ n ∧ n ≤ 800)
    (hIndexed : Project.EulerRiemann.Frozen.Traversal.Indexed n grid) (hGrid : Memory.GridAt initial source grid)
    (hGlobal0 : initial.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : initial.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : initial.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt initial.mem nodes) (hSep : gridFreeSeparated source grid.size nodes)
    (hHeap : source.toNat + 8 * (7 * grid.size + 1) ≤ base.toNat)
    (hPages : initial.mem.pages ≤ 65536)
    (hBump : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) nodes = none →
      base.toNat + 48 + (8 + grid.size * 56) ≤ 4294967296 ∧
      bumpPages base (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
        initial.memoryCap Project.EulerReconstructed.Frozen.«module» 0) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let root := allocatedRoot base need nodes
    let allocated := countedStore (allocatedStore initial base need nodes) count
    let prepared := writeLength allocated root (UInt64.ofNat grid.size)
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 121 initial
      [.i64 source, .i64 owner, .i64 ratio, .i64 (boolWord axis), .i64 fuel, .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 root, .i64 root] ∧
        Memory.GridAt final source grid ∧
        Memory.GridAt final root (Traversal.sweep n fuel.toNat axis ratio grid) ∧
        Memory.WritesGrid prepared final root grid.size) := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 7
  let root := allocatedRoot base need nodes
  let allocated := countedStore (allocatedStore initial base need nodes) count
  let prepared := writeLength allocated root (UInt64.ofNat grid.size)
  change TerminatesWith _ _ _ _ _ (fun final values => values = [.i64 root, .i64 root] ∧
    Memory.GridAt final source grid ∧ Memory.GridAt final root (Traversal.sweep n fuel.toNat axis ratio grid) ∧
    Memory.WritesGrid prepared final root grid.size)
  have hSize : grid.size ≤ 640000 := by
    rw [hIndexed.1]
    exact Nat.mul_le_mul hn.2 hn.2
  have hWord := UInt64.toNat_ofNat_of_lt' hGrid.size_lt
  have hNeed : need.toNat = 8 + grid.size * 56 := by
    simpa only [hWord] using sweep_capacity_toNat (UInt64.ofNat grid.size) (by omega)
  have hFit32 : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 := by
    intro hNone
    simpa only [hNeed] using (hBump hNone).1
  have hAllocatedGrid : Memory.GridAt allocated source grid := by
    apply gridAt_counted
    exact gridAt_allocated initial base need source nodes grid hList hGrid hSep
      (fun hNone => ⟨hFit32 hNone, hHeap⟩)
  have hBounds := sweep_allocated_bounds initial base grid.size nodes hSize hList
    (fun hNone => (hBump hNone).1)
  change 48 ≤ root.toNat ∧ root.toNat + 8 * (7 * grid.size + 1) ≤ 4294967296 ∧
    root.toNat + 8 * (7 * grid.size + 1) ≤ allocated.mem.pages * 65536 at hBounds
  have hDisjoint := allocated_disjoint initial base need source nodes grid.size hList hSep
    (by omega) (fun hNone => ⟨hFit32 hNone, hHeap⟩)
  change source.toNat + 8 * (7 * grid.size + 1) ≤ root.toNat ∨
    root.toNat + 8 * (7 * grid.size + 1) ≤ source.toNat at hDisjoint
  have hPreparedGrid : Memory.GridAt prepared source grid :=
    hAllocatedGrid.writeLength_disjoint (UInt64.ofNat grid.size) (by omega) (by omega)
  have hPrefix : Memory.PrefixAt prepared root (Traversal.sweep n fuel.toNat axis ratio grid) 0 := by
    simpa only [Traversal.sweep_size] using
      Memory.writeLength_prefix allocated root (Traversal.sweep n fuel.toNat axis ratio grid)
        (by simpa only [Traversal.sweep_size] using hBounds.2.1)
        (by simpa only [Traversal.sweep_size] using hBounds.2.2)
  have hLengthBound : root.toUInt32.toNat + 8 ≤ allocated.mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  refine TerminatesWith.of_wp_entry_for (f := func121Def) rfl ?_ (by decide)
  change wp Project.EulerReconstructed.Frozen.«module» func121 _ initial
    (func121Def.toLocals (sweepParameters n fuel axis ratio owner source)) env
  rw [sweep_shape]
  simp only [List.append_assoc]
  apply sweep_entry_spec env initial n fuel axis ratio owner source grid hGrid
  apply sweep_capacity_spec env initial n fuel axis ratio owner source grid.size
  rw [sweep_allocation_shape]
  change wp _ (Project.ProofKit.FixedArrayAllocate.program 49 7 ++ _) _ initial
    (Project.ProofKit.FixedArraySearch.frame _ _ [] need 0 0 0 0 0) _
  apply Project.ProofKit.FixedArrayAllocate.program_spec _ env initial
    (sweepParameters n fuel axis ratio owner source) (sweepSaved source grid.size) [] 49
    (by simp [sweepParameters, sweepSaved]) base need 7 0 0 0 0 0 count nodes
    hGlobal0 hGlobal1 hGlobal2 hList
    (fun hNone => ⟨hFit32 hNone, (hBump hNone).2⟩) hPages rfl
  intro previous current capacity next
  change wp _ _ _ allocated
    (sweepAllocationFrame (sweepParameters n fuel axis ratio owner source)
      (sweepSaved source grid.size) need previous current capacity next root) _
  apply sweep_install_spec env allocated n fuel axis ratio owner source root need previous current
    capacity next grid.size hLengthBound
  apply sweep_loop_spec env prepared n fuel axis ratio owner source root grid hn hIndexed
    hPreparedGrid hDisjoint 0 (Nat.zero_le _) hPrefix {} _ (by rfl)
  intro final scratch hSource hOutput hWrites
  rw [sweep_tail_shape]
  simp [wp_simp, sweepFrame, func121Def, Function.numParams]
  exact ⟨hSource, hOutput, hWrites⟩

#print axioms sweep_shape
#print axioms sweep_tail_shape
#print axioms sweep_exact

end Project.EulerReconstructed.Frozen.Execution
