import Project.EulerRiemann.SweepSetup
import Project.EulerRiemann.MemoryLength
import Project.EulerRiemann.SweepLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity Project.ProofKit.FixedArrayResult

theorem sweep_shape : func70 = func70.take 6 ++ (func70.drop 6).take 18 ++
    (func70.drop 24).take 15 ++ (func70.drop 39).take 8 ++
    [.block 0 0 [.loop 0 0 sweepLoop]] ++ func70.drop 48 := rfl

theorem sweep_tail_shape : func70.drop 48 =
    [.localGet 43, .localSet 38, .localGet 38, .localSet 39,
      .localGet 38, .localSet 40, .localGet 39, .localGet 40] := rfl

theorem sweep_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (axis : Bool) (ratio owner source base count : UInt64)
    (grid : Array Traversal.Cell) (nodes : List FreeNode) (hn : 2 ≤ n ∧ n ≤ 800)
    (hIndexed : Traversal.Indexed n grid) (hGrid : Memory.GridAt initial source grid)
    (hGlobal0 : initial.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : initial.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : initial.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt initial.mem nodes) (hSep : gridFreeSeparated source grid.size nodes)
    (hHeap : source.toNat + 8 * (7 * grid.size + 1) ≤ base.toNat)
    (hPages : initial.mem.pages ≤ 65536)
    (hBump : takeFirstFitFrom 0 (normalizedCapacity (UInt64.ofNat grid.size) 7) nodes = none →
      base.toNat + 48 + (8 + grid.size * 56) ≤ 4294967296 ∧
      bumpPages base (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
        initial.memoryCap Project.EulerRiemann.«module» 0) :
    let need := normalizedCapacity (UInt64.ofNat grid.size) 7
    let root := allocatedRoot base need nodes
    let allocated := countedStore (allocatedStore initial base need nodes) count
    let prepared := writeLength allocated root (UInt64.ofNat grid.size)
    TerminatesWith env Project.EulerRiemann.«module» 70 initial
      [.i64 source, .i64 owner, .i64 ratio, .i64 (boolWord axis), .i64 (UInt64.ofNat n)]
      (fun final values => values = [.i64 root, .i64 root] ∧
        Memory.GridAt final source grid ∧
        Memory.GridAt final root (Traversal.sweep n axis ratio grid) ∧
        Memory.WritesGrid prepared final root grid.size) := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 7
  let root := allocatedRoot base need nodes
  let allocated := countedStore (allocatedStore initial base need nodes) count
  let prepared := writeLength allocated root (UInt64.ofNat grid.size)
  change TerminatesWith _ _ _ _ _ (fun final values => values = [.i64 root, .i64 root] ∧
    Memory.GridAt final source grid ∧ Memory.GridAt final root (Traversal.sweep n axis ratio grid) ∧
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
  have hPrefix : Memory.PrefixAt prepared root (Traversal.sweep n axis ratio grid) 0 := by
    simpa only [Traversal.sweep_size] using
      Memory.writeLength_prefix allocated root (Traversal.sweep n axis ratio grid)
        (by simpa only [Traversal.sweep_size] using hBounds.2.1)
        (by simpa only [Traversal.sweep_size] using hBounds.2.2)
  have hLengthBound : root.toUInt32.toNat + 8 ≤ allocated.mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  refine TerminatesWith.of_wp_entry_for (f := func70Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func70 _ initial
    (func70Def.toLocals (sweepParameters n axis ratio owner source)) env
  rw [sweep_shape]
  simp only [List.append_assoc]
  apply sweep_entry_spec env initial n axis ratio owner source grid hGrid
  apply sweep_capacity_spec env initial _ _ rfl (sweep_saved_length source grid.size)
    (UInt64.ofNat grid.size) 0 0 0 0 0 0 (sweep_saved_count source grid.size)
  apply allocation_spec env initial _ _ rfl (sweep_saved_length source grid.size)
    base need 0 0 0 0 0 count nodes hGlobal0 hGlobal1 hGlobal2 hList
    (fun hNone => ⟨hFit32 hNone, (hBump hNone).2⟩) hPages
  intro previous current capacity next
  apply sweep_install_spec env allocated n axis ratio owner source root need previous current
    capacity next grid.size hLengthBound
  apply sweep_loop_spec env prepared n axis ratio owner source root grid hn hIndexed
    hPreparedGrid hDisjoint 0 (Nat.zero_le _) hPrefix {} _ (by rfl)
  intro final scratch hSource hOutput hWrites
  rw [sweep_tail_shape]
  simp [wp_simp, sweepFrame, func70Def, Function.numParams]
  exact ⟨hSource, hOutput, hWrites⟩

#print axioms sweep_shape
#print axioms sweep_tail_shape
#print axioms sweep_exact

end Project.EulerRiemann.Execution
