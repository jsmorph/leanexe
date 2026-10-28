import Verified.Wasi.ReadLocals
import Verified.Wasi.RuntimeFrame

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

def readAllocateCode : Program :=
  [.localGet 0, .eqzI64,
   .iff 0 1 [.constI64 0] [.localGet 0, .call 3] [] [.i64], .localSet 1]

theorem read_allocation_buffer {before after : Store World} {heap : Heap} {capacity : UInt64}
    (hHeap : heap.At (PureTransport.erase before))
    (hCount : capacity.toNat ≤ 4294967296) (hFits : heap.Fits (allocSize capacity))
    (hStore : PureTransport.erase after =
      heap.allocateStore (PureTransport.erase before) (allocSize capacity) 1) :
    let heap' := heap.allocate (allocSize capacity)
    let root := FixedArrayAllocate.root heap.top (allocSize capacity) heap.free
    Step heap (PureTransport.erase before) (fun _ => True)
        heap' (PureTransport.erase after) [block (PureTransport.erase after) root] ∧
      Heap.Buffer heap' (PureTransport.erase after) root
        (Bytes.snapshot (PureTransport.erase after) root capacity.toNat) ∧
      capacity.toNat ≤ capacityAt (PureTransport.erase after) root ∧
      heap'.top.toNat ≤ heap.top.toNat + allocCost (allocSize capacity).toNat := by
  dsimp only
  rw [hStore]
  have hBlock := hHeap.allocate_block 1 hFits
  have hCapacity := allocated_capacity (allocSize capacity) heap.free
  have hMinimum := Bytes.allocSize_minimum capacity
  have hCount' := le_allocSize hCount
  refine ⟨Step.allocate 1 hHeap hFits, Bytes.block_snapshot hBlock (by omega) _ (by omega),
    ?_, Heap.allocate_top hFits⟩
  rw [hBlock.capacity_eq]
  omega

theorem wp_read_allocate {World : Type} {source target : Module}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv World}
    {heap : Heap} {store : Store World} {capacity root errno length : UInt64}
    {values : List Value} {rest : Program} {Q : Assertion World} {aborts : Bool}
    (hHeap : heap.At (PureTransport.erase store))
    (hCount : capacity.toNat ≤ 4294967296)
    (hCap : (PureTransport.erase store).memoryCap source 0 ≤ 65535)
    (hRoom : capacity ≠ 0 → aborts = false →
      heap.Room (PureTransport.erase store) source (allocSize capacity))
    (hTrap : aborts = true → ∀ final : Store World,
      final.host = store.host → Q (.Trap final "unreachable"))
    (hZero : capacity = 0 →
      wp target rest Q store (readLocals capacity 0 errno length values) targetHost)
    (hAllocated : capacity ≠ 0 → ∀ final : Store World, heap.Fits (allocSize capacity) →
      PureTransport.erase final =
        heap.allocateStore (PureTransport.erase store) (allocSize capacity) 1 →
      final.host = store.host →
      wp target rest Q final
        (readLocals capacity (FixedArrayAllocate.root heap.top (allocSize capacity) heap.free)
          errno length values) targetHost) :
    wp target (readAllocateCode ++ rest) Q store
      (readLocals capacity root errno length values) targetHost := by
  by_cases hNull : capacity = 0
  · subst capacity
    simp only [readAllocateCode, List.cons_append, List.nil_append, wp_localGet_cons,
      readLocals_capacity, wp_eqzI64_cons, ite_true, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
    simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append, List.drop_zero, readLocals_stack]
    refine wp_localSet_local (by change 1 ≤ 1; omega) (by change 1 < 4; omega) ?_
    simpa only [readLocals_values, readLocals_set_root, readLocals_stack] using hZero rfl
  · simp only [readAllocateCode, List.cons_append, List.nil_append, wp_localGet_cons,
      readLocals_capacity, wp_eqzI64_cons, ite_eq_right hNull, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide : ¬((0 : UInt32) ≠ 0))]
    simp only [wp_localGet_cons, readLocals_capacity, readLocals_values, readLocals_stack]
    refine wp_alloc_frame (s := readLocals capacity root errno length values) (values := values)
      runtime layout profile hImports sourceHost hHeap hCount hCap (hRoom hNull) ?_ ?_
    · intro hAbort final hWorld
      exact hTrap hAbort final hWorld
    · intro final hFits hStore hWorld
      simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
        List.nil_append, List.drop_zero, readLocals_stack]
      refine wp_localSet_local (by change 1 ≤ 1; omega) (by change 1 < 4; omega) ?_
      simpa only [readLocals_values, readLocals_set_root, readLocals_stack] using
        hAllocated hNull final hFits hStore hWorld

end Verified.Wasi
