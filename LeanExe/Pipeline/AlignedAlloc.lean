import LeanExe.Pipeline.RuntimeSpec
import LeanExe.Pipeline.AlignedHeap
import LeanExe.Pipeline.AlignedRuns
import LeanExe.ProofKit.AlignedAllocate

/-!
`alloc` under `wpA`.  `alloc_spec_runsA` is `alloc_spec_runs` with `RunsA` for `Runs`: from an
aligned heap, the run of `alloc` makes only aligned 64-bit accesses inside memory.  The request
`allocSize bytes` is a multiple of 8, and `Heap.Aligned` gives the alignment of `top` and of the
roots and capacities of the free blocks that the allocation's ports take as premises.
-/

namespace LeanExe.Pipeline

open Wasm LeanExe.Runtime LeanExe.ProofKit

/-- `array_allocation_spec_runs` under `wpA`, from an aligned heap and a request that is a
multiple of 8. -/
theorem array_allocation_spec_runsA (aborts : Bool) (m : Wasm.Module)
    (hMemory32 : m.memIs64 = false) (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (need stride previous current capacity next result : UInt64) (hHeap : heap.At store)
    (hAligned : heap.Aligned) (hNeedAl : need.toNat % 8 = 0)
    (hNeed : need.toNat ≤ 4294967296) (hCap : store.memoryCap m 0 ≤ 65535)
    (Q : Assertion Unit) (rest : Wasm.Program) (hTrap : TrapOK aborts Q)
    (hRoom : aborts = false → heap.Room store m need)
    (hNext : heap.Fits need → ∀ previous current capacity next : UInt64,
      wpA m rest Q (heap.allocateStore store need stride)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (FixedArrayAllocate.root heap.top need heap.free)) env) :
    wpA m (FixedArrayAllocate.program start stride ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result)
      env := by
  have hTop := hHeap.top
  have hPages := hHeap.pages
  exact FixedArrayAllocate.program_spec_runsA aborts m env store params saved tail start hStart
    heap.top need stride previous current capacity next result heap.allocs heap.free
    (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
    hHeap.freeList (by omega) hNeed hHeap.pages hMemory32 hCap hAligned.top hAligned.roots
    hAligned.capacities hNeedAl Q rest (fun h => by subst h; exact hTrap) hRoom hNext

/-- `alloc_spec_runs` with `RunsA`: from an aligned heap, every 64-bit access of `alloc` inside
memory is aligned. -/
theorem alloc_spec_runsA (aborts : Bool) {m : Module} {typeIdx : Nat}
    (hMemory32 : m.memIs64 = false)
    (hImports : m.imports = []) (hFunc : m.funcs[0]? = some (allocFunction typeIdx))
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (bytes : UInt64)
    (hHeap : heap.At store) (hAligned : heap.Aligned) (hBytes : bytes.toNat ≤ 4294967296)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hRoom : aborts = false → heap.Room store m (allocSize bytes)) :
    RunsA aborts env m 0 store [.i64 bytes] fun final out =>
      heap.Fits (allocSize bytes) ∧ final = heap.allocateStore store (allocSize bytes) 1 ∧
      out = [.i64 (FixedArrayAllocate.root heap.top (allocSize bytes) heap.free)] := by
  refine RunsA.of_wpA_entry_for (f := allocFunction typeIdx)
    (by simpa [hImports] using hFunc) ?_ (by simp [hImports])
  have hSizeBound := allocSize_le hBytes
  simp [allocFunction, allocBody, Function.toLocals, Function.numParams, wpA_simp, wp_simp]
  refine wpA_iff_cons rfl ?_
  by_cases hSmall : (bytes + 7) / 8 * 8 < 8
  · have hSize : allocSize bytes = 8 := by simp [allocSize, hSmall]
    simp [hSmall, wpA_simp, wp_simp]
    show wpA m _ _ store (FixedArraySearch.frame [.i64 bytes] [] [] 8 0 0 0 0 0) env
    rw [← hSize]
    exact array_allocation_spec_runsA aborts m hMemory32 env store heap [.i64 bytes] [] [] 1 rfl
      (allocSize bytes) 1 0 0 0 0 0 hHeap hAligned (allocSize_mod8 bytes) hSizeBound hCap _ _
      (by cases aborts <;> simp [TrapOK, TrapMsg]) hRoom
      fun hFits _ _ _ _ => by simp [FixedArraySearch.frame, wpA_simp, wp_simp, hFits]
  · have hSize : allocSize bytes = (bytes + 7) / 8 * 8 := by simp [allocSize, hSmall]
    simp [hSmall, wpA_simp, wp_simp]
    show wpA m _ _ store
      (FixedArraySearch.frame [.i64 bytes] [] [] ((bytes + 7) / 8 * 8) 0 0 0 0 0) env
    rw [← hSize]
    exact array_allocation_spec_runsA aborts m hMemory32 env store heap [.i64 bytes] [] [] 1 rfl
      (allocSize bytes) 1 0 0 0 0 0 hHeap hAligned (allocSize_mod8 bytes) hSizeBound hCap _ _
      (by cases aborts <;> simp [TrapOK, TrapMsg]) hRoom
      fun hFits _ _ _ _ => by simp [FixedArraySearch.frame, wpA_simp, wp_simp, hFits]

end LeanExe.Pipeline
