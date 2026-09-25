import Project.TinyGpt2Infer.OutputCode
import Project.TinyGpt2Infer.OutputAllocation

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.Runtime Project.ProofKit ArrayPushLayout

def outputAllocationFrame (params saved tail : List Wasm.Value) (start count : Nat)
    (previous : UInt64) : Locals :=
  FixedArraySearch.frame params saved tail (UInt64.ofNat (capacity (count + 1))) previous 0
    (UInt64.ofNat (top start (count + 1)))
    ((UInt64.ofNat (top start (count + 1)) - 1) / 65536 + 1) (node start (count + 1)).root

theorem output_allocation_program_spec (module_ : Wasm.Module) (scratch : Nat)
    (hMemory32 : module_.memIs64 = false) (env : HostEnv Unit) (initial : Store Unit)
    (params saved tail : List Wasm.Value) (hStart : params.length + saved.length = scratch)
    (start count : Nat) (allocations retains releases frees previous current capacity' next result : UInt64)
    (hGlobals : initial.globals.globals = OutputMemory.globals start count allocations retains releases frees)
    (hList : FreeListAt initial.mem (freed start count))
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module_ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous' : UInt64, wp module_ rest Q
      (OutputMemory.allocate initial start (count + 1) allocations)
      (outputAllocationFrame params saved tail start count previous') env) :
    wp module_ (FixedArrayAllocate.program scratch 1 ++ rest) Q initial
      (FixedArraySearch.frame params saved tail (UInt64.ofNat (capacity (count + 1)))
        previous current capacity' next result) env := by
  have hWords := OutputMemory.allocation_words start (count + 1) hFit
  have hPagesNeeded : FixedArrayBump.requiredPages (UInt64.ofNat (base start (count + 1)))
      (UInt64.ofNat (capacity (count + 1))) ≤ initial.mem.pages := by
    unfold FixedArrayBump.requiredPages
    rw [hWords.1, hWords.2]
    unfold top root at hMemory
    omega
  apply FixedArrayAllocateNone.program_spec module_ env initial params saved tail scratch hStart
    (FixedArrayReuse.program scratch 1) (UInt64.ofNat (base start (count + 1)))
    (UInt64.ofNat (capacity (count + 1))) 1 previous current capacity' next result allocations
    (freed start count)
  · simp only [hGlobals, OutputMemory.globals, List.getElem?_cons_zero]
    rw [top_eq_next_base]
  · simp [hGlobals, OutputMemory.globals]
  · simp [hGlobals, OutputMemory.globals]
  · exact hList
  · exact no_fit start count (count + 1) (by omega) hFit
  · rw [hWords.1, hWords.2]
    exact hFit.le
  · exact hPages
  · exact hMemory32
  · exact hPagesNeeded.trans hCap
  · intro previous'
    rw [OutputMemory.allocation_top_word, OutputMemory.allocation_root_word]
    exact hNext previous'

theorem output_allocation_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved tail : List Wasm.Value) (hStart : params.length + saved.length = 60)
    (start count : Nat) (allocations retains releases frees previous current capacity' next result : UInt64)
    (hGlobals : initial.globals.globals = OutputMemory.globals start count allocations retains releases frees)
    (hList : FreeListAt initial.mem (freed start count))
    (hFit : top start (count + 1) < 4294967296)
    (hMemory : top start (count + 1) ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous' : UInt64, wp module rest Q
      (OutputMemory.allocate initial start (count + 1) allocations)
      (outputAllocationFrame params saved tail start count previous') env) :
    wp module ((outputBody.drop 67).take 15 ++ rest) Q initial
      (FixedArraySearch.frame params saved tail (UInt64.ofNat (capacity (count + 1)))
        previous current capacity' next result) env := by
  rw [output_allocation_shape]
  exact output_allocation_program_spec module 60 rfl env initial params saved tail hStart start count
    allocations retains releases frees previous current capacity' next result
    hGlobals hList hFit hMemory hPages hCap Q rest hNext

#print axioms output_allocation_program_spec
#print axioms output_allocation_spec
end Project.TinyGpt2Infer.Spec
