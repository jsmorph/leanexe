import Project.TinyGpt2Checked.OutputCode
import Project.TinyGpt2Infer.OutputAllocateExec

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.Runtime Project.ProofKit ArrayPushLayout
open Project.TinyGpt2Infer

theorem output_allocation_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved tail : List Wasm.Value) (hStart : params.length + saved.length = 63)
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
      (TinyGpt2Infer.Spec.outputAllocationFrame params saved tail start count previous') env) :
    wp module ((outputBody.drop 69).take 15 ++ rest) Q initial
      (FixedArraySearch.frame params saved tail (UInt64.ofNat (capacity (count + 1)))
        previous current capacity' next result) env := by
  rw [output_allocation_shape]
  exact TinyGpt2Infer.Spec.output_allocation_program_spec module 63 rfl env initial params saved tail hStart start count
    allocations retains releases frees previous current capacity' next result
    hGlobals hList hFit hMemory hPages hCap Q rest hNext

#print axioms output_allocation_spec
end Project.TinyGpt2Checked.Spec
