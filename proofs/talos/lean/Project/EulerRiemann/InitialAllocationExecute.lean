import Project.EulerRiemann.InitialAllocationShape

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime

theorem initial_allocation_none_spec (site : InitialAllocationSite)
    (env : HostEnv Unit) (store : Store Unit) (params saved tail : List Wasm.Value)
    (hStart : params.length + saved.length = site.capacityLocal)
    (base need previous current capacity next result count : UInt64) (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes) (hNone : takeFirstFit need nodes = none)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages base need ≤ store.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous : UInt64, wp module rest Q
      (FixedArrayAllocateNone.counted (FixedArrayBump.allocated store base need 7) count)
      (FixedArraySearch.frame params saved tail need previous 0 (base + 48 + need)
        ((base + 48 + need - 1) / 65536 + 1) (base + 48)) env) :
    wp module (site.allocationProgram ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  exact (congrArg (fun code : Wasm.Program => wp module (code ++ rest) Q store
    (FixedArraySearch.frame params saved tail need previous current capacity next result) env)
      (initial_allocation_shape site)).mpr
    (FixedArrayAllocateNone.program_spec module env store params saved tail site.capacityLocal hStart
      site.fitProgram base need 7 previous current capacity next result count nodes
      hGlobal0 hGlobal1 hGlobal2 hList hNone hFit32 hPages rfl hCap Q rest hNext)

#print axioms initial_allocation_none_spec

end Project.EulerRiemann.Execution
