import Project.EulerRiemann.InitialAllocationSearchShape
import Project.ProofKit.FixedArraySearchRegion

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime

theorem initial_search_none_spec (site : InitialAllocationSite)
    (env : HostEnv Unit) (store : Store Unit) (params saved tail : List Wasm.Value)
    (hStart : params.length + saved.length = site.capacityLocal)
    (need capacity next : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes) (hNone : takeFirstFit need nodes = none)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous capacity next : UInt64, wp module rest Q store
      (FixedArraySearch.frame params saved tail need previous 0 capacity next 0) env) :
    wp module ([.block 0 0 [.loop 0 0 site.searchBody]] ++ rest) Q store
      (FixedArraySearch.frame params saved tail need 0 (freeHead nodes) capacity next 0) env := by
  exact FixedArraySearch.noneRegion_spec module env store params saved tail
    site.capacityLocal hStart site.searchBody site.fitProgram (initial_search_body site)
    need capacity next nodes hList hNone Q rest hNext

#print axioms initial_search_none_spec

end Project.EulerRiemann.Execution
