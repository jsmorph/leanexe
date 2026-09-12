import Project.ProofKit.FixedArraySearchNone

namespace Project.ProofKit.FixedArraySearch
open Wasm Project.Runtime

theorem noneRegion_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (sourceBody fitProgram : Wasm.Program) (hBody : sourceBody = body start fitProgram)
    (need capacity next : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt initial.mem nodes) (hNone : takeFirstFit need nodes = none)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous capacity next : UInt64, wp module_ rest Q initial
      (frame params saved tail need previous 0 capacity next 0) env) :
    wp module_ ([.block 0 0 [.loop 0 0 sourceBody]] ++ rest) Q initial
      (frame params saved tail need 0 (freeHead nodes) capacity next 0) env := by
  subst sourceBody
  exact noneProgram_spec module_ env initial params saved tail start hStart fitProgram
    need capacity next nodes hList hNone Q rest hNext

#print axioms noneRegion_spec

end Project.ProofKit.FixedArraySearch
