import Project.EulerRiemann.AllocationSearchRead

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def searchGuard : Wasm.Program :=
  [.localGet 49, .constI64 0, .eqI64, .br_if 1,
    .localGet 52, .constI64 0, .neI64, .br_if 1]

theorem sweep_search_parts : sweepSearch = searchGuard ++ searchRead ++
    [.localGet 50, .localGet 47, .geUI64, .iff 0 0 sweepFit searchAdvance, .br 0] := rfl

theorem searchGuard_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (root : UInt64)
    (hValues : frame.values = []) (hRoot : root ≠ 0)
    (hCurrent : frame.get 49 = some (.i64 root))
    (hResult : frame.get 52 = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store frame env) :
    wp module_ (searchGuard ++ rest) Q store frame env := by
  have hEmpty : { frame with values := [] } = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [searchGuard, List.cons_append, List.nil_append, wp_localGet_cons,
    wp_constI64_cons, wp_eqI64_cons, wp_neI64_cons, wp_br_if_cons,
    Frame.withValues_get, hCurrent, hResult, hValues, hRoot, reduceIte]
  simpa [hEmpty] using hNext

#print axioms sweep_search_parts
#print axioms searchGuard_spec

end Project.EulerRiemann.Execution
