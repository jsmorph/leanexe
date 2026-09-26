import Project.ProofKit.Control
import Project.ProofKit.Frame

namespace Project.ProofKit.RangeGuard
open Wasm

def program (indexLocal stopLocal : Nat) : Wasm.Program :=
  [.localGet indexLocal, .localGet stopLocal, .geUI64, .br_if 1]

theorem program_spec (indexLocal stopLocal : Nat) (module_ : Wasm.Module)
    (env : HostEnv α) (store : Store α) (frame : Locals) (index stop : UInt64)
    (hValues : frame.values = [])
    (hIndex : frame.get indexLocal = some (.i64 index))
    (hStop : frame.get stopLocal = some (.i64 stop))
    (Q : Assertion α) (rest : Wasm.Program)
    (hNext : if stop ≤ index then Q (.Break 1 store frame)
      else wp module_ rest Q store frame env) :
    wp module_ (program indexLocal stopLocal ++ rest) Q store frame env := by
  have hEmpty : ({ frame with values := [] } : Locals) = frame :=
    Frame.ext _ _ rfl rfl hValues.symm
  simp only [program, List.cons_append, List.nil_append, wp_localGet_cons,
    Frame.withValues_get, hValues, hIndex, hStop, wp_geUI64_cons, wp_br_if_cons]
  by_cases hGuard : stop ≤ index <;>
    simpa [hGuard, hEmpty] using hNext

#print axioms program_spec
end Project.ProofKit.RangeGuard
