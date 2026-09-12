import Project.ProofKit.Control
import Project.ProofKit.Frame

namespace Project.ProofKit.FuelGuard
open Wasm

def program (fuelLocal doneLocal : Nat) : Wasm.Program :=
  [.localGet fuelLocal, .constI64 0, .eqI64, .eqz,
    .iff 0 1 [.localGet doneLocal, .constI64 0, .eqI64]
      [.const 0] [] [.i32],
    .eqz, .br_if 1]

theorem program_spec (fuelLocal doneLocal : Nat) (module_ : Wasm.Module)
    (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (fuel done : UInt64)
    (hValues : frame.values = [])
    (hFuel : frame.get fuelLocal = some (.i64 fuel))
    (hDone : frame.get doneLocal = some (.i64 done))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : if fuel = 0 ∨ done ≠ 0 then Q (.Break 1 store frame)
      else wp module_ rest Q store frame env) :
    wp module_ (program fuelLocal doneLocal ++ rest) Q store frame env := by
  have hEmpty : ({ frame with values := [] } : Locals) = frame :=
    Frame.ext _ _ rfl rfl hValues.symm
  unfold program
  by_cases hZero : fuel = 0 <;> by_cases hComplete : done = 0 <;>
    simp only [List.cons_append, List.nil_append, wp_simp,
      hFuel, hValues, hZero] <;>
    refine wp_iff_cons rfl ?_ <;>
    simp_all [wp_simp]

#print axioms program_spec

theorem zeroFuel_spec (fuelLocal doneLocal : Nat) (module_ : Wasm.Module)
    (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hValues : frame.values = [])
    (hFuel : frame.get fuelLocal = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : Q (.Break 1 store frame)) :
    wp module_ (program fuelLocal doneLocal ++ rest) Q store frame env := by
  have hEmpty : ({ frame with values := [] } : Locals) = frame :=
    Frame.ext _ _ rfl rfl hValues.symm
  unfold program
  simp only [List.cons_append, List.nil_append, wp_simp, hFuel, hValues]
  refine wp_iff_cons rfl ?_
  simpa [wp_simp, hValues, hEmpty] using hNext

#print axioms zeroFuel_spec

end Project.ProofKit.FuelGuard
