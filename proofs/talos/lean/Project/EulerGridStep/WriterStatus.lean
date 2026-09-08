import Project.EulerGridStep.WriterReleases

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The emitted status test, isolated from either large writer branch. -/
def writerStatusPrefix : Wasm.Program :=
  [.localGet 3, .constI64 0, .eqI64,
    .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
    .constI64 1, .eqI64,
    .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
    .constI64 0, .eqI64, .eqz]

theorem writer_status_shape : func34.take 10 = writerStatusPrefix := rfl

/-- The status prefix preserves memory and locals and produces the exact branch condition. -/
theorem writer_status_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (status : UInt64)
    (hGet : frame.get 3 = some (.i64 status)) (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial
      { frame with values := [.i32 (if status = 0 then 1 else 0)] } env) :
    wp m (writerStatusPrefix ++ rest) Q initial frame env := by
  simp only [writerStatusPrefix, List.cons_append, List.nil_append, wp_localGet_cons, hGet, hValues]
  by_cases hStatus : status = 0
  all_goals
    repeat first
      | wp_run [writerStatusPrefix, hGet, hValues, hStatus]
      | simp [hStatus, hGet, hValues]
      | refine wp_iff_cons rfl ?_
        simp [hStatus, hGet, hValues]
    simpa [hStatus, copyFrame_ofParts frame hValues] using hNext

#print axioms writer_status_shape
#print axioms writer_status_spec
end Project.EulerGridStep.Execution
