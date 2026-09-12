import Project.ProofKit.FixedArrayCopy
import Project.ProofKit.FixedArrayFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayCopy

def initialMapReadyFrame (frame : Locals) (target : UInt64) (hCounter : frame.validIndex 51) : Locals :=
  counterFrame (resultFrame frame 50 target) 51 0
    (by simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hCounter)

theorem initial_map_ready_get (frame : Locals) (target : UInt64) (hCounter : frame.validIndex 51)
    (hParams : frame.params.length = 5) (index : Nat) (h50 : index ≠ 50) (h51 : index ≠ 51) :
    (initialMapReadyFrame frame target hCounter).get index = frame.get index := by
  rw [initialMapReadyFrame, counterFrame_get_ne _ _ _ _ _ h51,
    resultFrame_get_ne frame 50 index target (by omega) h50]

theorem initial_map_ready_target (frame : Locals) (target : UInt64) (hCounter : frame.validIndex 51)
    (hParams : frame.params.length = 5) :
    (initialMapReadyFrame frame target hCounter).get 50 = some (.i64 target) := by
  rw [initialMapReadyFrame, counterFrame_get_ne _ _ _ _ _ (by decide)]
  apply resultFrame_get_result frame 50 target (by omega)
  unfold Locals.validIndex at *
  omega

#print axioms initial_map_ready_get
#print axioms initial_map_ready_target

end Project.EulerRiemann.Execution
