import Project.EulerRiemann.InitialMapReadyFrame
import Project.EulerRiemann.InitialMapCursor

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayCopy

theorem initial_map_ready_frame (frame : Locals) (target : UInt64) (hCounter : frame.validIndex 51)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    InitialMapFrameAt (initialMapReadyFrame frame target hCounter) 0
      (initialMapReadyFrame frame target hCounter) := by
  apply InitialMapFrameAt.initial
  · simpa only [initialMapReadyFrame, counterFrame_params_length, resultFrame_params] using hParams
  · simpa only [initialMapReadyFrame, counterFrame_locals_length, resultFrame_locals_length] using hLocals
  · rfl
  · exact counterFrame_get_counter ..

#print axioms initial_map_ready_frame

end Project.EulerRiemann.Execution
