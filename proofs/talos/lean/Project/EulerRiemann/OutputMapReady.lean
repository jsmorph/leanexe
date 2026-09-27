import Project.EulerRiemann.OutputMapLoop
import Project.ProofKit.FixedArrayFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayCopy FixedArrayResult

def outputMapReadyFrame (frame : Locals) (target : UInt64) (hCounter : frame.validIndex 39) : Locals :=
  counterFrame (resultFrame frame 38 target) 39 0
    (by simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hCounter)

theorem output_map_ready_get (frame : Locals) (target : UInt64) (hCounter : frame.validIndex 39)
    (hParams : frame.params.length = 5) (index : Nat) (h38 : index ≠ 38) (h39 : index ≠ 39) :
    (outputMapReadyFrame frame target hCounter).get index = frame.get index := by
  rw [outputMapReadyFrame, counterFrame_get_ne _ _ _ _ _ h39,
    resultFrame_get_ne frame 38 index target (by omega) h38]

theorem output_map_ready_target (frame : Locals) (target : UInt64) (hCounter : frame.validIndex 39)
    (hParams : frame.params.length = 5) :
    (outputMapReadyFrame frame target hCounter).get 38 = some (.i64 target) := by
  rw [outputMapReadyFrame, counterFrame_get_ne _ _ _ _ _ (by decide)]
  apply resultFrame_get_result frame 38 target (by omega)
  unfold Locals.validIndex at *
  omega

theorem output_map_ready_frame (pressure : Bool) (frame : Locals) (target : UInt64)
    (hCounter : frame.validIndex 39) (hParams : frame.params.length = 5)
    (hLocals : frame.locals.length = 52) :
    OutputMapFrameAt pressure (outputMapReadyFrame frame target hCounter) 0
      (outputMapReadyFrame frame target hCounter) := by
  apply OutputMapFrameAt.initial
  · simpa only [outputMapReadyFrame, counterFrame_params_length, resultFrame_params] using hParams
  · simpa only [outputMapReadyFrame, counterFrame_locals_length, resultFrame_locals_length] using hLocals
  · rfl
  · exact counterFrame_get_counter ..

theorem output_map_install_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (target count : UInt64) (hParams : frame.params.length = 5)
    (hLocals : frame.locals.length = 52) (hValues : frame.values = [])
    (hTarget : frame.get 47 = some (.i64 target))
    (hCount : frame.get 37 = some (.i64 count))
    (hBound : target.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (writeLength store target count) (resultFrame frame 38 target) env) :
    wp module ([.localGet 47, .localSet 38] ++ lengthStoreLocalProgram 38 37 ++ rest)
      Q store frame env := by
  change wp module (resultProgram 47 38 ++ lengthStoreLocalProgram 38 37 ++ rest) Q store frame env
  rw [List.append_assoc]
  apply resultProgram_spec 47 38 module env store frame target hValues hTarget
    (by omega) (by simp [Locals.validIndex, hParams, hLocals])
  apply lengthStoreLocal_spec module env store _ target count 38 37
  · exact resultFrame_get_result frame 38 target (by omega) (by simp [Locals.validIndex, hParams, hLocals])
  · exact (resultFrame_get_ne frame 38 37 target (by omega) (by decide)).trans hCount
  · exact hBound
  · exact hNext

#print axioms output_map_ready_get
#print axioms output_map_ready_target
#print axioms output_map_ready_frame
#print axioms output_map_install_spec

end Project.EulerRiemann.Execution
