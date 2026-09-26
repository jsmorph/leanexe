import Project.EulerRiemann.FrozenOutputMapPrepare

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit FixedArrayFold

def outputMapOwnerLocal (pressure : Bool) : Nat := if pressure then 23 else 13

def outputMapReturnProgram (pressure : Bool) : Wasm.Program :=
  resultProgram 38 (outputMapOwnerLocal pressure) ++
    resultProgram (outputMapOwnerLocal pressure) (outputMapOwnerLocal pressure + 1)

def outputMapReturnedFrame (pressure : Bool) (frame : Locals) (root : UInt64) : Locals :=
  resultFrame (resultFrame frame (outputMapOwnerLocal pressure) root) (outputMapOwnerLocal pressure + 1) root

theorem output_map_return_bounds (pressure : Bool) :
    5 ≤ outputMapOwnerLocal pressure ∧ outputMapOwnerLocal pressure + 1 < 36 := by
  cases pressure <;> decide

theorem output_map_return_gets (pressure : Bool) (frame : Locals) (root : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52) :
    (outputMapReturnedFrame pressure frame root).get (outputMapOwnerLocal pressure) = some (.i64 root) ∧
    (outputMapReturnedFrame pressure frame root).get (outputMapOwnerLocal pressure + 1) = some (.i64 root) := by
  have hBounds := output_map_return_bounds pressure
  constructor
  · rw [outputMapReturnedFrame, resultFrame_get_ne _ _ _ _
      (by change frame.params.length ≤ outputMapOwnerLocal pressure + 1; omega) (by omega)]
    apply resultFrame_get_result <;> simp only [Locals.validIndex, hParams, hLocals] <;> omega
  · apply resultFrame_get_result
    · change frame.params.length ≤ outputMapOwnerLocal pressure + 1
      omega
    · simp only [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]
      omega

theorem output_map_return_get_other (pressure : Bool) (frame : Locals) (root : UInt64) (index : Nat)
    (hParams : frame.params.length = 5)
    (hOwner : index ≠ outputMapOwnerLocal pressure) (hPointer : index ≠ outputMapOwnerLocal pressure + 1) :
    (outputMapReturnedFrame pressure frame root).get index = frame.get index := by
  have hBounds := output_map_return_bounds pressure
  rw [outputMapReturnedFrame, resultFrame_get_ne _ _ _ _
      (by change frame.params.length ≤ outputMapOwnerLocal pressure + 1; omega) hPointer,
    resultFrame_get_ne _ _ _ _ (by omega) hOwner]

theorem output_map_return_scratch (pressure : Bool) (frame : Locals) (root : UInt64)
    (hParams : frame.params.length = 5) (hScratch : I64LocalRange frame 42 57) :
    I64LocalRange (outputMapReturnedFrame pressure frame root) 42 57 := by
  apply hScratch.of_preserved
  intro index hFirst hLast
  have hBounds := output_map_return_bounds pressure
  exact output_map_return_get_other pressure frame root index hParams (by omega) (by omega)

theorem output_map_return_spec (pressure : Bool) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (root : UInt64) (hParams : frame.params.length = 5)
    (hLocals : frame.locals.length = 52) (hValues : frame.values = [])
    (hRoot : frame.get 38 = some (.i64 root)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (outputMapReturnedFrame pressure frame root) env) :
    wp module (outputMapReturnProgram pressure ++ rest) Q store frame env := by
  have hBounds := output_map_return_bounds pressure
  have hValid : frame.validIndex (outputMapOwnerLocal pressure) := by
    simp only [Locals.validIndex, hParams, hLocals]
    omega
  rw [outputMapReturnProgram, List.append_assoc]
  apply resultProgram_spec 38 (outputMapOwnerLocal pressure) module env store frame root hValues hRoot
    (by omega) hValid
  apply resultProgram_spec (outputMapOwnerLocal pressure) (outputMapOwnerLocal pressure + 1)
    module env store (resultFrame frame (outputMapOwnerLocal pressure) root) root rfl
    (resultFrame_get_result frame _ root (by omega) hValid)
    (by change frame.params.length ≤ outputMapOwnerLocal pressure + 1; omega)
    (by simp only [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]; omega)
  exact hNext

#print axioms output_map_return_gets
#print axioms output_map_return_get_other
#print axioms output_map_return_scratch
#print axioms output_map_return_spec

end Project.EulerRiemann.Frozen.Execution
