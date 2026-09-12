import Project.EulerRiemann.InitialCopyPrefix
import Project.ProofKit.ArrayField

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def initialMapLoop : Wasm.Program :=
  (Annotation.resolve func88
    [{ instructionIndex := 4, field := .block },
     { instructionIndex := 0, field := .loop },
     { instructionIndex := 14, field := .elseBranch },
     { instructionIndex := 53, field := .block },
     { instructionIndex := 0, field := .loop }]).getD []

def initialLoadedFrame (frame : Locals) (cell : Traversal.Cell) : Locals :=
  let slots0 := frame.locals.set 6 (.i64 ((Memory.cellWords cell).getD 0 0))
  let slots1 := slots0.set 7 (.i64 ((Memory.cellWords cell).getD 1 0))
  let slots2 := slots1.set 8 (.i64 ((Memory.cellWords cell).getD 2 0))
  let slots3 := slots2.set 9 (.i64 ((Memory.cellWords cell).getD 3 0))
  let slots4 := slots3.set 10 (.i64 ((Memory.cellWords cell).getD 4 0))
  let slots5 := slots4.set 11 (.i64 ((Memory.cellWords cell).getD 5 0))
  let slots6 := slots5.set 12 (.i64 ((Memory.cellWords cell).getD 6 0))
  { frame with locals := slots6, values := [] }

theorem initial_map_load_shape : (initialMapLoop.drop 4).take 84 =
    ArrayField.loadProgram 48 51 7 0 ++ [.localSet 11] ++
    ArrayField.loadProgram 48 51 7 1 ++ [.localSet 12] ++
    ArrayField.loadProgram 48 51 7 2 ++ [.localSet 13] ++
    ArrayField.loadProgram 48 51 7 3 ++ [.localSet 14] ++
    ArrayField.loadProgram 48 51 7 4 ++ [.localSet 15] ++
    ArrayField.loadProgram 48 51 7 5 ++ [.localSet 16] ++
    ArrayField.loadProgram 48 51 7 6 ++ [.localSet 17] := by
  rfl

theorem initial_map_load_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source : UInt64) (grid : Array Traversal.Cell) (index : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = [])
    (hSource : frame.get 48 = some (.i64 source))
    (hIndex : frame.get 51 = some (.i64 (UInt64.ofNat index)))
    (hGrid : Memory.GridAt store source grid) (hi : index < grid.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialLoadedFrame frame grid[index]) env) :
    wp module ((initialMapLoop.drop 4).take 84 ++ rest) Q store frame env := by
  have hSourceRead := Frame.internal_getElem_of_get frame 5 43 (.i64 source)
    hParams (by omega) hSource
  have hIndexRead := Frame.internal_getElem_of_get frame 5 46 (.i64 (UInt64.ofNat index))
    hParams (by omega) hIndex
  rw [initial_map_load_shape]
  simp only [List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  iterate 7
    refine ArrayField.load_spec 48 51 7 _ module env store _ source _ index []
      ?_ ?_ ?_ (hGrid.fieldBound index _ hi ?_)
      (hGrid.fieldRead index _ hi ?_) Q _ ?_
    · first | exact hValues | rfl
    · simp [Locals.get, hParams, hLocals, hSourceRead]
    · simp [Locals.get, hParams, hLocals, hIndexRead]
    · decide
    · decide
    simp only [wp_localSet_cons]
    simp [Locals.set?, hParams, hLocals]
  simpa [initialLoadedFrame] using hNext

#print axioms initial_map_load_shape
#print axioms initial_map_load_spec

end Project.EulerRiemann.Execution
