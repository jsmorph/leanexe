import Project.EulerRiemann.FrozenOutputShape
import Project.EulerRiemann.FrozenMemory

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit

def outputItemStart (pressure : Bool) : Nat := if pressure then 15 else 5

def outputLoadedFrame (pressure : Bool) (frame : Locals) (cell : Traversal.Cell) : Locals :=
  let start := if pressure then 10 else 0
  let slots0 := frame.locals.set start (.i64 ((Memory.cellWords cell).getD 0 0))
  let slots1 := slots0.set (start + 1) (.i64 ((Memory.cellWords cell).getD 1 0))
  let slots2 := slots1.set (start + 2) (.i64 ((Memory.cellWords cell).getD 2 0))
  let slots3 := slots2.set (start + 3) (.i64 ((Memory.cellWords cell).getD 3 0))
  let slots4 := slots3.set (start + 4) (.i64 ((Memory.cellWords cell).getD 4 0))
  let slots5 := slots4.set (start + 5) (.i64 ((Memory.cellWords cell).getD 5 0))
  let slots6 := slots5.set (start + 6) (.i64 ((Memory.cellWords cell).getD 6 0))
  { frame with locals := slots6, values := [] }

def outputCellWord (pressure : Bool) (cell : Traversal.Cell) : UInt64 :=
  if pressure then cell.pressure else cell.state.density

theorem output_loads_shape (start : Nat) : outputMapLoads start =
    ArrayField.loadProgram 36 39 7 0 ++ [.localSet start] ++
    ArrayField.loadProgram 36 39 7 1 ++ [.localSet (start + 1)] ++
    ArrayField.loadProgram 36 39 7 2 ++ [.localSet (start + 2)] ++
    ArrayField.loadProgram 36 39 7 3 ++ [.localSet (start + 3)] ++
    ArrayField.loadProgram 36 39 7 4 ++ [.localSet (start + 4)] ++
    ArrayField.loadProgram 36 39 7 5 ++ [.localSet (start + 5)] ++
    ArrayField.loadProgram 36 39 7 6 ++ [.localSet (start + 6)] := rfl

theorem output_map_load_spec (pressure : Bool) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (source : UInt64)
    (grid : Array Traversal.Cell) (index : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = [])
    (hSource : frame.get 36 = some (.i64 source))
    (hIndex : frame.get 39 = some (.i64 (UInt64.ofNat index)))
    (hGrid : Memory.GridAt store source grid) (hi : index < grid.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (outputLoadedFrame pressure frame grid[index]) env) :
    wp module (outputMapLoads (outputItemStart pressure) ++ rest) Q store frame env := by
  have hSourceRead := Frame.internal_getElem_of_get frame 5 31 (.i64 source)
    hParams (by omega) hSource
  have hIndexRead := Frame.internal_getElem_of_get frame 5 34 (.i64 (UInt64.ofNat index))
    hParams (by omega) hIndex
  cases pressure <;> rw [output_loads_shape] <;>
    simp only [outputItemStart, Bool.false_eq_true, ite_false, ite_true,
      Nat.reduceAdd, List.append_assoc, List.cons_append, List.nil_append]
  all_goals
    iterate 7
      refine ArrayField.load_spec 36 39 7 _ module env store _ source _ index []
        ?_ ?_ ?_ (hGrid.fieldBound index _ hi ?_)
        (hGrid.fieldRead index _ hi ?_) Q _ ?_
      · first | exact hValues | rfl
      · simp [Locals.get, hParams, hLocals, hSourceRead]
      · simp [Locals.get, hParams, hLocals, hIndexRead]
      · decide
      · decide
      simp only [wp_localSet_cons]
      simp [Locals.set?, hParams, hLocals]
    simpa [outputLoadedFrame] using hNext

@[simp] theorem outputLoadedFrame_params (pressure : Bool) (frame : Locals)
    (cell : Traversal.Cell) : (outputLoadedFrame pressure frame cell).params = frame.params := rfl

@[simp] theorem outputLoadedFrame_length (pressure : Bool) (frame : Locals)
    (cell : Traversal.Cell) :
    (outputLoadedFrame pressure frame cell).locals.length = frame.locals.length := by
  simp only [outputLoadedFrame, List.length_set]

theorem output_loaded_get_other (pressure : Bool) (frame : Locals)
    (cell : Traversal.Cell) (index : Nat) (hParams : frame.params.length = 5)
    (hOther : index < outputItemStart pressure ∨ outputItemStart pressure + 7 ≤ index) :
    (outputLoadedFrame pressure frame cell).get index = frame.get index := by
  cases pressure <;> simp only [outputItemStart, Bool.false_eq_true, ite_false, ite_true] at hOther ⊢
  all_goals
    simp only [outputLoadedFrame, Bool.false_eq_true, ite_false, ite_true,
      Nat.reduceAdd, Locals.get, List.length_set, hParams]
    split_ifs with hp hl
    · rfl
    · repeat rw [List.getElem?_set_ne (by omega)]
    · rfl

theorem output_loaded_word (pressure : Bool) (frame : Locals) (cell : Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52) :
    (outputLoadedFrame pressure frame cell).get (if pressure then 20 else 6) =
      some (.i64 (outputCellWord pressure cell)) := by
  cases pressure <;>
    simp [outputLoadedFrame, outputCellWord, Locals.get, hParams, hLocals,
      Memory.cellWords, Array.getD]

#print axioms output_loads_shape
#print axioms output_map_load_spec
#print axioms output_loaded_get_other
#print axioms output_loaded_word

end Project.EulerRiemann.Frozen.Execution
