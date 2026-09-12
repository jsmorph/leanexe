import Project.EulerRiemann.InitialMapCall
import Project.EulerRiemann.InitialMapStore

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

@[simp] theorem initialLoadedFrame_params (frame : Locals) (cell : Traversal.Cell) :
    (initialLoadedFrame frame cell).params = frame.params := rfl

@[simp] theorem initialLoadedFrame_length (frame : Locals) (cell : Traversal.Cell) :
    (initialLoadedFrame frame cell).locals.length = frame.locals.length := by
  simp only [initialLoadedFrame, List.length_set]

@[simp] theorem initialLoadedFrame_values (frame : Locals) (cell : Traversal.Cell) :
    (initialLoadedFrame frame cell).values = [] := rfl

@[simp] theorem initialCalledFrame_params (frame : Locals) (n index offset : Nat) :
    (initialCalledFrame frame n index offset).params = frame.params := by
  simp only [initialCalledFrame, initialCallResultFrame, initialCallSetupFrame]

@[simp] theorem initialCalledFrame_length (frame : Locals) (n index offset : Nat) :
    (initialCalledFrame frame n index offset).locals.length = frame.locals.length := by
  simp only [initialCalledFrame, initialCallResultFrame, initialCallSetupFrame, List.length_set]

@[simp] theorem initialCalledFrame_values (frame : Locals) (n index offset : Nat) :
    (initialCalledFrame frame n index offset).values = [] := rfl

theorem initial_loaded_get_other (frame : Locals) (cell : Traversal.Cell) (index : Nat)
    (hParams : frame.params.length = 5) (hOther : index < 11 ∨ 17 < index) :
    (initialLoadedFrame frame cell).get index = frame.get index := by
  simp only [initialLoadedFrame, Locals.get, List.length_set, hParams]
  split_ifs with hp hl
  · rfl
  · repeat rw [List.getElem?_set_ne (by omega)]
  · rfl

theorem initial_call_setup_get_other (frame : Locals) (n cellIndex offset index : Nat)
    (hParams : frame.params.length = 5)
    (hLow : index < 18 ∨ 19 < index) (hHigh : index < 54 ∨ 56 < index) :
    (initialCallSetupFrame frame n cellIndex offset).get index = frame.get index := by
  simp only [initialCallSetupFrame, Locals.get, List.length_set, hParams]
  split_ifs with hp hl
  · rfl
  · repeat rw [List.getElem?_set_ne (by omega)]
  · rfl

theorem initial_call_result_get_other (frame : Locals) (cell : Traversal.Cell) (index : Nat)
    (hParams : frame.params.length = 5) (hOther : index < 20 ∨ 33 < index) :
    (initialCallResultFrame frame cell).get index = frame.get index := by
  simp only [initialCallResultFrame, Locals.get, List.length_set, hParams]
  split_ifs with hp hl
  · rfl
  · repeat rw [List.getElem?_set_ne (by omega)]
  · rfl

theorem initial_called_get_other (frame : Locals) (n cellIndex offset index : Nat)
    (hParams : frame.params.length = 5)
    (hLow : index < 18 ∨ 33 < index) (hHigh : index < 54 ∨ 56 < index) :
    (initialCalledFrame frame n cellIndex offset).get index = frame.get index := by
  unfold initialCalledFrame
  rw [initial_call_result_get_other (initialCallSetupFrame frame n cellIndex offset)
    _ _ (by simpa only [initialCallSetupFrame] using hParams) (by omega)]
  exact initial_call_setup_get_other _ _ _ _ _ hParams (by omega) hHigh

theorem initial_loaded_index (frame : Locals) (cell : Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    (initialLoadedFrame frame cell).get 11 = some (.i64 (UInt64.ofNat cell.index)) := by
  simp [initialLoadedFrame, Locals.get, hParams, hLocals, Memory.cellWords, Array.getD]

theorem initial_called_data (frame : Locals) (n index offset field : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hf : field < 7) :
    (initialCalledFrame frame n index offset).get (27 + field) =
      some (.i64 ((Memory.cellWords (Traversal.initialCell n (index + offset))).getD field 0)) := by
  interval_cases field <;>
    simp [initialCalledFrame, initialCallResultFrame, initialCallSetupFrame,
      Locals.get, hParams, hLocals]

def initialMappedFrame (frame : Locals) (n offset : Nat) (cell : Traversal.Cell) : Locals :=
  initialCalledFrame (initialLoadedFrame frame cell) n cell.index offset

theorem initial_mapped_get_other (frame : Locals) (n offset : Nat) (cell : Traversal.Cell)
    (index : Nat) (hParams : frame.params.length = 5)
    (hLow : index < 11 ∨ 33 < index) (hHigh : index < 54 ∨ 56 < index) :
    (initialMappedFrame frame n offset cell).get index = frame.get index := by
  rw [initialMappedFrame, initial_called_get_other (initialLoadedFrame frame cell)
    _ _ _ _ (by simpa using hParams) (by omega) hHigh,
    initial_loaded_get_other _ _ _ hParams (by omega)]

#print axioms initial_loaded_get_other
#print axioms initial_called_get_other
#print axioms initial_loaded_index
#print axioms initial_called_data
#print axioms initial_mapped_get_other

end Project.EulerRiemann.Execution
