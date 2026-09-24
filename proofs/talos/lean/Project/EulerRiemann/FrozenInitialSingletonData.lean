import Project.EulerRiemann.FrozenInitialSingletonStore
import Project.EulerRiemann.FrozenInitialSingletonMemory

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult

def initialSingletonStageFrame (frame : Locals) (cell : Traversal.Cell) : Locals :=
  let locals := frame.locals.set 23 (.i64 (UInt64.ofNat cell.index))
  let locals := locals.set 24 (.i64 cell.state.density)
  let locals := locals.set 25 (.i64 cell.state.mx)
  let locals := locals.set 26 (.i64 cell.state.my)
  let locals := locals.set 27 (.i64 cell.state.energy)
  let locals := locals.set 28 (.i64 cell.pressure)
  let locals := locals.set 29 (.i64 cell.status)
  { frame with locals := locals, values := [] }

def initialSingletonDataFrame (frame : Locals) (root : UInt64) (cell : Traversal.Cell) : Locals :=
  initialSingletonStageFrame (resultFrame frame 21 root) cell

theorem initial_singleton_stage_shape : (initialCellsBody.drop 66).take 14 =
    [.localGet 6, .localSet 24, .localGet 7, .localSet 25, .localGet 8, .localSet 26,
      .localGet 9, .localSet 27, .localGet 10, .localSet 28, .localGet 11, .localSet 29,
      .localGet 12, .localSet 30] := rfl

theorem initial_singleton_data_shape : (initialCellsBody.drop 60).take 104 =
    resultProgram 36 21 ++ lengthStoreProgram 21 1 ++ (initialCellsBody.drop 66).take 14 ++
      (initialCellsBody.drop 80).take 84 := rfl

theorem initial_singleton_stage_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (cell : Traversal.Cell) (hParams : frame.params.length = 1) (hLocals : frame.locals.length = 36)
    (hValues : frame.values = [])
    (hData : ∀ field : Nat, field < 7 →
      frame.get (6 + field) = some (.i64 ((Memory.cellWords cell).getD field 0)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialSingletonStageFrame frame cell) env) :
    wp module ((initialCellsBody.drop 66).take 14 ++ rest) Q store frame env := by
  have hReads (field : Nat) (hf : field < 7) :
      frame.locals[5 + field]? = some (.i64 ((Memory.cellWords cell).getD field 0)) :=
    Frame.internal_getElem?_of_get frame 1 (5 + field) _ hParams (by omega)
      (by simpa only [← Nat.add_assoc, Nat.reduceAdd] using hData field hf)
  rw [initial_singleton_stage_shape]
  wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, reduceIte,
    hParams, hLocals, hValues, hReads 0 (by decide), hReads 1 (by decide), hReads 2 (by decide),
    hReads 3 (by decide), hReads 4 (by decide), hReads 5 (by decide), hReads 6 (by decide)]
  simpa [initialSingletonStageFrame, Memory.cellWords, Array.getD] using hNext

theorem initial_singleton_data_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (root : UInt64) (cell : Traversal.Cell)
    (hParams : frame.params.length = 1) (hLocals : frame.locals.length = 36) (hValues : frame.values = [])
    (hRoot : frame.get 36 = some (.i64 root))
    (hData : ∀ field : Nat, field < 7 →
      frame.get (6 + field) = some (.i64 ((Memory.cellWords cell).getD field 0)))
    (hFit32 : root.toNat + 64 ≤ 4294967296) (hFitMemory : root.toNat + 64 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : Memory.GridAt (initialSingletonStore store root cell) root #[cell] →
      Memory.WritesGrid store (initialSingletonStore store root cell) root 1 →
      wp module rest Q (initialSingletonStore store root cell) (initialSingletonDataFrame frame root cell) env) :
    wp module ((initialCellsBody.drop 60).take 104 ++ rest) Q store frame env := by
  have hLower : frame.params.length ≤ 21 := by omega
  have hValid : frame.validIndex 21 := by simp [Locals.validIndex, hParams, hLocals]
  have hInstalledRoot := resultFrame_get_result frame 21 root hLower hValid
  have hInstalledData (field : Nat) (hf : field < 7) :
      (resultFrame frame 21 root).get (6 + field) = some (.i64 ((Memory.cellWords cell).getD field 0)) := by
    apply resultFrame_get_of_ne frame 21 (6 + field) root _ hLower (by omega)
      (by simp [Locals.validIndex, hParams, hLocals]; omega) (by omega) (hData field hf)
  have hLengthBound : root.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [initial_singleton_data_shape]
  simp only [List.append_assoc]
  apply resultProgram_spec 36 21 module env store frame root hValues hRoot hLower hValid
  apply lengthStore_spec module env store (resultFrame frame 21 root) root 1 21 rfl hInstalledRoot hLengthBound
  apply initial_singleton_stage_spec env (writeLength store root 1) (resultFrame frame 21 root) cell
    hParams (by simpa only [resultFrame_locals_length] using hLocals) rfl hInstalledData
  apply initial_singleton_store_spec env (writeLength store root 1) (initialSingletonDataFrame frame root cell)
    root cell rfl
  · simp [initialSingletonDataFrame, initialSingletonStageFrame, resultFrame, Locals.get, hParams, hLocals]
  · intro field hf
    interval_cases field <;>
      simp [initialSingletonDataFrame, initialSingletonStageFrame, resultFrame, Locals.get,
        Memory.cellWords, Array.getD, hParams, hLocals]
  · exact hFit32
  · simpa only [writeLength_pages] using hFitMemory
  · exact hNext (initial_singleton_grid store root cell hFit32 hFitMemory)
      (initial_singleton_writes store root cell hFit32)

#print axioms initial_singleton_stage_shape
#print axioms initial_singleton_data_shape
#print axioms initial_singleton_stage_spec
#print axioms initial_singleton_data_spec

end Project.EulerRiemann.Frozen.Execution
