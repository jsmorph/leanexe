import Project.EulerRiemann.InitialExtractLoad
import Project.EulerRiemann.InitialExtractSelect
import Project.EulerRiemann.InitialExtractCounts

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold

def initialExtractInputProgram : Wasm.Program := initialExtractBody.take 28

def initialExtractInputFrame (frame : Locals) (source size length : UInt64) : Locals :=
  initialExtractCountsFrame
    (resultFrame (resultFrame (initialExtractLoadFrame frame source size length) 52 size) 53 size) size

theorem initial_extract_input_shape : initialExtractInputProgram =
    initialExtractBody.take 10 ++ (initialExtractBody.drop 10).take 5 ++
      (initialExtractBody.drop 15).take 5 ++ (initialExtractBody.drop 20).take 8 := by
  rfl

theorem initial_extract_input_gets (frame : Locals) (source size length : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    (initialExtractInputFrame frame source size length).get 48 = some (.i64 source) ∧
    (initialExtractInputFrame frame source size length).get 53 = some (.i64 size) ∧
    (initialExtractInputFrame frame source size length).get 54 = some (.i64 0) ∧
    (initialExtractInputFrame frame source size length).get 55 = some (.i64 (size * 7)) := by
  simp only [initialExtractInputFrame, initialExtractCountsFrame, initialExtractLoadFrame,
    initialExtractPointersFrame, resultFrame_get_ne, resultFrame_params, hParams,
    Nat.reduceLeDiff, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply resultFrame_get_result <;>
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem initial_extract_input_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source : UInt64) (size : Nat) (grid : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hSource : frame.get 4 = some (.i64 source))
    (hSizeParam : frame.get 2 = some (.i64 (UInt64.ofNat size)))
    (hGrid : Memory.GridAt store source grid) (hSize : size ≤ grid.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store
      (initialExtractInputFrame frame source (UInt64.ofNat size) (UInt64.ofNat grid.size)) env) :
    wp module (initialExtractInputProgram ++ rest) Q store frame env := by
  let loaded := initialExtractLoadFrame frame source (UInt64.ofNat size) (UInt64.ofNat grid.size)
  let stopped := resultFrame loaded 52 (UInt64.ofNat size)
  let spanned := resultFrame stopped 53 (UInt64.ofNat size)
  have hLoadedParams : loaded.params.length = 5 := hParams
  have hLoadedLocals : loaded.locals.length = 61 := by
    simpa only [loaded, initialExtractLoadFrame, initialExtractPointersFrame, resultFrame_locals_length] using hLocals
  have hGets := initial_extract_load_gets frame source (UInt64.ofNat size) (UInt64.ofNat grid.size) hParams hLocals
  have hLe : UInt64.ofNat size ≤ UInt64.ofNat grid.size := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt hSize hGrid.size_lt),
      UInt64.toNat_ofNat_of_lt' hGrid.size_lt]
    exact hSize
  have hStart : stopped.get 49 = some (.i64 0) :=
    (resultFrame_get_ne loaded 52 49 (UInt64.ofNat size) (by omega) (by decide)).trans hGets.2.1
  have hStop : stopped.get 52 = some (.i64 (UInt64.ofNat size)) :=
    resultFrame_get_result loaded 52 (UInt64.ofNat size) (by omega)
      (by simp [Locals.validIndex, hLoadedParams, hLoadedLocals])
  have hSpanStart : spanned.get 49 = some (.i64 0) :=
    (resultFrame_get_ne stopped 53 49 (UInt64.ofNat size)
      (by change loaded.params.length ≤ 53; omega) (by decide)).trans hStart
  have hSpanSize : spanned.get 53 = some (.i64 (UInt64.ofNat size)) :=
    resultFrame_get_result stopped 53 (UInt64.ofNat size) (by change loaded.params.length ≤ 53; omega)
      (by simp [stopped, Locals.validIndex, resultFrame_params, resultFrame_locals_length,
        hLoadedParams, hLoadedLocals])
  rw [initial_extract_input_shape, List.append_assoc, List.append_assoc, List.append_assoc]
  apply initial_extract_load_spec env store frame source (UInt64.ofNat size) grid
    hParams hLocals hValues hSource hSizeParam hGrid
  apply initial_extract_stop_spec env store loaded (UInt64.ofNat size) (UInt64.ofNat grid.size)
    hLoadedParams hLoadedLocals rfl hGets.2.2.1 hGets.2.2.2 hLe
  apply initial_extract_span_spec env store stopped (UInt64.ofNat size) hLoadedParams
    (by simpa only [stopped, resultFrame_locals_length] using hLoadedLocals) rfl hStart hStop
  apply initial_extract_counts_spec env store spanned (UInt64.ofNat size) hLoadedParams
    (by simpa only [spanned, stopped, resultFrame_locals_length] using hLoadedLocals) rfl hSpanStart hSpanSize
  exact hNext

#print axioms initial_extract_input_shape
#print axioms initial_extract_input_gets
#print axioms initial_extract_input_spec

end Project.EulerRiemann.Execution
