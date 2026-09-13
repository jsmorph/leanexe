import Project.EulerRiemann.InitialLoopFrame
import Project.EulerRiemann.MemoryLength

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold

theorem initial_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n size : Nat) (source tracker output : UInt64) (done : Bool)
    (h : InitialFrameAt frame fuel n size source tracker output done)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : if fuel = 0 ∨ done then Q (.Break 1 store frame)
      else wp module rest Q store frame env) :
    wp module (initialLoop.take 7 ++ rest) Q store frame env := by
  have hShape := AnnotationMatches.function_95_while_loop_0_guard_eq
  change some (initialLoop.take 7) = some (FuelGuard.program 0 8) at hShape
  rw [Option.some.inj hShape]
  apply FuelGuard.program_spec 0 8 module env store frame fuel (if done then 1 else 0) h.values
    (by simp [Locals.get, h.params])
    (by simpa [Locals.get, h.params, h.locals] using h.done)
  cases done <;> simpa using hNext

theorem initial_select_shape : (initialLoop.drop 7).take 7 =
    [.localGet 2, .localGet 4, .localSet 48, .localGet 48, .wrapI64, .load64 0, .leUI64] := rfl

theorem initial_select_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source : UInt64) (size : Nat) (grid : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hSource : frame.get 4 = some (.i64 source))
    (hSize : frame.get 2 = some (.i64 (UInt64.ofNat size)))
    (hSize64 : size < UInt64.size) (hGrid64 : grid.size < UInt64.size)
    (hGrid : Memory.GridAt store source grid) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store
      { initialSelectedFrame frame source with values := [.i32 (if size ≤ grid.size then 1 else 0)] } env) :
    wp module ((initialLoop.drop 7).take 7 ++ rest) Q store frame env := by
  have hSourceParam := Frame.parameter_getElem_of_get frame 4 (.i64 source) (by omega) hSource
  have hSizeParam := Frame.parameter_getElem_of_get frame 2 (.i64 (UInt64.ofNat size)) (by omega) hSize
  rw [initial_select_shape]
  wp_run [List.cons_append, List.nil_append, hParams, hLocals, hValues, hSourceParam, hSizeParam]
  simp only [Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, reduceIte, List.length_set,
    List.getElem?_eq_getElem, hParams, hLocals, hSourceParam, hSizeParam, List.getElem_set_self]
  have hTwo32 : 2 ^ 32 = 4294967296 := by norm_num
  rw [hTwo32, ← Project.ProofKit.Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, UInt32.add_zero, add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr hGrid.lengthBound), hGrid.lengthRead]
  have hCompare : (UInt64.ofNat size ≤ UInt64.ofNat grid.size) ↔ size ≤ grid.size := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hSize64,
      UInt64.toNat_ofNat_of_lt' hGrid64]
  simpa [wp_leUI64_cons, hCompare, initialSelectedFrame, resultFrame, hParams] using hNext

#print axioms initial_guard_spec
#print axioms initial_select_shape
#print axioms initial_select_spec

end Project.EulerRiemann.Execution
