import Project.EulerRiemann.InitialExtractData
import Project.ProofKit.ScalarConditional

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit ScalarTransition FixedArrayFold

def initialExtractSpan : Stmt :=
  .assign 53 (.ite (.ltU (.get 49) (.get 52)) (.bin .sub (.get 52) (.get 49)) (.const 0))

theorem initial_extract_span_shape : (initialExtractBody.drop 15).take 5 =
    Expr.typedIteProgram (.ltU (.get 49) (.get 52)) (.bin .sub (.get 52) (.get 49))
      (.const 0) 66 [] [.i64] ++ [.localSet 53] := by
  rfl

theorem initial_extract_span_eval (frame : Locals) (size : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hStart : frame.get 49 = some (.i64 0)) (hStop : frame.get 52 = some (.i64 size)) :
    initialExtractSpan.eval 66 (State.ofLocals frame) =
      some (State.ofLocals (resultFrame frame 53 size)) := by
  have hSet := State.ofLocals_result_set frame 53 size (by omega)
    (by simp [Locals.validIndex, hParams, hLocals])
  have hStateStart : (State.ofLocals frame).get 49 = some (.i64 0) := hStart
  have hStateStop : (State.ofLocals frame).get 52 = some (.i64 size) := hStop
  by_cases hPos : (0 : UInt64) < size
  · simpa [initialExtractSpan, Stmt.eval, Expr.eval, U64Op.apply, hStateStart, hStateStop, hPos] using hSet
  · have hZero : size = 0 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.lt_iff_toNat_lt] at hPos
      change ¬0 < size.toNat at hPos
      change size.toNat = 0
      omega
    subst size
    simpa [initialExtractSpan, Stmt.eval, Expr.eval, U64Op.apply, hStateStart, hStateStop] using hSet

theorem initial_extract_span_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (size : UInt64) (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hStart : frame.get 49 = some (.i64 0))
    (hStop : frame.get 52 = some (.i64 size)) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (resultFrame frame 53 size) env) :
    wp module ((initialExtractBody.drop 15).take 5 ++ rest) Q store frame env := by
  rw [initial_extract_span_shape]
  exact Stmt.typedIteAssignProgram_frame_spec 53 (.ltU (.get 49) (.get 52))
    (.bin .sub (.get 52) (.get 49)) (.const 0) 66 [] [.i64] frame (resultFrame frame 53 size)
    module env store hValues rfl (initial_extract_span_eval frame size hParams hLocals hStart hStop)
    Q rest hNext

#print axioms initial_extract_span_shape
#print axioms initial_extract_span_eval
#print axioms initial_extract_span_spec

end Project.EulerRiemann.Execution
