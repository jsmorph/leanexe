import Project.ProofKit.ScalarTransition
import Project.ProofKit.Frame
import Project.ProofKit.FixedArrayFrame

namespace Project.ProofKit.ScalarTransition
open Wasm FixedArrayFold

theorem State.ofLocals_get (frame : Locals) (index : Nat) :
    (State.ofLocals frame).get index = frame.get index := rfl

theorem State.ofLocals_result_set (frame : Locals) (index : Nat) (value : UInt64)
    (hLower : frame.params.length ≤ index) (hValid : frame.validIndex index) :
    (State.ofLocals frame).set? index (.i64 value) =
      some (State.ofLocals (resultFrame frame index value)) := by
  have hNotParam : ¬index < frame.params.length := Nat.not_lt.mpr hLower
  have hBound : index < frame.params.length + frame.locals.length := hValid
  simp [State.ofLocals, State.set?, resultFrame, hNotParam, hBound]

theorem Stmt.program_frame_spec (statement : Stmt) (scratch : Nat) (frame next : Locals)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (hValues : frame.values = []) (hNextValues : next.values = [])
    (hEval : statement.eval scratch (State.ofLocals frame) = some (State.ofLocals next))
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : wp module_ rest Q store next env) :
    wp module_ (statement.program scratch ++ rest) Q store frame env := by
  have hInitial : (State.ofLocals frame).toLocals [] = frame := by
    apply Project.ProofKit.Frame.ext
    · rfl
    · rfl
    · exact hValues.symm
  have hFinal : (State.ofLocals next).toLocals [] = next := by
    apply Project.ProofKit.Frame.ext
    · rfl
    · rfl
    · exact hNextValues.symm
  simpa only [hInitial, hFinal] using statement.program_spec scratch (State.ofLocals frame)
    (State.ofLocals next) [] module_ env store rest Q hEval (by simpa only [hFinal] using hNext)

theorem Expr.assign_frame_spec (expression : Expr .u64) (scratch index : Nat)
    (frame : Locals) (value : UInt64) (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (hValues : frame.values = []) (hLower : frame.params.length ≤ index) (hValid : frame.validIndex index)
    (hEval : expression.eval scratch (State.ofLocals frame) = some (value, State.ofLocals frame))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store (resultFrame frame index value) env) :
    wp module_ ((Stmt.assign index expression).program scratch ++ rest) Q store frame env := by
  apply (Stmt.assign index expression).program_frame_spec scratch frame (resultFrame frame index value)
    module_ env store hValues rfl
  · simpa [Stmt.eval, hEval] using
      State.ofLocals_result_set frame index value hLower hValid
  · exact hNext

#print axioms Expr.assign_frame_spec
#print axioms State.ofLocals_result_set
#print axioms Stmt.program_frame_spec

end Project.ProofKit.ScalarTransition
