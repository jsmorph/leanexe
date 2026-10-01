import Project.Axpy.Module
import Project.IR.Correct
import Project.ProofKit.F64Bits
import Project.Encoding.RoundTrip

namespace Project.Axpy

open Project.Pipeline Project.IR Project.ProofKit

/-- `axpy` with its three arguments as one tuple. -/
def axpyTuple (x : Float × Float × Float) : Float := LeanExe.Examples.Axpy.axpy x.1 x.2.1 x.2.2

theorem axpy_implements : Implements axpy.module 2 axpyTuple :=
  Func.implements [(axpy.ir, "axpy")] 0 axpy.ir "axpy" rfl axpyTuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨a, x, y⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [axpy.ir, Expr.evalResults, Func.state, Func.locals, Func.width, Func.scratch, Expr.eval, Expr.scratchWidth,
        IR.Stmt.scratchWidth, State.get, F64Op.apply, Scalar.values, axpyTuple,
        LeanExe.Examples.Axpy.axpy, F64Bits.toBits_add, F64Bits.toBits_mul]⟩) fun _ _ h => h

/-- `encode` succeeds on `axpy.module`, and its bytes decode to a module that
computes `axpy` bit for bit. -/
theorem axpy_bytes : ∃ bytes, Wasm.Encoding.encode axpy.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 axpyTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip axpy.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, axpy.module, decoded, axpy_implements⟩

end Project.Axpy
