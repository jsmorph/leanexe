import Project.Scale.Module
import Project.IR.Correct
import Project.Encoding.RoundTrip

namespace Project.Scale

open Project.Pipeline Project.IR

/-- `scale` with its three arguments as one tuple. -/
def scaleTuple (x : UInt64 × UInt64 × UInt64) : UInt64 :=
  LeanExe.Examples.Scale.scale x.1 x.2.1 x.2.2

theorem scale_implements : Implements scale.module 0 scaleTuple (fun _ => 0) :=
  Func.implements scale.ir "scale" scaleTuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨a, b, c⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      simp [scale.ir, Func.state, Func.width, Func.scratch, Expr.eval, Expr.scratchWidth,
        Stmt.scratchWidth, State.get, State.set?, U64Op.apply, Scalar.values, scaleTuple,
        LeanExe.Examples.Scale.scale]
      intro hZero
      simp [hZero]⟩) fun _ _ h => h

/-- The bytes `encode` produces for `scale.module` decode to a module that
computes `scale` exactly. -/
theorem scale_bytes (bytes : ByteArray) (success : Wasm.Encoding.encode scale.module = .ok bytes) :
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 0 scaleTuple (fun _ => 0) :=
  ⟨scale.module, Wasm.Encoding.decode_encode scale.module bytes (by decide) success,
    scale_implements⟩

end Project.Scale
