import Project.ScaledHypot.Module
import Project.IR.Correct
import Project.ProofKit.F64Bits
import Project.Encoding.RoundTrip

namespace Project.ScaledHypot

open Project.Pipeline Project.IR Project.ProofKit

/-- `scaledHypot` with its three arguments as one tuple. -/
def scaledHypotTuple (x : Float × Float × Float) : Float :=
  LeanExe.Examples.ScaledHypot.scaledHypot x.1 x.2.1 x.2.2

theorem scaledHypot_implements :
    Implements scaledHypot.module 0 scaledHypotTuple (fun _ => 0) :=
  Func.implements scaledHypot.ir "scaledHypot" scaledHypotTuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨x, y, s⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [scaledHypot.ir, Func.state, Func.width, Func.scratch, Expr.eval, Expr.scratchWidth,
        IR.Stmt.scratchWidth, State.get, F64Op.apply, F64UnOp.apply, Scalar.values,
        scaledHypotTuple, LeanExe.Examples.ScaledHypot.scaledHypot, F64Bits.toBits_add,
        F64Bits.toBits_mul, F64Bits.toBits_div, F64Bits.toBits_sqrt]⟩) fun _ _ h => h

/-- The bytes `encode` produces for `scaledHypot.module` decode to a module that
computes `scaledHypot` bit for bit. -/
theorem scaledHypot_bytes (bytes : ByteArray)
    (success : Wasm.Encoding.encode scaledHypot.module = .ok bytes) :
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 0 scaledHypotTuple (fun _ => 0) :=
  ⟨scaledHypot.module, Wasm.Encoding.decode_encode scaledHypot.module bytes (by decide) success,
    scaledHypot_implements⟩

end Project.ScaledHypot
