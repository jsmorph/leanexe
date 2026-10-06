import Examples.Bucket.Module
import LeanExe.IR.Correct
import LeanExe.ProofKit.F64Convert
import LeanExe.Encoding.RoundTrip

namespace Examples.Bucket

open LeanExe.Pipeline LeanExe.IR LeanExe.ProofKit

/-- `bucket` with its three arguments as one tuple. -/
def bucketTuple (x : Float × Float × Float) : UInt64 :=
  Examples.Bucket.bucket x.1 x.2.1 x.2.2

theorem bucket_implements : Implements bucket.module 2 bucketTuple :=
  Func.implements [(bucket.ir, "bucket")] 0 bucket.ir "bucket" rfl bucketTuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨x, lo, width⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [bucket.ir, Expr.evalResults, Func.state, Func.locals, Func.width, Func.scratch, Expr.eval,
        Expr.scratchWidth, LeanExe.IR.Stmt.scratchWidth, State.get, F64Op.apply, Scalar.values,
        bucketTuple, Examples.Bucket.bucket, F64Bits.toBits_sub, F64Bits.toBits_div,
        F64Convert.toUInt64_eq]⟩) fun _ _ h => h

/-- `encode` succeeds on `bucket.module`, and its bytes decode to a module that
computes `bucket` exactly. -/
theorem bucket_bytes : ∃ bytes, Wasm.Encoding.encode bucket.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 bucketTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip bucket.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, bucket.module, decoded, bucket_implements⟩

end Examples.Bucket
