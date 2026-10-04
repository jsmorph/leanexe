import Project.Binary32.Module
import Project.IR.Correct
import Project.ProofKit.F32Bits
import Project.Encoding.RoundTrip

namespace Project.Binary32

open Project.Pipeline Project.IR Project.ProofKit LeanExe.Examples.Binary32

/-- `axpy32` with its three arguments as one tuple. -/
def axpy32Tuple (x : Float32 × Float32 × Float32) : Float32 := axpy32 x.1 x.2.1 x.2.2

/-- `hypot32` with its two arguments as one pair. -/
def hypot32Pair (x : Float32 × Float32) : Float32 := hypot32 x.1 x.2

/-- `ratio32` with its three arguments as one tuple. -/
def ratio32Tuple (x : Float32 × Float32 × Float32) : Float32 := ratio32 x.1 x.2.1 x.2.2

theorem axpy32_implements : Implements binary32.module 2 axpy32Tuple :=
  Func.implements binary32.funcs 0 binary32.axpy32.ir "axpy32" rfl axpy32Tuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨a, x, y⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [binary32.axpy32.ir, Expr.evalResults, Func.state, Func.locals, Func.width,
        Func.scratch, Expr.eval, Expr.scratchWidth, IR.Stmt.scratchWidth, State.get, F32Op.apply,
        Scalar.values, axpy32Tuple, axpy32, F32Bits.toBits_add, F32Bits.toBits_mul]⟩)
      fun _ _ h => h

theorem hypot32_implements : Implements binary32.module 3 hypot32Pair :=
  Func.implements binary32.funcs 1 binary32.hypot32.ir "hypot32" rfl hypot32Pair
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨x, y⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [binary32.hypot32.ir, Expr.evalResults, Func.state, Func.locals, Func.width,
        Func.scratch, Expr.eval, Expr.scratchWidth, IR.Stmt.scratchWidth, State.get, F32Op.apply,
        F32UnOp.apply, Scalar.values, hypot32Pair, hypot32, F32Bits.toBits_add,
        F32Bits.toBits_mul, F32Bits.toBits_sqrt]⟩)
      fun _ _ h => h

theorem ratio32_implements : Implements binary32.module 4 ratio32Tuple :=
  Func.implements binary32.funcs 2 binary32.ratio32.ir "ratio32" rfl ratio32Tuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨a, b, c⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [binary32.ratio32.ir, Expr.evalResults, Func.state, Func.locals, Func.width,
        Func.scratch, Expr.eval, Expr.scratchWidth, IR.Stmt.scratchWidth, State.get, F32Op.apply,
        Scalar.values, ratio32Tuple, ratio32, F32Bits.toBits_sub, F32Bits.toBits_div]⟩)
      fun _ _ h => h

/-- `encode` succeeds on `binary32.module`, and its bytes decode to a module that computes
`axpy32`, `hypot32`, and `ratio32` bit for bit. -/
theorem binary32_bytes : ∃ bytes, Wasm.Encoding.encode binary32.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 axpy32Tuple ∧
      Implements m 3 hypot32Pair ∧ Implements m 4 ratio32Tuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip binary32.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, binary32.module, decoded, axpy32_implements, hypot32_implements,
    ratio32_implements⟩

#print axioms binary32_bytes

end Project.Binary32
