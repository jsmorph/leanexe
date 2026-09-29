import Project.Piecewise.Module
import Project.IR.Correct
import Project.ProofKit.F64Bits
import Project.Encoding.RoundTrip

namespace Project.Piecewise

open Project.Pipeline Project.IR Project.ProofKit

/-- `piecewise` with its three arguments as one tuple. -/
def piecewiseTuple (x : Float × Float × Float) : Float :=
  LeanExe.Examples.Piecewise.piecewise x.1 x.2.1 x.2.2

theorem piecewise_implements :
    Implements piecewise.module 3 piecewiseTuple (fun _ => 0) :=
  Func.implements [(piecewise.ir, "piecewise")] 0 piecewise.ir "piecewise" rfl piecewiseTuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨x, lo, hi⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨[.f64 (LeanExe.Examples.Piecewise.piecewise x lo hi).toBits],
        piecewise.ir.state (Scalar.values (x, lo, hi)), ?_, rfl⟩
      have h0 : (0.0 : Float).toBits = 0 := by decide
      have h05 : (0.5 : Float).toBits = 4602678819172646912 := by decide
      have h15 : (1.5 : Float).toBits = 4609434218613702656 := by decide
      have hx : piecewise.ir.state (Scalar.values (x, lo, hi)) =
          { params := [.f64 x.toBits, .f64 lo.toBits, .f64 hi.toBits], locals := [] } := rfl
      rw [hx]
      dsimp only [piecewise.ir, Func.scratch]
      simp [Expr.evalResults, Expr.eval, State.get, F64Op.apply, F64UnOp.apply,
        LeanExe.Examples.Piecewise.piecewise, F64Bits.beq_eq,
        F64Bits.lt_iff, F64Bits.le_iff]
      cases h1 : Wasm.IEEE64.eq x.toBits lo.toBits <;>
        cases h2 : Wasm.IEEE64.lt x.toBits lo.toBits <;>
        cases h3 : Wasm.IEEE64.le hi.toBits x.toBits <;>
        cases h4 : Wasm.IEEE64.le x.toBits hi.toBits <;>
        cases h5 : Wasm.IEEE64.le lo.toBits x.toBits <;>
        cases h6 : Wasm.IEEE64.le lo.toBits hi.toBits <;>
        simp [h1, h2, h3, h4, h5, h6, F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul,
          F64Bits.toBits_neg, F64Bits.toBits_abs, F64Bits.toBits_min, F64Bits.toBits_max, h0, h05,
          h15]⟩) fun _ _ h => h

/-- `encode` succeeds on `piecewise.module`, and its bytes decode to a module that
computes `piecewise` bit for bit. -/
theorem piecewise_bytes : ∃ bytes, Wasm.Encoding.encode piecewise.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 3 piecewiseTuple (fun _ => 0) := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip piecewise.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, piecewise.module, decoded, piecewise_implements⟩

end Project.Piecewise
