import LeanExe.WGSL.RectangularArtifact
import LeanExe.WGSL.Invocation

namespace LeanExe.WGSL

/-- Exact source identity, checked resources and the operational theorem travel
together. No renderer or manifest equality is used to establish source identity. -/
structure InvocationArtifact (source : String) (s : ScalarSemantics) (p : Profile) where
  kernel : CheckedGemm
  parsed : parseGemm source = .ok kernel.ast
  execution : ExecutionTheorem (Invocation.model s) p kernel
    (fun input => input.buffers.Valid kernel.ast.config)
    (fun input output => Invocation.Invariant s p kernel.ast.config input.buffers
      input.row input.col (.done output))

def RectangularArtifact.invocationArtifact {s p c} (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c) :
    InvocationArtifact RectangularArtifact.source s p where
  kernel := RectangularArtifact.checked
  parsed := RectangularArtifact.parsed
  execution := Invocation.execution _ hc he ht

/-- Every active invocation's observable store equals the source GEMM word
under an interpretation that establishes the restricted scalar graph. -/
theorem InvocationArtifact.exact {source s arithmetic} (artifact : InvocationArtifact source s restricted)
    (hs : SeparateInterpretation s arithmetic) (input : Invocation.Input)
    (hb : input.buffers.Valid artifact.kernel.ast.config)
    (hr : input.row < artifact.kernel.ast.config.rows)
    (hc : input.col < artifact.kernel.ast.config.cols)
    (output : Option Invocation.Write)
    (run : (Invocation.model s).Exec restricted artifact.kernel input output) :
    output = some ⟨input.row * artifact.kernel.ast.config.cols + input.col,
      gemmCell arithmetic artifact.kernel.ast.config input.buffers.a input.buffers.b
        input.row input.col⟩ := by
  have h := artifact.execution.corresponds input output hb run
  cases output with
  | none => exact False.elim (h ⟨hr, hc⟩)
  | some w =>
      have value := h.2.2.2.restricted_exact hs
      cases w
      simp only [gemmCell] at *
      congr 2
      exact h.2.2.1

#print axioms RectangularArtifact.invocationArtifact
#print axioms InvocationArtifact.exact

end LeanExe.WGSL
