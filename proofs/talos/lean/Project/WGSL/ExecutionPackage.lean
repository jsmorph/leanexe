import Project.WGSL.Binary32
import LeanExe.WGSL.Manifest

/-! Artifact fidelity over binary32 words. No real-valued specification or
error-domain premise is used by this package. Runtime conformance is explicit. -/
namespace Project.WGSL.Binary32

open LeanExe.WGSL

theorem except_ok_of_toOption {E A : Type} (result : Except E A) (value : A)
    (h : result.toOption = some value) : result = .ok value := by
  cases result with
  | error _ => cases h
  | ok actual => cases Option.some.inj h; rfl

/-- An independently parsed shader and manifest with its selected profile.
Neither a generator identity nor a hash can inhabit the parsing obligation. -/
structure Package (source : String) (metadata : Manifest) where
  tag : ProfileTag
  kernel : CheckedGemm
  parsed : parseGemm source = .ok kernel.ast
  matched : metadata.Matches kernel.ast.config tag

def Package.artifact {source metadata} (package : Package source metadata) :
    DispatchArtifact source semantics package.tag.profile where
  kernel := package.kernel
  parsed := package.parsed
  execution := Dispatch.execution package.kernel package.tag.acceptsScalar package.tag.acceptsSeparate total

theorem Package.exact {source metadata} (package : Package source metadata)
    (restrictedTag : package.tag = .separate)
    (input : Dispatch.Input) (output : WordBuffer)
    (hb : input.buffers.Valid package.kernel.ast.config)
    (run : (Dispatch.model semantics).Exec package.tag.profile package.kernel input output)
    {row col : Nat} (hr : row < package.kernel.ast.config.rows)
    (hc : col < package.kernel.ast.config.cols) :
    output (row * package.kernel.ast.config.cols + col) =
      gemmCell arithmetic package.kernel.ast.config input.buffers.a input.buffers.b row col := by
  have result := package.artifact.execution.corresponds input output hb run row col hr hc
  change Dot semantics package.tag.profile package.kernel.ast.config input.buffers.a input.buffers.b
    row col package.kernel.ast.config.inner (output (row * package.kernel.ast.config.cols + col)) at result
  rw [restrictedTag] at result
  exact result.restricted_exact separate

end Project.WGSL.Binary32
