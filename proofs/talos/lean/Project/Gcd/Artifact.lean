import Project.Gcd.ArtifactDecode
import Project.Gcd.Program
import Project.Artifact.Binary.Evidence

set_option maxRecDepth 1048576

namespace Project.Gcd.Artifact

open Wasm.Binary

def cachedModule? : Option Wasm.Module := do
  let validated ← (validate Project.Gcd.Artifact.Cache.raw).toOption
  pure validated.toTalos

theorem cachedModule_isSome : cachedModule?.isSome = true := by
  native_decide

def module? : Option Wasm.Module := do
  verifiedModule? artifactBytes

theorem module_isSome : module?.isSome = true := by
  native_decide

theorem decode_validate_exists :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧ validate raw = .ok validated := by
  have evidence := evidenceOfIsSome artifactBytes module_isSome
  exact evidence.imp fun raw ⟨validated, hdecode, hvalidate, _⟩ =>
    ⟨validated, hdecode, hvalidate⟩

def module : Wasm.Module :=
  module?.getD default

theorem module?_eq : module? = some module := by
  cases h : module? with
  | none =>
      have hsome := module_isSome
      simp [h] at hsome
  | some value => simp [module, h]

def cachedModule : Wasm.Module :=
  cachedModule?.getD default

end Project.Gcd.Artifact
