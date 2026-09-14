import Project.EulerOutwardCfl.ArtifactDecode
import Project.Artifact.Binary.Evidence
import Lean.Elab.Tactic.Cbv

namespace Project.EulerOutwardCfl.Artifact

open Wasm.Binary

def cacheValidationSucceeded : Bool :=
  (validate Cache.raw).toOption.isSome

set_option maxRecDepth 131072 in
set_option cbv.maxSteps 1000000 in
theorem cache_validation_test : cacheValidationSucceeded = true := by
  cbv

theorem cache_validation_exists :
    ∃ validated, validate Cache.raw = .ok validated := by
  exact ok_exists_of_toOption_isSome cache_validation_test

#print axioms cache_validation_test
#print axioms cache_validation_exists
end Project.EulerOutwardCfl.Artifact
