import Project.TinyGpt2Hidden.ArtifactBody12
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code12_decoded :
    code { bytes := artifactBytes, pos := 2335, limit := 16006 } =
      .ok (Cache.raw.codes[12]!, { bytes := artifactBytes, pos := 2587, limit := 16006 }) := by
  exact code12_decoded_parts

#print axioms code12_decoded

theorem code13_decoded :
    code { bytes := artifactBytes, pos := 2587, limit := 16006 } =
      .ok (Cache.raw.codes[13]!, { bytes := artifactBytes, pos := 2598, limit := 16006 }) := by
  cbv

#print axioms code13_decoded

theorem code14_decoded :
    code { bytes := artifactBytes, pos := 2598, limit := 16006 } =
      .ok (Cache.raw.codes[14]!, { bytes := artifactBytes, pos := 2609, limit := 16006 }) := by
  cbv

#print axioms code14_decoded

theorem code15_decoded :
    code { bytes := artifactBytes, pos := 2609, limit := 16006 } =
      .ok (Cache.raw.codes[15]!, { bytes := artifactBytes, pos := 2620, limit := 16006 }) := by
  cbv

#print axioms code15_decoded

end Project.TinyGpt2Hidden.Artifact
