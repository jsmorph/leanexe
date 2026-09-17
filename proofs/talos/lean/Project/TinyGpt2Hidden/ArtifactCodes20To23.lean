import Project.TinyGpt2Hidden.ArtifactBody20
import Project.TinyGpt2Hidden.ArtifactBody21
import Project.TinyGpt2Hidden.ArtifactBody22
import Project.TinyGpt2Hidden.ArtifactBody23
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code20_decoded :
    code { bytes := artifactBytes, pos := 2913, limit := 16006 } =
      .ok (Cache.raw.codes[20]!, { bytes := artifactBytes, pos := 2942, limit := 16006 }) := by
  exact code20_decoded_parts

#print axioms code20_decoded

theorem code21_decoded :
    code { bytes := artifactBytes, pos := 2942, limit := 16006 } =
      .ok (Cache.raw.codes[21]!, { bytes := artifactBytes, pos := 2971, limit := 16006 }) := by
  exact code21_decoded_parts

#print axioms code21_decoded

theorem code22_decoded :
    code { bytes := artifactBytes, pos := 2971, limit := 16006 } =
      .ok (Cache.raw.codes[22]!, { bytes := artifactBytes, pos := 3000, limit := 16006 }) := by
  exact code22_decoded_parts

#print axioms code22_decoded

theorem code23_decoded :
    code { bytes := artifactBytes, pos := 3000, limit := 16006 } =
      .ok (Cache.raw.codes[23]!, { bytes := artifactBytes, pos := 3029, limit := 16006 }) := by
  exact code23_decoded_parts

#print axioms code23_decoded

end Project.TinyGpt2Hidden.Artifact
