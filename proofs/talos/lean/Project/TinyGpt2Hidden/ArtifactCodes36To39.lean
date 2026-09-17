import Project.TinyGpt2Hidden.ArtifactBody36
import Project.TinyGpt2Hidden.ArtifactBody38
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code36_decoded :
    code { bytes := artifactBytes, pos := 4743, limit := 16006 } =
      .ok (Cache.raw.codes[36]!, { bytes := artifactBytes, pos := 4820, limit := 16006 }) := by
  exact code36_decoded_parts

#print axioms code36_decoded

theorem code37_decoded :
    code { bytes := artifactBytes, pos := 4820, limit := 16006 } =
      .ok (Cache.raw.codes[37]!, { bytes := artifactBytes, pos := 4831, limit := 16006 }) := by
  cbv

#print axioms code37_decoded

theorem code38_decoded :
    code { bytes := artifactBytes, pos := 4831, limit := 16006 } =
      .ok (Cache.raw.codes[38]!, { bytes := artifactBytes, pos := 5279, limit := 16006 }) := by
  exact code38_decoded_parts

#print axioms code38_decoded

theorem code39_decoded :
    code { bytes := artifactBytes, pos := 5279, limit := 16006 } =
      .ok (Cache.raw.codes[39]!, { bytes := artifactBytes, pos := 5290, limit := 16006 }) := by
  cbv

#print axioms code39_decoded

end Project.TinyGpt2Hidden.Artifact
