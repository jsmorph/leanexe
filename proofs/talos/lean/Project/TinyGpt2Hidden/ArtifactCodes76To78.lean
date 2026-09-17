import Project.TinyGpt2Hidden.ArtifactBody76
import Project.TinyGpt2Hidden.ArtifactBody77
import Project.TinyGpt2Hidden.ArtifactBody78
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code76_decoded :
    code { bytes := artifactBytes, pos := 15544, limit := 16006 } =
      .ok (Cache.raw.codes[76]!, { bytes := artifactBytes, pos := 15572, limit := 16006 }) := by
  exact code76_decoded_parts

#print axioms code76_decoded

theorem code77_decoded :
    code { bytes := artifactBytes, pos := 15572, limit := 16006 } =
      .ok (Cache.raw.codes[77]!, { bytes := artifactBytes, pos := 15653, limit := 16006 }) := by
  exact code77_decoded_parts

#print axioms code77_decoded

theorem code78_decoded :
    code { bytes := artifactBytes, pos := 15653, limit := 16006 } =
      .ok (Cache.raw.codes[78]!, { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  exact code78_decoded_parts

#print axioms code78_decoded

end Project.TinyGpt2Hidden.Artifact
