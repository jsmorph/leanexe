import Project.TinyGpt2Hidden.ArtifactBody24
import Project.TinyGpt2Hidden.ArtifactBody25
import Project.TinyGpt2Hidden.ArtifactBody26
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code24_decoded :
    code { bytes := artifactBytes, pos := 3029, limit := 16006 } =
      .ok (Cache.raw.codes[24]!, { bytes := artifactBytes, pos := 3094, limit := 16006 }) := by
  exact code24_decoded_parts

#print axioms code24_decoded

theorem code25_decoded :
    code { bytes := artifactBytes, pos := 3094, limit := 16006 } =
      .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 3541, limit := 16006 }) := by
  exact code25_decoded_parts

#print axioms code25_decoded

theorem code26_decoded :
    code { bytes := artifactBytes, pos := 3541, limit := 16006 } =
      .ok (Cache.raw.codes[26]!, { bytes := artifactBytes, pos := 3803, limit := 16006 }) := by
  exact code26_decoded_parts

#print axioms code26_decoded

theorem code27_decoded :
    code { bytes := artifactBytes, pos := 3803, limit := 16006 } =
      .ok (Cache.raw.codes[27]!, { bytes := artifactBytes, pos := 3815, limit := 16006 }) := by
  cbv

#print axioms code27_decoded

end Project.TinyGpt2Hidden.Artifact
