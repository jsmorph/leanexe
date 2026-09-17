import Project.TinyGpt2Hidden.ArtifactBody72
import Project.TinyGpt2Hidden.ArtifactBody74
import Project.TinyGpt2Hidden.ArtifactBody75
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code72_decoded :
    code { bytes := artifactBytes, pos := 9349, limit := 16006 } =
      .ok (Cache.raw.codes[72]!, { bytes := artifactBytes, pos := 9983, limit := 16006 }) := by
  exact code72_decoded_parts

#print axioms code72_decoded

theorem code73_decoded :
    code { bytes := artifactBytes, pos := 9983, limit := 16006 } =
      .ok (Cache.raw.codes[73]!, { bytes := artifactBytes, pos := 9995, limit := 16006 }) := by
  cbv

#print axioms code73_decoded

theorem code74_decoded :
    code { bytes := artifactBytes, pos := 9995, limit := 16006 } =
      .ok (Cache.raw.codes[74]!, { bytes := artifactBytes, pos := 15177, limit := 16006 }) := by
  exact code74_decoded_parts

#print axioms code74_decoded

theorem code75_decoded :
    code { bytes := artifactBytes, pos := 15177, limit := 16006 } =
      .ok (Cache.raw.codes[75]!, { bytes := artifactBytes, pos := 15544, limit := 16006 }) := by
  exact code75_decoded_parts

#print axioms code75_decoded

end Project.TinyGpt2Hidden.Artifact
