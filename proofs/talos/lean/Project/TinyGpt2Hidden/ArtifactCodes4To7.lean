import Project.TinyGpt2Hidden.ArtifactBody4
import Project.TinyGpt2Hidden.ArtifactBody5
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 1105, limit := 16006 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 1158, limit := 16006 }) := by
  exact code4_decoded_parts

#print axioms code4_decoded

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 1158, limit := 16006 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 1409, limit := 16006 }) := by
  exact code5_decoded_parts

#print axioms code5_decoded

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 1409, limit := 16006 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 1420, limit := 16006 }) := by
  cbv

#print axioms code6_decoded

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 1420, limit := 16006 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 1432, limit := 16006 }) := by
  cbv

#print axioms code7_decoded

end Project.TinyGpt2Hidden.Artifact
