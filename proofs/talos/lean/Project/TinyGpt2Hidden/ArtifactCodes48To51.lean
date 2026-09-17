import Project.TinyGpt2Hidden.ArtifactBody51
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code48_decoded :
    code { bytes := artifactBytes, pos := 6073, limit := 16006 } =
      .ok (Cache.raw.codes[48]!, { bytes := artifactBytes, pos := 6084, limit := 16006 }) := by
  cbv

#print axioms code48_decoded

theorem code49_decoded :
    code { bytes := artifactBytes, pos := 6084, limit := 16006 } =
      .ok (Cache.raw.codes[49]!, { bytes := artifactBytes, pos := 6095, limit := 16006 }) := by
  cbv

#print axioms code49_decoded

theorem code50_decoded :
    code { bytes := artifactBytes, pos := 6095, limit := 16006 } =
      .ok (Cache.raw.codes[50]!, { bytes := artifactBytes, pos := 6106, limit := 16006 }) := by
  cbv

#print axioms code50_decoded

theorem code51_decoded :
    code { bytes := artifactBytes, pos := 6106, limit := 16006 } =
      .ok (Cache.raw.codes[51]!, { bytes := artifactBytes, pos := 6169, limit := 16006 }) := by
  exact code51_decoded_parts

#print axioms code51_decoded

end Project.TinyGpt2Hidden.Artifact
