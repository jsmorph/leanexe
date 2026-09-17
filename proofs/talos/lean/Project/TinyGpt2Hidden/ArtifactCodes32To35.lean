import Project.TinyGpt2Hidden.ArtifactBody32
import Project.TinyGpt2Hidden.ArtifactBody34
import Project.TinyGpt2Hidden.ArtifactBody35
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code32_decoded :
    code { bytes := artifactBytes, pos := 4323, limit := 16006 } =
      .ok (Cache.raw.codes[32]!, { bytes := artifactBytes, pos := 4416, limit := 16006 }) := by
  exact code32_decoded_parts

#print axioms code32_decoded

theorem code33_decoded :
    code { bytes := artifactBytes, pos := 4416, limit := 16006 } =
      .ok (Cache.raw.codes[33]!, { bytes := artifactBytes, pos := 4438, limit := 16006 }) := by
  cbv

#print axioms code33_decoded

theorem code34_decoded :
    code { bytes := artifactBytes, pos := 4438, limit := 16006 } =
      .ok (Cache.raw.codes[34]!, { bytes := artifactBytes, pos := 4582, limit := 16006 }) := by
  exact code34_decoded_parts

#print axioms code34_decoded

theorem code35_decoded :
    code { bytes := artifactBytes, pos := 4582, limit := 16006 } =
      .ok (Cache.raw.codes[35]!, { bytes := artifactBytes, pos := 4743, limit := 16006 }) := by
  exact code35_decoded_parts

#print axioms code35_decoded

end Project.TinyGpt2Hidden.Artifact
