import Project.TinyGpt2Hidden.ArtifactBody8
import Project.TinyGpt2Hidden.ArtifactBody9
import Project.TinyGpt2Hidden.ArtifactBody10
import Project.TinyGpt2Hidden.ArtifactBody11
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code8_decoded :
    code { bytes := artifactBytes, pos := 1432, limit := 16006 } =
      .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 2178, limit := 16006 }) := by
  exact code8_decoded_parts

#print axioms code8_decoded

theorem code9_decoded :
    code { bytes := artifactBytes, pos := 2178, limit := 16006 } =
      .ok (Cache.raw.codes[9]!, { bytes := artifactBytes, pos := 2222, limit := 16006 }) := by
  exact code9_decoded_parts

#print axioms code9_decoded

theorem code10_decoded :
    code { bytes := artifactBytes, pos := 2222, limit := 16006 } =
      .ok (Cache.raw.codes[10]!, { bytes := artifactBytes, pos := 2306, limit := 16006 }) := by
  exact code10_decoded_parts

#print axioms code10_decoded

theorem code11_decoded :
    code { bytes := artifactBytes, pos := 2306, limit := 16006 } =
      .ok (Cache.raw.codes[11]!, { bytes := artifactBytes, pos := 2335, limit := 16006 }) := by
  exact code11_decoded_parts

#print axioms code11_decoded

end Project.TinyGpt2Hidden.Artifact
