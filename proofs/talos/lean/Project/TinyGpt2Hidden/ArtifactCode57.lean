import Project.TinyGpt2Hidden.ArtifactBody57
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code57_decoded :
    code { bytes := artifactBytes, pos := 6675, limit := 16006 } =
      .ok (Cache.raw.codes[57]!, { bytes := artifactBytes, pos := 7739, limit := 16006 }) := by
  exact code57_decoded_parts

#print axioms code57_decoded

end Project.TinyGpt2Hidden.Artifact
