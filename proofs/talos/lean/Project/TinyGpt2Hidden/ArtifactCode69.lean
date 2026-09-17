import Project.TinyGpt2Hidden.ArtifactBody69
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code69_decoded :
    code { bytes := artifactBytes, pos := 8354, limit := 16006 } =
      .ok (Cache.raw.codes[69]!, { bytes := artifactBytes, pos := 9325, limit := 16006 }) := by
  exact code69_decoded_parts

#print axioms code69_decoded

end Project.TinyGpt2Hidden.Artifact
