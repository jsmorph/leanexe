import Project.TinyGpt2Hidden.ArtifactBody68
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code68_decoded :
    code { bytes := artifactBytes, pos := 8241, limit := 16006 } =
      .ok (Cache.raw.codes[68]!, { bytes := artifactBytes, pos := 8354, limit := 16006 }) := by
  exact code68_decoded_parts

#print axioms code68_decoded

end Project.TinyGpt2Hidden.Artifact
