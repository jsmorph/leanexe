import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code58_decoded :
    code { bytes := artifactBytes, pos := 7739, limit := 16006 } =
      .ok (Cache.raw.codes[58]!, { bytes := artifactBytes, pos := 7751, limit := 16006 }) := by
  cbv

#print axioms code58_decoded

end Project.TinyGpt2Hidden.Artifact
