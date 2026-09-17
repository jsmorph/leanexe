import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code71_decoded :
    code { bytes := artifactBytes, pos := 9337, limit := 16006 } =
      .ok (Cache.raw.codes[71]!, { bytes := artifactBytes, pos := 9349, limit := 16006 }) := by
  cbv

#print axioms code71_decoded

end Project.TinyGpt2Hidden.Artifact
