import Project.TinyGpt2Hidden.ArtifactBody64
import Project.TinyGpt2Hidden.ArtifactBody65
import Project.TinyGpt2Hidden.ArtifactBody66
import Project.TinyGpt2Hidden.ArtifactBody67
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code64_decoded :
    code { bytes := artifactBytes, pos := 8038, limit := 16006 } =
      .ok (Cache.raw.codes[64]!, { bytes := artifactBytes, pos := 8114, limit := 16006 }) := by
  exact code64_decoded_parts

#print axioms code64_decoded

theorem code65_decoded :
    code { bytes := artifactBytes, pos := 8114, limit := 16006 } =
      .ok (Cache.raw.codes[65]!, { bytes := artifactBytes, pos := 8183, limit := 16006 }) := by
  exact code65_decoded_parts

#print axioms code65_decoded

theorem code66_decoded :
    code { bytes := artifactBytes, pos := 8183, limit := 16006 } =
      .ok (Cache.raw.codes[66]!, { bytes := artifactBytes, pos := 8212, limit := 16006 }) := by
  exact code66_decoded_parts

#print axioms code66_decoded

theorem code67_decoded :
    code { bytes := artifactBytes, pos := 8212, limit := 16006 } =
      .ok (Cache.raw.codes[67]!, { bytes := artifactBytes, pos := 8241, limit := 16006 }) := by
  exact code67_decoded_parts

#print axioms code67_decoded

end Project.TinyGpt2Hidden.Artifact
