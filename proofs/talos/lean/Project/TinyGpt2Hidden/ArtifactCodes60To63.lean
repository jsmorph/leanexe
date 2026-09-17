import Project.TinyGpt2Hidden.ArtifactBody60
import Project.TinyGpt2Hidden.ArtifactBody61
import Project.TinyGpt2Hidden.ArtifactBody62
import Project.TinyGpt2Hidden.ArtifactBody63
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code60_decoded :
    code { bytes := artifactBytes, pos := 7774, limit := 16006 } =
      .ok (Cache.raw.codes[60]!, { bytes := artifactBytes, pos := 7811, limit := 16006 }) := by
  exact code60_decoded_parts

#print axioms code60_decoded

theorem code61_decoded :
    code { bytes := artifactBytes, pos := 7811, limit := 16006 } =
      .ok (Cache.raw.codes[61]!, { bytes := artifactBytes, pos := 7840, limit := 16006 }) := by
  exact code61_decoded_parts

#print axioms code61_decoded

theorem code62_decoded :
    code { bytes := artifactBytes, pos := 7840, limit := 16006 } =
      .ok (Cache.raw.codes[62]!, { bytes := artifactBytes, pos := 7913, limit := 16006 }) := by
  exact code62_decoded_parts

#print axioms code62_decoded

theorem code63_decoded :
    code { bytes := artifactBytes, pos := 7913, limit := 16006 } =
      .ok (Cache.raw.codes[63]!, { bytes := artifactBytes, pos := 8038, limit := 16006 }) := by
  exact code63_decoded_parts

#print axioms code63_decoded

end Project.TinyGpt2Hidden.Artifact
