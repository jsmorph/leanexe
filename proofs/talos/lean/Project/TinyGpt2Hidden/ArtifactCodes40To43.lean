import Project.TinyGpt2Hidden.ArtifactBody40
import Project.TinyGpt2Hidden.ArtifactBody41
import Project.TinyGpt2Hidden.ArtifactBody42
import Project.TinyGpt2Hidden.ArtifactBody43
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code40_decoded :
    code { bytes := artifactBytes, pos := 5290, limit := 16006 } =
      .ok (Cache.raw.codes[40]!, { bytes := artifactBytes, pos := 5380, limit := 16006 }) := by
  exact code40_decoded_parts

#print axioms code40_decoded

theorem code41_decoded :
    code { bytes := artifactBytes, pos := 5380, limit := 16006 } =
      .ok (Cache.raw.codes[41]!, { bytes := artifactBytes, pos := 5420, limit := 16006 }) := by
  exact code41_decoded_parts

#print axioms code41_decoded

theorem code42_decoded :
    code { bytes := artifactBytes, pos := 5420, limit := 16006 } =
      .ok (Cache.raw.codes[42]!, { bytes := artifactBytes, pos := 5449, limit := 16006 }) := by
  exact code42_decoded_parts

#print axioms code42_decoded

theorem code43_decoded :
    code { bytes := artifactBytes, pos := 5449, limit := 16006 } =
      .ok (Cache.raw.codes[43]!, { bytes := artifactBytes, pos := 5477, limit := 16006 }) := by
  exact code43_decoded_parts

#print axioms code43_decoded

end Project.TinyGpt2Hidden.Artifact
