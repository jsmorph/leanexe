import Project.TinyGpt2Hidden.ArtifactBody44
import Project.TinyGpt2Hidden.ArtifactBody45
import Project.TinyGpt2Hidden.ArtifactBody46
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code44_decoded :
    code { bytes := artifactBytes, pos := 5477, limit := 16006 } =
      .ok (Cache.raw.codes[44]!, { bytes := artifactBytes, pos := 5823, limit := 16006 }) := by
  exact code44_decoded_parts

#print axioms code44_decoded

theorem code45_decoded :
    code { bytes := artifactBytes, pos := 5823, limit := 16006 } =
      .ok (Cache.raw.codes[45]!, { bytes := artifactBytes, pos := 5872, limit := 16006 }) := by
  exact code45_decoded_parts

#print axioms code45_decoded

theorem code46_decoded :
    code { bytes := artifactBytes, pos := 5872, limit := 16006 } =
      .ok (Cache.raw.codes[46]!, { bytes := artifactBytes, pos := 6062, limit := 16006 }) := by
  exact code46_decoded_parts

#print axioms code46_decoded

theorem code47_decoded :
    code { bytes := artifactBytes, pos := 6062, limit := 16006 } =
      .ok (Cache.raw.codes[47]!, { bytes := artifactBytes, pos := 6073, limit := 16006 }) := by
  cbv

#print axioms code47_decoded

end Project.TinyGpt2Hidden.Artifact
