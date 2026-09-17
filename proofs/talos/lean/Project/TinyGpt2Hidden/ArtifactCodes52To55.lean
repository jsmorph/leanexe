import Project.TinyGpt2Hidden.ArtifactBody52
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code52_decoded :
    code { bytes := artifactBytes, pos := 6169, limit := 16006 } =
      .ok (Cache.raw.codes[52]!, { bytes := artifactBytes, pos := 6627, limit := 16006 }) := by
  exact code52_decoded_parts

#print axioms code52_decoded

theorem code53_decoded :
    code { bytes := artifactBytes, pos := 6627, limit := 16006 } =
      .ok (Cache.raw.codes[53]!, { bytes := artifactBytes, pos := 6639, limit := 16006 }) := by
  cbv

#print axioms code53_decoded

theorem code54_decoded :
    code { bytes := artifactBytes, pos := 6639, limit := 16006 } =
      .ok (Cache.raw.codes[54]!, { bytes := artifactBytes, pos := 6651, limit := 16006 }) := by
  cbv

#print axioms code54_decoded

theorem code55_decoded :
    code { bytes := artifactBytes, pos := 6651, limit := 16006 } =
      .ok (Cache.raw.codes[55]!, { bytes := artifactBytes, pos := 6663, limit := 16006 }) := by
  cbv

#print axioms code55_decoded

end Project.TinyGpt2Hidden.Artifact
