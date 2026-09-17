import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 1061, limit := 16006 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 1072, limit := 16006 }) := by
  cbv

#print axioms code0_decoded

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 1072, limit := 16006 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 1083, limit := 16006 }) := by
  cbv

#print axioms code1_decoded

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 1083, limit := 16006 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 1094, limit := 16006 }) := by
  cbv

#print axioms code2_decoded

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 1094, limit := 16006 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 1105, limit := 16006 }) := by
  cbv

#print axioms code3_decoded

end Project.TinyGpt2Hidden.Artifact
