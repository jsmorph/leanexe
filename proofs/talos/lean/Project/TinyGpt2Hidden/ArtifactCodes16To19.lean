import Project.TinyGpt2Hidden.ArtifactBody17
import Project.TinyGpt2Hidden.ArtifactBody19
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code16_decoded :
    code { bytes := artifactBytes, pos := 2620, limit := 16006 } =
      .ok (Cache.raw.codes[16]!, { bytes := artifactBytes, pos := 2631, limit := 16006 }) := by
  cbv

#print axioms code16_decoded

theorem code17_decoded :
    code { bytes := artifactBytes, pos := 2631, limit := 16006 } =
      .ok (Cache.raw.codes[17]!, { bytes := artifactBytes, pos := 2872, limit := 16006 }) := by
  exact code17_decoded_parts

#print axioms code17_decoded

theorem code18_decoded :
    code { bytes := artifactBytes, pos := 2872, limit := 16006 } =
      .ok (Cache.raw.codes[18]!, { bytes := artifactBytes, pos := 2884, limit := 16006 }) := by
  cbv

#print axioms code18_decoded

theorem code19_decoded :
    code { bytes := artifactBytes, pos := 2884, limit := 16006 } =
      .ok (Cache.raw.codes[19]!, { bytes := artifactBytes, pos := 2913, limit := 16006 }) := by
  exact code19_decoded_parts

#print axioms code19_decoded

end Project.TinyGpt2Hidden.Artifact
