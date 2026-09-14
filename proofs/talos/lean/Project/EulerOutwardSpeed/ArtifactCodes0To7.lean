import Project.EulerOutwardSpeed.ArtifactByteLookup
import Project.EulerOutwardSpeed.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.EulerOutwardSpeed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem code0_decoded :
    code { bytes := artifactBytes, pos := 488, limit := 4936 } =
      .ok (Cache.raw.codes[0]!, { bytes := artifactBytes, pos := 530, limit := 4936 }) := by
  cbv

#print axioms code0_decoded

theorem code1_decoded :
    code { bytes := artifactBytes, pos := 530, limit := 4936 } =
      .ok (Cache.raw.codes[1]!, { bytes := artifactBytes, pos := 553, limit := 4936 }) := by
  cbv

#print axioms code1_decoded

theorem code2_decoded :
    code { bytes := artifactBytes, pos := 553, limit := 4936 } =
      .ok (Cache.raw.codes[2]!, { bytes := artifactBytes, pos := 590, limit := 4936 }) := by
  cbv

#print axioms code2_decoded

theorem code3_decoded :
    code { bytes := artifactBytes, pos := 590, limit := 4936 } =
      .ok (Cache.raw.codes[3]!, { bytes := artifactBytes, pos := 718, limit := 4936 }) := by
  cbv

#print axioms code3_decoded

theorem code4_decoded :
    code { bytes := artifactBytes, pos := 718, limit := 4936 } =
      .ok (Cache.raw.codes[4]!, { bytes := artifactBytes, pos := 760, limit := 4936 }) := by
  cbv

#print axioms code4_decoded

theorem code5_decoded :
    code { bytes := artifactBytes, pos := 760, limit := 4936 } =
      .ok (Cache.raw.codes[5]!, { bytes := artifactBytes, pos := 783, limit := 4936 }) := by
  cbv

#print axioms code5_decoded

theorem code6_decoded :
    code { bytes := artifactBytes, pos := 783, limit := 4936 } =
      .ok (Cache.raw.codes[6]!, { bytes := artifactBytes, pos := 820, limit := 4936 }) := by
  cbv

#print axioms code6_decoded

theorem code7_decoded :
    code { bytes := artifactBytes, pos := 820, limit := 4936 } =
      .ok (Cache.raw.codes[7]!, { bytes := artifactBytes, pos := 842, limit := 4936 }) := by
  cbv

#print axioms code7_decoded

end Project.EulerOutwardSpeed.Artifact
