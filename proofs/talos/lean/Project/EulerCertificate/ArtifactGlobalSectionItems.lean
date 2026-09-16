import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem global0_decoded :
    global { bytes := artifactBytes, pos := 2846, limit := 2877 } =
      .ok (Cache.raw.globals[0]!, { bytes := artifactBytes, pos := 2852, limit := 2877 }) := by cbv

#print axioms global0_decoded

theorem global1_decoded :
    global { bytes := artifactBytes, pos := 2852, limit := 2877 } =
      .ok (Cache.raw.globals[1]!, { bytes := artifactBytes, pos := 2857, limit := 2877 }) := by cbv

#print axioms global1_decoded

theorem global2_decoded :
    global { bytes := artifactBytes, pos := 2857, limit := 2877 } =
      .ok (Cache.raw.globals[2]!, { bytes := artifactBytes, pos := 2862, limit := 2877 }) := by cbv

#print axioms global2_decoded

theorem global3_decoded :
    global { bytes := artifactBytes, pos := 2862, limit := 2877 } =
      .ok (Cache.raw.globals[3]!, { bytes := artifactBytes, pos := 2867, limit := 2877 }) := by cbv

#print axioms global3_decoded

theorem global4_decoded :
    global { bytes := artifactBytes, pos := 2867, limit := 2877 } =
      .ok (Cache.raw.globals[4]!, { bytes := artifactBytes, pos := 2872, limit := 2877 }) := by cbv

#print axioms global4_decoded

theorem global5_decoded :
    global { bytes := artifactBytes, pos := 2872, limit := 2877 } =
      .ok (Cache.raw.globals[5]!, { bytes := artifactBytes, pos := 2877, limit := 2877 }) := by cbv

#print axioms global5_decoded

end Project.EulerCertificate.Artifact
