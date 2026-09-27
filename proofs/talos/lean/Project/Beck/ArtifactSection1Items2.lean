import Project.Beck.ArtifactByteLookup
import Project.Beck.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Beck.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type32_decoded :
    funcType { bytes := artifactBytes, pos := 350, limit := 419 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 366, limit := 419 }) := by cbv

#print axioms type32_decoded

theorem type33_decoded :
    funcType { bytes := artifactBytes, pos := 366, limit := 419 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 381, limit := 419 }) := by cbv

#print axioms type33_decoded

theorem type34_decoded :
    funcType { bytes := artifactBytes, pos := 381, limit := 419 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 397, limit := 419 }) := by cbv

#print axioms type34_decoded

theorem type35_decoded :
    funcType { bytes := artifactBytes, pos := 397, limit := 419 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 402, limit := 419 }) := by cbv

#print axioms type35_decoded

theorem type36_decoded :
    funcType { bytes := artifactBytes, pos := 402, limit := 419 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 407, limit := 419 }) := by cbv

#print axioms type36_decoded

theorem type37_decoded :
    funcType { bytes := artifactBytes, pos := 407, limit := 419 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 410, limit := 419 }) := by cbv

#print axioms type37_decoded

theorem type38_decoded :
    funcType { bytes := artifactBytes, pos := 410, limit := 419 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 415, limit := 419 }) := by cbv

#print axioms type38_decoded

theorem type39_decoded :
    funcType { bytes := artifactBytes, pos := 415, limit := 419 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 419, limit := 419 }) := by cbv

#print axioms type39_decoded


end Project.Beck.Artifact
