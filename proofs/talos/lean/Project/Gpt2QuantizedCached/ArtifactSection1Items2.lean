import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type32_decoded :
    funcType { bytes := artifactBytes, pos := 177, limit := 534 } =
      .ok (Cache.raw.types[32]!, { bytes := artifactBytes, pos := 185, limit := 534 }) := by cbv

#print axioms type32_decoded

theorem type33_decoded :
    funcType { bytes := artifactBytes, pos := 185, limit := 534 } =
      .ok (Cache.raw.types[33]!, { bytes := artifactBytes, pos := 194, limit := 534 }) := by cbv

#print axioms type33_decoded

theorem type34_decoded :
    funcType { bytes := artifactBytes, pos := 194, limit := 534 } =
      .ok (Cache.raw.types[34]!, { bytes := artifactBytes, pos := 209, limit := 534 }) := by cbv

#print axioms type34_decoded

theorem type35_decoded :
    funcType { bytes := artifactBytes, pos := 209, limit := 534 } =
      .ok (Cache.raw.types[35]!, { bytes := artifactBytes, pos := 218, limit := 534 }) := by cbv

#print axioms type35_decoded

theorem type36_decoded :
    funcType { bytes := artifactBytes, pos := 218, limit := 534 } =
      .ok (Cache.raw.types[36]!, { bytes := artifactBytes, pos := 224, limit := 534 }) := by cbv

#print axioms type36_decoded

theorem type37_decoded :
    funcType { bytes := artifactBytes, pos := 224, limit := 534 } =
      .ok (Cache.raw.types[37]!, { bytes := artifactBytes, pos := 238, limit := 534 }) := by cbv

#print axioms type37_decoded

theorem type38_decoded :
    funcType { bytes := artifactBytes, pos := 238, limit := 534 } =
      .ok (Cache.raw.types[38]!, { bytes := artifactBytes, pos := 251, limit := 534 }) := by cbv

#print axioms type38_decoded

theorem type39_decoded :
    funcType { bytes := artifactBytes, pos := 251, limit := 534 } =
      .ok (Cache.raw.types[39]!, { bytes := artifactBytes, pos := 263, limit := 534 }) := by cbv

#print axioms type39_decoded

theorem type40_decoded :
    funcType { bytes := artifactBytes, pos := 263, limit := 534 } =
      .ok (Cache.raw.types[40]!, { bytes := artifactBytes, pos := 270, limit := 534 }) := by cbv

#print axioms type40_decoded

theorem type41_decoded :
    funcType { bytes := artifactBytes, pos := 270, limit := 534 } =
      .ok (Cache.raw.types[41]!, { bytes := artifactBytes, pos := 282, limit := 534 }) := by cbv

#print axioms type41_decoded

theorem type42_decoded :
    funcType { bytes := artifactBytes, pos := 282, limit := 534 } =
      .ok (Cache.raw.types[42]!, { bytes := artifactBytes, pos := 301, limit := 534 }) := by cbv

#print axioms type42_decoded

theorem type43_decoded :
    funcType { bytes := artifactBytes, pos := 301, limit := 534 } =
      .ok (Cache.raw.types[43]!, { bytes := artifactBytes, pos := 315, limit := 534 }) := by cbv

#print axioms type43_decoded

theorem type44_decoded :
    funcType { bytes := artifactBytes, pos := 315, limit := 534 } =
      .ok (Cache.raw.types[44]!, { bytes := artifactBytes, pos := 329, limit := 534 }) := by cbv

#print axioms type44_decoded

theorem type45_decoded :
    funcType { bytes := artifactBytes, pos := 329, limit := 534 } =
      .ok (Cache.raw.types[45]!, { bytes := artifactBytes, pos := 335, limit := 534 }) := by cbv

#print axioms type45_decoded

theorem type46_decoded :
    funcType { bytes := artifactBytes, pos := 335, limit := 534 } =
      .ok (Cache.raw.types[46]!, { bytes := artifactBytes, pos := 344, limit := 534 }) := by cbv

#print axioms type46_decoded

theorem type47_decoded :
    funcType { bytes := artifactBytes, pos := 344, limit := 534 } =
      .ok (Cache.raw.types[47]!, { bytes := artifactBytes, pos := 349, limit := 534 }) := by cbv

#print axioms type47_decoded


end Project.Gpt2QuantizedCached.Artifact
