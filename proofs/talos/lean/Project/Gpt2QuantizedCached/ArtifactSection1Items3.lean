import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type48_decoded :
    funcType { bytes := artifactBytes, pos := 349, limit := 534 } =
      .ok (Cache.raw.types[48]!, { bytes := artifactBytes, pos := 354, limit := 534 }) := by cbv

theorem type49_decoded :
    funcType { bytes := artifactBytes, pos := 354, limit := 534 } =
      .ok (Cache.raw.types[49]!, { bytes := artifactBytes, pos := 363, limit := 534 }) := by cbv

theorem type50_decoded :
    funcType { bytes := artifactBytes, pos := 363, limit := 534 } =
      .ok (Cache.raw.types[50]!, { bytes := artifactBytes, pos := 377, limit := 534 }) := by cbv

theorem type51_decoded :
    funcType { bytes := artifactBytes, pos := 377, limit := 534 } =
      .ok (Cache.raw.types[51]!, { bytes := artifactBytes, pos := 389, limit := 534 }) := by cbv

theorem type52_decoded :
    funcType { bytes := artifactBytes, pos := 389, limit := 534 } =
      .ok (Cache.raw.types[52]!, { bytes := artifactBytes, pos := 394, limit := 534 }) := by cbv

theorem type53_decoded :
    funcType { bytes := artifactBytes, pos := 394, limit := 534 } =
      .ok (Cache.raw.types[53]!, { bytes := artifactBytes, pos := 403, limit := 534 }) := by cbv

theorem type54_decoded :
    funcType { bytes := artifactBytes, pos := 403, limit := 534 } =
      .ok (Cache.raw.types[54]!, { bytes := artifactBytes, pos := 424, limit := 534 }) := by cbv

theorem type55_decoded :
    funcType { bytes := artifactBytes, pos := 424, limit := 534 } =
      .ok (Cache.raw.types[55]!, { bytes := artifactBytes, pos := 435, limit := 534 }) := by cbv

theorem type56_decoded :
    funcType { bytes := artifactBytes, pos := 435, limit := 534 } =
      .ok (Cache.raw.types[56]!, { bytes := artifactBytes, pos := 448, limit := 534 }) := by cbv

theorem type57_decoded :
    funcType { bytes := artifactBytes, pos := 448, limit := 534 } =
      .ok (Cache.raw.types[57]!, { bytes := artifactBytes, pos := 461, limit := 534 }) := by cbv

theorem type58_decoded :
    funcType { bytes := artifactBytes, pos := 461, limit := 534 } =
      .ok (Cache.raw.types[58]!, { bytes := artifactBytes, pos := 479, limit := 534 }) := by cbv

theorem type59_decoded :
    funcType { bytes := artifactBytes, pos := 479, limit := 534 } =
      .ok (Cache.raw.types[59]!, { bytes := artifactBytes, pos := 497, limit := 534 }) := by cbv

theorem type60_decoded :
    funcType { bytes := artifactBytes, pos := 497, limit := 534 } =
      .ok (Cache.raw.types[60]!, { bytes := artifactBytes, pos := 503, limit := 534 }) := by cbv

theorem type61_decoded :
    funcType { bytes := artifactBytes, pos := 503, limit := 534 } =
      .ok (Cache.raw.types[61]!, { bytes := artifactBytes, pos := 517, limit := 534 }) := by cbv

theorem type62_decoded :
    funcType { bytes := artifactBytes, pos := 517, limit := 534 } =
      .ok (Cache.raw.types[62]!, { bytes := artifactBytes, pos := 522, limit := 534 }) := by cbv

theorem type63_decoded :
    funcType { bytes := artifactBytes, pos := 522, limit := 534 } =
      .ok (Cache.raw.types[63]!, { bytes := artifactBytes, pos := 525, limit := 534 }) := by cbv


end Project.Gpt2QuantizedCached.Artifact
