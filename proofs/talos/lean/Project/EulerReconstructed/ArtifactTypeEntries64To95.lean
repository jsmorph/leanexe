import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.EulerReconstructed.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type64_decoded :
    funcType { bytes := artifactBytes, pos := 522, limit := 1622 } =
      .ok (Cache.raw.types[64]!, { bytes := artifactBytes, pos := 530, limit := 1622 }) := by cbv

theorem type65_decoded :
    funcType { bytes := artifactBytes, pos := 530, limit := 1622 } =
      .ok (Cache.raw.types[65]!, { bytes := artifactBytes, pos := 550, limit := 1622 }) := by cbv

theorem type66_decoded :
    funcType { bytes := artifactBytes, pos := 550, limit := 1622 } =
      .ok (Cache.raw.types[66]!, { bytes := artifactBytes, pos := 559, limit := 1622 }) := by cbv

theorem type67_decoded :
    funcType { bytes := artifactBytes, pos := 559, limit := 1622 } =
      .ok (Cache.raw.types[67]!, { bytes := artifactBytes, pos := 576, limit := 1622 }) := by cbv

theorem type68_decoded :
    funcType { bytes := artifactBytes, pos := 576, limit := 1622 } =
      .ok (Cache.raw.types[68]!, { bytes := artifactBytes, pos := 588, limit := 1622 }) := by cbv

theorem type69_decoded :
    funcType { bytes := artifactBytes, pos := 588, limit := 1622 } =
      .ok (Cache.raw.types[69]!, { bytes := artifactBytes, pos := 603, limit := 1622 }) := by cbv

theorem type70_decoded :
    funcType { bytes := artifactBytes, pos := 603, limit := 1622 } =
      .ok (Cache.raw.types[70]!, { bytes := artifactBytes, pos := 616, limit := 1622 }) := by cbv

theorem type71_decoded :
    funcType { bytes := artifactBytes, pos := 616, limit := 1622 } =
      .ok (Cache.raw.types[71]!, { bytes := artifactBytes, pos := 638, limit := 1622 }) := by cbv

theorem type72_decoded :
    funcType { bytes := artifactBytes, pos := 638, limit := 1622 } =
      .ok (Cache.raw.types[72]!, { bytes := artifactBytes, pos := 652, limit := 1622 }) := by cbv

theorem type73_decoded :
    funcType { bytes := artifactBytes, pos := 652, limit := 1622 } =
      .ok (Cache.raw.types[73]!, { bytes := artifactBytes, pos := 675, limit := 1622 }) := by cbv

theorem type74_decoded :
    funcType { bytes := artifactBytes, pos := 675, limit := 1622 } =
      .ok (Cache.raw.types[74]!, { bytes := artifactBytes, pos := 687, limit := 1622 }) := by cbv

theorem type75_decoded :
    funcType { bytes := artifactBytes, pos := 687, limit := 1622 } =
      .ok (Cache.raw.types[75]!, { bytes := artifactBytes, pos := 713, limit := 1622 }) := by cbv

theorem type76_decoded :
    funcType { bytes := artifactBytes, pos := 713, limit := 1622 } =
      .ok (Cache.raw.types[76]!, { bytes := artifactBytes, pos := 724, limit := 1622 }) := by cbv

theorem type77_decoded :
    funcType { bytes := artifactBytes, pos := 724, limit := 1622 } =
      .ok (Cache.raw.types[77]!, { bytes := artifactBytes, pos := 739, limit := 1622 }) := by cbv

theorem type78_decoded :
    funcType { bytes := artifactBytes, pos := 739, limit := 1622 } =
      .ok (Cache.raw.types[78]!, { bytes := artifactBytes, pos := 751, limit := 1622 }) := by cbv

theorem type79_decoded :
    funcType { bytes := artifactBytes, pos := 751, limit := 1622 } =
      .ok (Cache.raw.types[79]!, { bytes := artifactBytes, pos := 763, limit := 1622 }) := by cbv

theorem type80_decoded :
    funcType { bytes := artifactBytes, pos := 763, limit := 1622 } =
      .ok (Cache.raw.types[80]!, { bytes := artifactBytes, pos := 768, limit := 1622 }) := by cbv

theorem type81_decoded :
    funcType { bytes := artifactBytes, pos := 768, limit := 1622 } =
      .ok (Cache.raw.types[81]!, { bytes := artifactBytes, pos := 773, limit := 1622 }) := by cbv

theorem type82_decoded :
    funcType { bytes := artifactBytes, pos := 773, limit := 1622 } =
      .ok (Cache.raw.types[82]!, { bytes := artifactBytes, pos := 778, limit := 1622 }) := by cbv

theorem type83_decoded :
    funcType { bytes := artifactBytes, pos := 778, limit := 1622 } =
      .ok (Cache.raw.types[83]!, { bytes := artifactBytes, pos := 783, limit := 1622 }) := by cbv

theorem type84_decoded :
    funcType { bytes := artifactBytes, pos := 783, limit := 1622 } =
      .ok (Cache.raw.types[84]!, { bytes := artifactBytes, pos := 793, limit := 1622 }) := by cbv

theorem type85_decoded :
    funcType { bytes := artifactBytes, pos := 793, limit := 1622 } =
      .ok (Cache.raw.types[85]!, { bytes := artifactBytes, pos := 803, limit := 1622 }) := by cbv

theorem type86_decoded :
    funcType { bytes := artifactBytes, pos := 803, limit := 1622 } =
      .ok (Cache.raw.types[86]!, { bytes := artifactBytes, pos := 815, limit := 1622 }) := by cbv

theorem type87_decoded :
    funcType { bytes := artifactBytes, pos := 815, limit := 1622 } =
      .ok (Cache.raw.types[87]!, { bytes := artifactBytes, pos := 827, limit := 1622 }) := by cbv

theorem type88_decoded :
    funcType { bytes := artifactBytes, pos := 827, limit := 1622 } =
      .ok (Cache.raw.types[88]!, { bytes := artifactBytes, pos := 839, limit := 1622 }) := by cbv

theorem type89_decoded :
    funcType { bytes := artifactBytes, pos := 839, limit := 1622 } =
      .ok (Cache.raw.types[89]!, { bytes := artifactBytes, pos := 851, limit := 1622 }) := by cbv

theorem type90_decoded :
    funcType { bytes := artifactBytes, pos := 851, limit := 1622 } =
      .ok (Cache.raw.types[90]!, { bytes := artifactBytes, pos := 857, limit := 1622 }) := by cbv

theorem type91_decoded :
    funcType { bytes := artifactBytes, pos := 857, limit := 1622 } =
      .ok (Cache.raw.types[91]!, { bytes := artifactBytes, pos := 863, limit := 1622 }) := by cbv

theorem type92_decoded :
    funcType { bytes := artifactBytes, pos := 863, limit := 1622 } =
      .ok (Cache.raw.types[92]!, { bytes := artifactBytes, pos := 872, limit := 1622 }) := by cbv

theorem type93_decoded :
    funcType { bytes := artifactBytes, pos := 872, limit := 1622 } =
      .ok (Cache.raw.types[93]!, { bytes := artifactBytes, pos := 889, limit := 1622 }) := by cbv

theorem type94_decoded :
    funcType { bytes := artifactBytes, pos := 889, limit := 1622 } =
      .ok (Cache.raw.types[94]!, { bytes := artifactBytes, pos := 899, limit := 1622 }) := by cbv

theorem type95_decoded :
    funcType { bytes := artifactBytes, pos := 899, limit := 1622 } =
      .ok (Cache.raw.types[95]!, { bytes := artifactBytes, pos := 909, limit := 1622 }) := by cbv


#print axioms type95_decoded

end Project.EulerReconstructed.Artifact
