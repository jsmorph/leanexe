import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactFunctionSectionItems

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem functionTypeIndices_tail195_decoded :
    Internal.vectorLoop Leb.u32 0 { bytes := artifactBytes, pos := 2838, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 195, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by rfl

theorem functionTypeIndices_tail194_decoded :
    Internal.vectorLoop Leb.u32 1 { bytes := artifactBytes, pos := 2836, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 194, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex194_decoded functionTypeIndices_tail195_decoded

theorem functionTypeIndices_tail193_decoded :
    Internal.vectorLoop Leb.u32 2 { bytes := artifactBytes, pos := 2834, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 193, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex193_decoded functionTypeIndices_tail194_decoded

theorem functionTypeIndices_tail192_decoded :
    Internal.vectorLoop Leb.u32 3 { bytes := artifactBytes, pos := 2832, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 192, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex192_decoded functionTypeIndices_tail193_decoded

theorem functionTypeIndices_tail191_decoded :
    Internal.vectorLoop Leb.u32 4 { bytes := artifactBytes, pos := 2830, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 191, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex191_decoded functionTypeIndices_tail192_decoded

theorem functionTypeIndices_tail190_decoded :
    Internal.vectorLoop Leb.u32 5 { bytes := artifactBytes, pos := 2828, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 190, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex190_decoded functionTypeIndices_tail191_decoded

theorem functionTypeIndices_tail189_decoded :
    Internal.vectorLoop Leb.u32 6 { bytes := artifactBytes, pos := 2826, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 189, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex189_decoded functionTypeIndices_tail190_decoded

theorem functionTypeIndices_tail188_decoded :
    Internal.vectorLoop Leb.u32 7 { bytes := artifactBytes, pos := 2824, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 188, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex188_decoded functionTypeIndices_tail189_decoded

theorem functionTypeIndices_tail187_decoded :
    Internal.vectorLoop Leb.u32 8 { bytes := artifactBytes, pos := 2822, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 187, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex187_decoded functionTypeIndices_tail188_decoded

theorem functionTypeIndices_tail186_decoded :
    Internal.vectorLoop Leb.u32 9 { bytes := artifactBytes, pos := 2820, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 186, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex186_decoded functionTypeIndices_tail187_decoded

theorem functionTypeIndices_tail185_decoded :
    Internal.vectorLoop Leb.u32 10 { bytes := artifactBytes, pos := 2818, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 185, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex185_decoded functionTypeIndices_tail186_decoded

theorem functionTypeIndices_tail184_decoded :
    Internal.vectorLoop Leb.u32 11 { bytes := artifactBytes, pos := 2816, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 184, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex184_decoded functionTypeIndices_tail185_decoded

theorem functionTypeIndices_tail183_decoded :
    Internal.vectorLoop Leb.u32 12 { bytes := artifactBytes, pos := 2814, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 183, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex183_decoded functionTypeIndices_tail184_decoded

theorem functionTypeIndices_tail182_decoded :
    Internal.vectorLoop Leb.u32 13 { bytes := artifactBytes, pos := 2812, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 182, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex182_decoded functionTypeIndices_tail183_decoded

theorem functionTypeIndices_tail181_decoded :
    Internal.vectorLoop Leb.u32 14 { bytes := artifactBytes, pos := 2810, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 181, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex181_decoded functionTypeIndices_tail182_decoded

theorem functionTypeIndices_tail180_decoded :
    Internal.vectorLoop Leb.u32 15 { bytes := artifactBytes, pos := 2808, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 180, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex180_decoded functionTypeIndices_tail181_decoded


theorem functionTypeIndices_tail179_decoded :
    Internal.vectorLoop Leb.u32 16 { bytes := artifactBytes, pos := 2806, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 179, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex179_decoded functionTypeIndices_tail180_decoded

theorem functionTypeIndices_tail178_decoded :
    Internal.vectorLoop Leb.u32 17 { bytes := artifactBytes, pos := 2804, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 178, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex178_decoded functionTypeIndices_tail179_decoded

theorem functionTypeIndices_tail177_decoded :
    Internal.vectorLoop Leb.u32 18 { bytes := artifactBytes, pos := 2802, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 177, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex177_decoded functionTypeIndices_tail178_decoded

theorem functionTypeIndices_tail176_decoded :
    Internal.vectorLoop Leb.u32 19 { bytes := artifactBytes, pos := 2800, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 176, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex176_decoded functionTypeIndices_tail177_decoded

theorem functionTypeIndices_tail175_decoded :
    Internal.vectorLoop Leb.u32 20 { bytes := artifactBytes, pos := 2798, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 175, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex175_decoded functionTypeIndices_tail176_decoded

theorem functionTypeIndices_tail174_decoded :
    Internal.vectorLoop Leb.u32 21 { bytes := artifactBytes, pos := 2796, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 174, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex174_decoded functionTypeIndices_tail175_decoded

theorem functionTypeIndices_tail173_decoded :
    Internal.vectorLoop Leb.u32 22 { bytes := artifactBytes, pos := 2794, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 173, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex173_decoded functionTypeIndices_tail174_decoded

theorem functionTypeIndices_tail172_decoded :
    Internal.vectorLoop Leb.u32 23 { bytes := artifactBytes, pos := 2792, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 172, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex172_decoded functionTypeIndices_tail173_decoded

theorem functionTypeIndices_tail171_decoded :
    Internal.vectorLoop Leb.u32 24 { bytes := artifactBytes, pos := 2790, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 171, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex171_decoded functionTypeIndices_tail172_decoded

theorem functionTypeIndices_tail170_decoded :
    Internal.vectorLoop Leb.u32 25 { bytes := artifactBytes, pos := 2788, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 170, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex170_decoded functionTypeIndices_tail171_decoded

theorem functionTypeIndices_tail169_decoded :
    Internal.vectorLoop Leb.u32 26 { bytes := artifactBytes, pos := 2786, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 169, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex169_decoded functionTypeIndices_tail170_decoded

theorem functionTypeIndices_tail168_decoded :
    Internal.vectorLoop Leb.u32 27 { bytes := artifactBytes, pos := 2784, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 168, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex168_decoded functionTypeIndices_tail169_decoded

theorem functionTypeIndices_tail167_decoded :
    Internal.vectorLoop Leb.u32 28 { bytes := artifactBytes, pos := 2782, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 167, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex167_decoded functionTypeIndices_tail168_decoded

theorem functionTypeIndices_tail166_decoded :
    Internal.vectorLoop Leb.u32 29 { bytes := artifactBytes, pos := 2780, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 166, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex166_decoded functionTypeIndices_tail167_decoded

theorem functionTypeIndices_tail165_decoded :
    Internal.vectorLoop Leb.u32 30 { bytes := artifactBytes, pos := 2778, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 165, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex165_decoded functionTypeIndices_tail166_decoded

theorem functionTypeIndices_tail164_decoded :
    Internal.vectorLoop Leb.u32 31 { bytes := artifactBytes, pos := 2776, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 164, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex164_decoded functionTypeIndices_tail165_decoded


theorem functionTypeIndices_tail163_decoded :
    Internal.vectorLoop Leb.u32 32 { bytes := artifactBytes, pos := 2774, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 163, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex163_decoded functionTypeIndices_tail164_decoded

theorem functionTypeIndices_tail162_decoded :
    Internal.vectorLoop Leb.u32 33 { bytes := artifactBytes, pos := 2772, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 162, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex162_decoded functionTypeIndices_tail163_decoded

theorem functionTypeIndices_tail161_decoded :
    Internal.vectorLoop Leb.u32 34 { bytes := artifactBytes, pos := 2770, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 161, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex161_decoded functionTypeIndices_tail162_decoded

theorem functionTypeIndices_tail160_decoded :
    Internal.vectorLoop Leb.u32 35 { bytes := artifactBytes, pos := 2768, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 160, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex160_decoded functionTypeIndices_tail161_decoded

theorem functionTypeIndices_tail159_decoded :
    Internal.vectorLoop Leb.u32 36 { bytes := artifactBytes, pos := 2766, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 159, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex159_decoded functionTypeIndices_tail160_decoded

theorem functionTypeIndices_tail158_decoded :
    Internal.vectorLoop Leb.u32 37 { bytes := artifactBytes, pos := 2764, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 158, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex158_decoded functionTypeIndices_tail159_decoded

theorem functionTypeIndices_tail157_decoded :
    Internal.vectorLoop Leb.u32 38 { bytes := artifactBytes, pos := 2762, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 157, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex157_decoded functionTypeIndices_tail158_decoded

theorem functionTypeIndices_tail156_decoded :
    Internal.vectorLoop Leb.u32 39 { bytes := artifactBytes, pos := 2760, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 156, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex156_decoded functionTypeIndices_tail157_decoded

theorem functionTypeIndices_tail155_decoded :
    Internal.vectorLoop Leb.u32 40 { bytes := artifactBytes, pos := 2758, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 155, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex155_decoded functionTypeIndices_tail156_decoded

theorem functionTypeIndices_tail154_decoded :
    Internal.vectorLoop Leb.u32 41 { bytes := artifactBytes, pos := 2756, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 154, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex154_decoded functionTypeIndices_tail155_decoded

theorem functionTypeIndices_tail153_decoded :
    Internal.vectorLoop Leb.u32 42 { bytes := artifactBytes, pos := 2754, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 153, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex153_decoded functionTypeIndices_tail154_decoded

theorem functionTypeIndices_tail152_decoded :
    Internal.vectorLoop Leb.u32 43 { bytes := artifactBytes, pos := 2752, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 152, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex152_decoded functionTypeIndices_tail153_decoded

theorem functionTypeIndices_tail151_decoded :
    Internal.vectorLoop Leb.u32 44 { bytes := artifactBytes, pos := 2750, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 151, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex151_decoded functionTypeIndices_tail152_decoded

theorem functionTypeIndices_tail150_decoded :
    Internal.vectorLoop Leb.u32 45 { bytes := artifactBytes, pos := 2748, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 150, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex150_decoded functionTypeIndices_tail151_decoded

theorem functionTypeIndices_tail149_decoded :
    Internal.vectorLoop Leb.u32 46 { bytes := artifactBytes, pos := 2746, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 149, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex149_decoded functionTypeIndices_tail150_decoded

theorem functionTypeIndices_tail148_decoded :
    Internal.vectorLoop Leb.u32 47 { bytes := artifactBytes, pos := 2744, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 148, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex148_decoded functionTypeIndices_tail149_decoded


theorem functionTypeIndices_tail147_decoded :
    Internal.vectorLoop Leb.u32 48 { bytes := artifactBytes, pos := 2742, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 147, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex147_decoded functionTypeIndices_tail148_decoded

theorem functionTypeIndices_tail146_decoded :
    Internal.vectorLoop Leb.u32 49 { bytes := artifactBytes, pos := 2740, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 146, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex146_decoded functionTypeIndices_tail147_decoded

theorem functionTypeIndices_tail145_decoded :
    Internal.vectorLoop Leb.u32 50 { bytes := artifactBytes, pos := 2738, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 145, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex145_decoded functionTypeIndices_tail146_decoded

theorem functionTypeIndices_tail144_decoded :
    Internal.vectorLoop Leb.u32 51 { bytes := artifactBytes, pos := 2736, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 144, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex144_decoded functionTypeIndices_tail145_decoded

theorem functionTypeIndices_tail143_decoded :
    Internal.vectorLoop Leb.u32 52 { bytes := artifactBytes, pos := 2734, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 143, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex143_decoded functionTypeIndices_tail144_decoded

theorem functionTypeIndices_tail142_decoded :
    Internal.vectorLoop Leb.u32 53 { bytes := artifactBytes, pos := 2732, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 142, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex142_decoded functionTypeIndices_tail143_decoded

theorem functionTypeIndices_tail141_decoded :
    Internal.vectorLoop Leb.u32 54 { bytes := artifactBytes, pos := 2730, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 141, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex141_decoded functionTypeIndices_tail142_decoded

theorem functionTypeIndices_tail140_decoded :
    Internal.vectorLoop Leb.u32 55 { bytes := artifactBytes, pos := 2728, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 140, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex140_decoded functionTypeIndices_tail141_decoded

theorem functionTypeIndices_tail139_decoded :
    Internal.vectorLoop Leb.u32 56 { bytes := artifactBytes, pos := 2726, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 139, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex139_decoded functionTypeIndices_tail140_decoded

theorem functionTypeIndices_tail138_decoded :
    Internal.vectorLoop Leb.u32 57 { bytes := artifactBytes, pos := 2724, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 138, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex138_decoded functionTypeIndices_tail139_decoded

theorem functionTypeIndices_tail137_decoded :
    Internal.vectorLoop Leb.u32 58 { bytes := artifactBytes, pos := 2722, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 137, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex137_decoded functionTypeIndices_tail138_decoded

theorem functionTypeIndices_tail136_decoded :
    Internal.vectorLoop Leb.u32 59 { bytes := artifactBytes, pos := 2720, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 136, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex136_decoded functionTypeIndices_tail137_decoded

theorem functionTypeIndices_tail135_decoded :
    Internal.vectorLoop Leb.u32 60 { bytes := artifactBytes, pos := 2718, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 135, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex135_decoded functionTypeIndices_tail136_decoded

theorem functionTypeIndices_tail134_decoded :
    Internal.vectorLoop Leb.u32 61 { bytes := artifactBytes, pos := 2716, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 134, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex134_decoded functionTypeIndices_tail135_decoded

theorem functionTypeIndices_tail133_decoded :
    Internal.vectorLoop Leb.u32 62 { bytes := artifactBytes, pos := 2714, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 133, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex133_decoded functionTypeIndices_tail134_decoded

theorem functionTypeIndices_tail132_decoded :
    Internal.vectorLoop Leb.u32 63 { bytes := artifactBytes, pos := 2712, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 132, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex132_decoded functionTypeIndices_tail133_decoded


theorem functionTypeIndices_tail131_decoded :
    Internal.vectorLoop Leb.u32 64 { bytes := artifactBytes, pos := 2710, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 131, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex131_decoded functionTypeIndices_tail132_decoded

theorem functionTypeIndices_tail130_decoded :
    Internal.vectorLoop Leb.u32 65 { bytes := artifactBytes, pos := 2708, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 130, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex130_decoded functionTypeIndices_tail131_decoded

theorem functionTypeIndices_tail129_decoded :
    Internal.vectorLoop Leb.u32 66 { bytes := artifactBytes, pos := 2706, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 129, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex129_decoded functionTypeIndices_tail130_decoded

theorem functionTypeIndices_tail128_decoded :
    Internal.vectorLoop Leb.u32 67 { bytes := artifactBytes, pos := 2704, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 128, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex128_decoded functionTypeIndices_tail129_decoded

theorem functionTypeIndices_tail127_decoded :
    Internal.vectorLoop Leb.u32 68 { bytes := artifactBytes, pos := 2703, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 127, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex127_decoded functionTypeIndices_tail128_decoded

theorem functionTypeIndices_tail126_decoded :
    Internal.vectorLoop Leb.u32 69 { bytes := artifactBytes, pos := 2702, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 126, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex126_decoded functionTypeIndices_tail127_decoded

theorem functionTypeIndices_tail125_decoded :
    Internal.vectorLoop Leb.u32 70 { bytes := artifactBytes, pos := 2701, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 125, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex125_decoded functionTypeIndices_tail126_decoded

theorem functionTypeIndices_tail124_decoded :
    Internal.vectorLoop Leb.u32 71 { bytes := artifactBytes, pos := 2700, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 124, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex124_decoded functionTypeIndices_tail125_decoded

theorem functionTypeIndices_tail123_decoded :
    Internal.vectorLoop Leb.u32 72 { bytes := artifactBytes, pos := 2699, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 123, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex123_decoded functionTypeIndices_tail124_decoded

theorem functionTypeIndices_tail122_decoded :
    Internal.vectorLoop Leb.u32 73 { bytes := artifactBytes, pos := 2698, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 122, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex122_decoded functionTypeIndices_tail123_decoded

theorem functionTypeIndices_tail121_decoded :
    Internal.vectorLoop Leb.u32 74 { bytes := artifactBytes, pos := 2697, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 121, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex121_decoded functionTypeIndices_tail122_decoded

theorem functionTypeIndices_tail120_decoded :
    Internal.vectorLoop Leb.u32 75 { bytes := artifactBytes, pos := 2696, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 120, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex120_decoded functionTypeIndices_tail121_decoded

theorem functionTypeIndices_tail119_decoded :
    Internal.vectorLoop Leb.u32 76 { bytes := artifactBytes, pos := 2695, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 119, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex119_decoded functionTypeIndices_tail120_decoded

theorem functionTypeIndices_tail118_decoded :
    Internal.vectorLoop Leb.u32 77 { bytes := artifactBytes, pos := 2694, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 118, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex118_decoded functionTypeIndices_tail119_decoded

theorem functionTypeIndices_tail117_decoded :
    Internal.vectorLoop Leb.u32 78 { bytes := artifactBytes, pos := 2693, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 117, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex117_decoded functionTypeIndices_tail118_decoded

theorem functionTypeIndices_tail116_decoded :
    Internal.vectorLoop Leb.u32 79 { bytes := artifactBytes, pos := 2692, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 116, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex116_decoded functionTypeIndices_tail117_decoded


theorem functionTypeIndices_tail115_decoded :
    Internal.vectorLoop Leb.u32 80 { bytes := artifactBytes, pos := 2691, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 115, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex115_decoded functionTypeIndices_tail116_decoded

theorem functionTypeIndices_tail114_decoded :
    Internal.vectorLoop Leb.u32 81 { bytes := artifactBytes, pos := 2690, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 114, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex114_decoded functionTypeIndices_tail115_decoded

theorem functionTypeIndices_tail113_decoded :
    Internal.vectorLoop Leb.u32 82 { bytes := artifactBytes, pos := 2689, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 113, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex113_decoded functionTypeIndices_tail114_decoded

theorem functionTypeIndices_tail112_decoded :
    Internal.vectorLoop Leb.u32 83 { bytes := artifactBytes, pos := 2688, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 112, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex112_decoded functionTypeIndices_tail113_decoded

theorem functionTypeIndices_tail111_decoded :
    Internal.vectorLoop Leb.u32 84 { bytes := artifactBytes, pos := 2687, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 111, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex111_decoded functionTypeIndices_tail112_decoded

theorem functionTypeIndices_tail110_decoded :
    Internal.vectorLoop Leb.u32 85 { bytes := artifactBytes, pos := 2686, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 110, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex110_decoded functionTypeIndices_tail111_decoded

theorem functionTypeIndices_tail109_decoded :
    Internal.vectorLoop Leb.u32 86 { bytes := artifactBytes, pos := 2685, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 109, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex109_decoded functionTypeIndices_tail110_decoded

theorem functionTypeIndices_tail108_decoded :
    Internal.vectorLoop Leb.u32 87 { bytes := artifactBytes, pos := 2684, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 108, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex108_decoded functionTypeIndices_tail109_decoded

theorem functionTypeIndices_tail107_decoded :
    Internal.vectorLoop Leb.u32 88 { bytes := artifactBytes, pos := 2683, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 107, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex107_decoded functionTypeIndices_tail108_decoded

theorem functionTypeIndices_tail106_decoded :
    Internal.vectorLoop Leb.u32 89 { bytes := artifactBytes, pos := 2682, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 106, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex106_decoded functionTypeIndices_tail107_decoded

theorem functionTypeIndices_tail105_decoded :
    Internal.vectorLoop Leb.u32 90 { bytes := artifactBytes, pos := 2681, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 105, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex105_decoded functionTypeIndices_tail106_decoded

theorem functionTypeIndices_tail104_decoded :
    Internal.vectorLoop Leb.u32 91 { bytes := artifactBytes, pos := 2680, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 104, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex104_decoded functionTypeIndices_tail105_decoded

theorem functionTypeIndices_tail103_decoded :
    Internal.vectorLoop Leb.u32 92 { bytes := artifactBytes, pos := 2679, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 103, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex103_decoded functionTypeIndices_tail104_decoded

theorem functionTypeIndices_tail102_decoded :
    Internal.vectorLoop Leb.u32 93 { bytes := artifactBytes, pos := 2678, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 102, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex102_decoded functionTypeIndices_tail103_decoded

theorem functionTypeIndices_tail101_decoded :
    Internal.vectorLoop Leb.u32 94 { bytes := artifactBytes, pos := 2677, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 101, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex101_decoded functionTypeIndices_tail102_decoded

theorem functionTypeIndices_tail100_decoded :
    Internal.vectorLoop Leb.u32 95 { bytes := artifactBytes, pos := 2676, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 100, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex100_decoded functionTypeIndices_tail101_decoded


theorem functionTypeIndices_tail99_decoded :
    Internal.vectorLoop Leb.u32 96 { bytes := artifactBytes, pos := 2675, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 99, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex99_decoded functionTypeIndices_tail100_decoded

theorem functionTypeIndices_tail98_decoded :
    Internal.vectorLoop Leb.u32 97 { bytes := artifactBytes, pos := 2674, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 98, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex98_decoded functionTypeIndices_tail99_decoded

theorem functionTypeIndices_tail97_decoded :
    Internal.vectorLoop Leb.u32 98 { bytes := artifactBytes, pos := 2673, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 97, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex97_decoded functionTypeIndices_tail98_decoded

theorem functionTypeIndices_tail96_decoded :
    Internal.vectorLoop Leb.u32 99 { bytes := artifactBytes, pos := 2672, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 96, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex96_decoded functionTypeIndices_tail97_decoded

theorem functionTypeIndices_tail95_decoded :
    Internal.vectorLoop Leb.u32 100 { bytes := artifactBytes, pos := 2671, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 95, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex95_decoded functionTypeIndices_tail96_decoded

theorem functionTypeIndices_tail94_decoded :
    Internal.vectorLoop Leb.u32 101 { bytes := artifactBytes, pos := 2670, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 94, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex94_decoded functionTypeIndices_tail95_decoded

theorem functionTypeIndices_tail93_decoded :
    Internal.vectorLoop Leb.u32 102 { bytes := artifactBytes, pos := 2669, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 93, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex93_decoded functionTypeIndices_tail94_decoded

theorem functionTypeIndices_tail92_decoded :
    Internal.vectorLoop Leb.u32 103 { bytes := artifactBytes, pos := 2668, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 92, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex92_decoded functionTypeIndices_tail93_decoded

theorem functionTypeIndices_tail91_decoded :
    Internal.vectorLoop Leb.u32 104 { bytes := artifactBytes, pos := 2667, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 91, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex91_decoded functionTypeIndices_tail92_decoded

theorem functionTypeIndices_tail90_decoded :
    Internal.vectorLoop Leb.u32 105 { bytes := artifactBytes, pos := 2666, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 90, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex90_decoded functionTypeIndices_tail91_decoded

theorem functionTypeIndices_tail89_decoded :
    Internal.vectorLoop Leb.u32 106 { bytes := artifactBytes, pos := 2665, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 89, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex89_decoded functionTypeIndices_tail90_decoded

theorem functionTypeIndices_tail88_decoded :
    Internal.vectorLoop Leb.u32 107 { bytes := artifactBytes, pos := 2664, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 88, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex88_decoded functionTypeIndices_tail89_decoded

theorem functionTypeIndices_tail87_decoded :
    Internal.vectorLoop Leb.u32 108 { bytes := artifactBytes, pos := 2663, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 87, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex87_decoded functionTypeIndices_tail88_decoded

theorem functionTypeIndices_tail86_decoded :
    Internal.vectorLoop Leb.u32 109 { bytes := artifactBytes, pos := 2662, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 86, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex86_decoded functionTypeIndices_tail87_decoded

theorem functionTypeIndices_tail85_decoded :
    Internal.vectorLoop Leb.u32 110 { bytes := artifactBytes, pos := 2661, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 85, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex85_decoded functionTypeIndices_tail86_decoded

theorem functionTypeIndices_tail84_decoded :
    Internal.vectorLoop Leb.u32 111 { bytes := artifactBytes, pos := 2660, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 84, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex84_decoded functionTypeIndices_tail85_decoded


theorem functionTypeIndices_tail83_decoded :
    Internal.vectorLoop Leb.u32 112 { bytes := artifactBytes, pos := 2659, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 83, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex83_decoded functionTypeIndices_tail84_decoded

theorem functionTypeIndices_tail82_decoded :
    Internal.vectorLoop Leb.u32 113 { bytes := artifactBytes, pos := 2658, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 82, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex82_decoded functionTypeIndices_tail83_decoded

theorem functionTypeIndices_tail81_decoded :
    Internal.vectorLoop Leb.u32 114 { bytes := artifactBytes, pos := 2657, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 81, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex81_decoded functionTypeIndices_tail82_decoded

theorem functionTypeIndices_tail80_decoded :
    Internal.vectorLoop Leb.u32 115 { bytes := artifactBytes, pos := 2656, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 80, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex80_decoded functionTypeIndices_tail81_decoded

theorem functionTypeIndices_tail79_decoded :
    Internal.vectorLoop Leb.u32 116 { bytes := artifactBytes, pos := 2655, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 79, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex79_decoded functionTypeIndices_tail80_decoded

theorem functionTypeIndices_tail78_decoded :
    Internal.vectorLoop Leb.u32 117 { bytes := artifactBytes, pos := 2654, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 78, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex78_decoded functionTypeIndices_tail79_decoded

theorem functionTypeIndices_tail77_decoded :
    Internal.vectorLoop Leb.u32 118 { bytes := artifactBytes, pos := 2653, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 77, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex77_decoded functionTypeIndices_tail78_decoded

theorem functionTypeIndices_tail76_decoded :
    Internal.vectorLoop Leb.u32 119 { bytes := artifactBytes, pos := 2652, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 76, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex76_decoded functionTypeIndices_tail77_decoded

theorem functionTypeIndices_tail75_decoded :
    Internal.vectorLoop Leb.u32 120 { bytes := artifactBytes, pos := 2651, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 75, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex75_decoded functionTypeIndices_tail76_decoded

theorem functionTypeIndices_tail74_decoded :
    Internal.vectorLoop Leb.u32 121 { bytes := artifactBytes, pos := 2650, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 74, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex74_decoded functionTypeIndices_tail75_decoded

theorem functionTypeIndices_tail73_decoded :
    Internal.vectorLoop Leb.u32 122 { bytes := artifactBytes, pos := 2649, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 73, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex73_decoded functionTypeIndices_tail74_decoded

theorem functionTypeIndices_tail72_decoded :
    Internal.vectorLoop Leb.u32 123 { bytes := artifactBytes, pos := 2648, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 72, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex72_decoded functionTypeIndices_tail73_decoded

theorem functionTypeIndices_tail71_decoded :
    Internal.vectorLoop Leb.u32 124 { bytes := artifactBytes, pos := 2647, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 71, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex71_decoded functionTypeIndices_tail72_decoded

theorem functionTypeIndices_tail70_decoded :
    Internal.vectorLoop Leb.u32 125 { bytes := artifactBytes, pos := 2646, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 70, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex70_decoded functionTypeIndices_tail71_decoded

theorem functionTypeIndices_tail69_decoded :
    Internal.vectorLoop Leb.u32 126 { bytes := artifactBytes, pos := 2645, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 69, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex69_decoded functionTypeIndices_tail70_decoded

theorem functionTypeIndices_tail68_decoded :
    Internal.vectorLoop Leb.u32 127 { bytes := artifactBytes, pos := 2644, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 68, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex68_decoded functionTypeIndices_tail69_decoded


theorem functionTypeIndices_tail67_decoded :
    Internal.vectorLoop Leb.u32 128 { bytes := artifactBytes, pos := 2643, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 67, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex67_decoded functionTypeIndices_tail68_decoded

theorem functionTypeIndices_tail66_decoded :
    Internal.vectorLoop Leb.u32 129 { bytes := artifactBytes, pos := 2642, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 66, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex66_decoded functionTypeIndices_tail67_decoded

theorem functionTypeIndices_tail65_decoded :
    Internal.vectorLoop Leb.u32 130 { bytes := artifactBytes, pos := 2641, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 65, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex65_decoded functionTypeIndices_tail66_decoded

theorem functionTypeIndices_tail64_decoded :
    Internal.vectorLoop Leb.u32 131 { bytes := artifactBytes, pos := 2640, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 64, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex64_decoded functionTypeIndices_tail65_decoded

theorem functionTypeIndices_tail63_decoded :
    Internal.vectorLoop Leb.u32 132 { bytes := artifactBytes, pos := 2639, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 63, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex63_decoded functionTypeIndices_tail64_decoded

theorem functionTypeIndices_tail62_decoded :
    Internal.vectorLoop Leb.u32 133 { bytes := artifactBytes, pos := 2638, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 62, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex62_decoded functionTypeIndices_tail63_decoded

theorem functionTypeIndices_tail61_decoded :
    Internal.vectorLoop Leb.u32 134 { bytes := artifactBytes, pos := 2637, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 61, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex61_decoded functionTypeIndices_tail62_decoded

theorem functionTypeIndices_tail60_decoded :
    Internal.vectorLoop Leb.u32 135 { bytes := artifactBytes, pos := 2636, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 60, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex60_decoded functionTypeIndices_tail61_decoded

theorem functionTypeIndices_tail59_decoded :
    Internal.vectorLoop Leb.u32 136 { bytes := artifactBytes, pos := 2635, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 59, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex59_decoded functionTypeIndices_tail60_decoded

theorem functionTypeIndices_tail58_decoded :
    Internal.vectorLoop Leb.u32 137 { bytes := artifactBytes, pos := 2634, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 58, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex58_decoded functionTypeIndices_tail59_decoded

theorem functionTypeIndices_tail57_decoded :
    Internal.vectorLoop Leb.u32 138 { bytes := artifactBytes, pos := 2633, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 57, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex57_decoded functionTypeIndices_tail58_decoded

theorem functionTypeIndices_tail56_decoded :
    Internal.vectorLoop Leb.u32 139 { bytes := artifactBytes, pos := 2632, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 56, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex56_decoded functionTypeIndices_tail57_decoded

theorem functionTypeIndices_tail55_decoded :
    Internal.vectorLoop Leb.u32 140 { bytes := artifactBytes, pos := 2631, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 55, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex55_decoded functionTypeIndices_tail56_decoded

theorem functionTypeIndices_tail54_decoded :
    Internal.vectorLoop Leb.u32 141 { bytes := artifactBytes, pos := 2630, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 54, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex54_decoded functionTypeIndices_tail55_decoded

theorem functionTypeIndices_tail53_decoded :
    Internal.vectorLoop Leb.u32 142 { bytes := artifactBytes, pos := 2629, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 53, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex53_decoded functionTypeIndices_tail54_decoded

theorem functionTypeIndices_tail52_decoded :
    Internal.vectorLoop Leb.u32 143 { bytes := artifactBytes, pos := 2628, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 52, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex52_decoded functionTypeIndices_tail53_decoded


theorem functionTypeIndices_tail51_decoded :
    Internal.vectorLoop Leb.u32 144 { bytes := artifactBytes, pos := 2627, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 51, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex51_decoded functionTypeIndices_tail52_decoded

theorem functionTypeIndices_tail50_decoded :
    Internal.vectorLoop Leb.u32 145 { bytes := artifactBytes, pos := 2626, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 50, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex50_decoded functionTypeIndices_tail51_decoded

theorem functionTypeIndices_tail49_decoded :
    Internal.vectorLoop Leb.u32 146 { bytes := artifactBytes, pos := 2625, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 49, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex49_decoded functionTypeIndices_tail50_decoded

theorem functionTypeIndices_tail48_decoded :
    Internal.vectorLoop Leb.u32 147 { bytes := artifactBytes, pos := 2624, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 48, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex48_decoded functionTypeIndices_tail49_decoded

theorem functionTypeIndices_tail47_decoded :
    Internal.vectorLoop Leb.u32 148 { bytes := artifactBytes, pos := 2623, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 47, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex47_decoded functionTypeIndices_tail48_decoded

theorem functionTypeIndices_tail46_decoded :
    Internal.vectorLoop Leb.u32 149 { bytes := artifactBytes, pos := 2622, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 46, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex46_decoded functionTypeIndices_tail47_decoded

theorem functionTypeIndices_tail45_decoded :
    Internal.vectorLoop Leb.u32 150 { bytes := artifactBytes, pos := 2621, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 45, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex45_decoded functionTypeIndices_tail46_decoded

theorem functionTypeIndices_tail44_decoded :
    Internal.vectorLoop Leb.u32 151 { bytes := artifactBytes, pos := 2620, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 44, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex44_decoded functionTypeIndices_tail45_decoded

theorem functionTypeIndices_tail43_decoded :
    Internal.vectorLoop Leb.u32 152 { bytes := artifactBytes, pos := 2619, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 43, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex43_decoded functionTypeIndices_tail44_decoded

theorem functionTypeIndices_tail42_decoded :
    Internal.vectorLoop Leb.u32 153 { bytes := artifactBytes, pos := 2618, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 42, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex42_decoded functionTypeIndices_tail43_decoded

theorem functionTypeIndices_tail41_decoded :
    Internal.vectorLoop Leb.u32 154 { bytes := artifactBytes, pos := 2617, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 41, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex41_decoded functionTypeIndices_tail42_decoded

theorem functionTypeIndices_tail40_decoded :
    Internal.vectorLoop Leb.u32 155 { bytes := artifactBytes, pos := 2616, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 40, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex40_decoded functionTypeIndices_tail41_decoded

theorem functionTypeIndices_tail39_decoded :
    Internal.vectorLoop Leb.u32 156 { bytes := artifactBytes, pos := 2615, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 39, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex39_decoded functionTypeIndices_tail40_decoded

theorem functionTypeIndices_tail38_decoded :
    Internal.vectorLoop Leb.u32 157 { bytes := artifactBytes, pos := 2614, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 38, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex38_decoded functionTypeIndices_tail39_decoded

theorem functionTypeIndices_tail37_decoded :
    Internal.vectorLoop Leb.u32 158 { bytes := artifactBytes, pos := 2613, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 37, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex37_decoded functionTypeIndices_tail38_decoded

theorem functionTypeIndices_tail36_decoded :
    Internal.vectorLoop Leb.u32 159 { bytes := artifactBytes, pos := 2612, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 36, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex36_decoded functionTypeIndices_tail37_decoded


theorem functionTypeIndices_tail35_decoded :
    Internal.vectorLoop Leb.u32 160 { bytes := artifactBytes, pos := 2611, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 35, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex35_decoded functionTypeIndices_tail36_decoded

theorem functionTypeIndices_tail34_decoded :
    Internal.vectorLoop Leb.u32 161 { bytes := artifactBytes, pos := 2610, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 34, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex34_decoded functionTypeIndices_tail35_decoded

theorem functionTypeIndices_tail33_decoded :
    Internal.vectorLoop Leb.u32 162 { bytes := artifactBytes, pos := 2609, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 33, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex33_decoded functionTypeIndices_tail34_decoded

theorem functionTypeIndices_tail32_decoded :
    Internal.vectorLoop Leb.u32 163 { bytes := artifactBytes, pos := 2608, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 32, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex32_decoded functionTypeIndices_tail33_decoded

theorem functionTypeIndices_tail31_decoded :
    Internal.vectorLoop Leb.u32 164 { bytes := artifactBytes, pos := 2607, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 31, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex31_decoded functionTypeIndices_tail32_decoded

theorem functionTypeIndices_tail30_decoded :
    Internal.vectorLoop Leb.u32 165 { bytes := artifactBytes, pos := 2606, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 30, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex30_decoded functionTypeIndices_tail31_decoded

theorem functionTypeIndices_tail29_decoded :
    Internal.vectorLoop Leb.u32 166 { bytes := artifactBytes, pos := 2605, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 29, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex29_decoded functionTypeIndices_tail30_decoded

theorem functionTypeIndices_tail28_decoded :
    Internal.vectorLoop Leb.u32 167 { bytes := artifactBytes, pos := 2604, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 28, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex28_decoded functionTypeIndices_tail29_decoded

theorem functionTypeIndices_tail27_decoded :
    Internal.vectorLoop Leb.u32 168 { bytes := artifactBytes, pos := 2603, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 27, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex27_decoded functionTypeIndices_tail28_decoded

theorem functionTypeIndices_tail26_decoded :
    Internal.vectorLoop Leb.u32 169 { bytes := artifactBytes, pos := 2602, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 26, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex26_decoded functionTypeIndices_tail27_decoded

theorem functionTypeIndices_tail25_decoded :
    Internal.vectorLoop Leb.u32 170 { bytes := artifactBytes, pos := 2601, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 25, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex25_decoded functionTypeIndices_tail26_decoded

theorem functionTypeIndices_tail24_decoded :
    Internal.vectorLoop Leb.u32 171 { bytes := artifactBytes, pos := 2600, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 24, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex24_decoded functionTypeIndices_tail25_decoded

theorem functionTypeIndices_tail23_decoded :
    Internal.vectorLoop Leb.u32 172 { bytes := artifactBytes, pos := 2599, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 23, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex23_decoded functionTypeIndices_tail24_decoded

theorem functionTypeIndices_tail22_decoded :
    Internal.vectorLoop Leb.u32 173 { bytes := artifactBytes, pos := 2598, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 22, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex22_decoded functionTypeIndices_tail23_decoded

theorem functionTypeIndices_tail21_decoded :
    Internal.vectorLoop Leb.u32 174 { bytes := artifactBytes, pos := 2597, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 21, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex21_decoded functionTypeIndices_tail22_decoded

theorem functionTypeIndices_tail20_decoded :
    Internal.vectorLoop Leb.u32 175 { bytes := artifactBytes, pos := 2596, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 20, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex20_decoded functionTypeIndices_tail21_decoded


theorem functionTypeIndices_tail19_decoded :
    Internal.vectorLoop Leb.u32 176 { bytes := artifactBytes, pos := 2595, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 19, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex19_decoded functionTypeIndices_tail20_decoded

theorem functionTypeIndices_tail18_decoded :
    Internal.vectorLoop Leb.u32 177 { bytes := artifactBytes, pos := 2594, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 18, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex18_decoded functionTypeIndices_tail19_decoded

theorem functionTypeIndices_tail17_decoded :
    Internal.vectorLoop Leb.u32 178 { bytes := artifactBytes, pos := 2593, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 17, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex17_decoded functionTypeIndices_tail18_decoded

theorem functionTypeIndices_tail16_decoded :
    Internal.vectorLoop Leb.u32 179 { bytes := artifactBytes, pos := 2592, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 16, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex16_decoded functionTypeIndices_tail17_decoded

theorem functionTypeIndices_tail15_decoded :
    Internal.vectorLoop Leb.u32 180 { bytes := artifactBytes, pos := 2591, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 15, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex15_decoded functionTypeIndices_tail16_decoded

theorem functionTypeIndices_tail14_decoded :
    Internal.vectorLoop Leb.u32 181 { bytes := artifactBytes, pos := 2590, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 14, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex14_decoded functionTypeIndices_tail15_decoded

theorem functionTypeIndices_tail13_decoded :
    Internal.vectorLoop Leb.u32 182 { bytes := artifactBytes, pos := 2589, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 13, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex13_decoded functionTypeIndices_tail14_decoded

theorem functionTypeIndices_tail12_decoded :
    Internal.vectorLoop Leb.u32 183 { bytes := artifactBytes, pos := 2588, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 12, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex12_decoded functionTypeIndices_tail13_decoded

theorem functionTypeIndices_tail11_decoded :
    Internal.vectorLoop Leb.u32 184 { bytes := artifactBytes, pos := 2587, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 11, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex11_decoded functionTypeIndices_tail12_decoded

theorem functionTypeIndices_tail10_decoded :
    Internal.vectorLoop Leb.u32 185 { bytes := artifactBytes, pos := 2586, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 10, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex10_decoded functionTypeIndices_tail11_decoded

theorem functionTypeIndices_tail9_decoded :
    Internal.vectorLoop Leb.u32 186 { bytes := artifactBytes, pos := 2585, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 9, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex9_decoded functionTypeIndices_tail10_decoded

theorem functionTypeIndices_tail8_decoded :
    Internal.vectorLoop Leb.u32 187 { bytes := artifactBytes, pos := 2584, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 8, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex8_decoded functionTypeIndices_tail9_decoded

theorem functionTypeIndices_tail7_decoded :
    Internal.vectorLoop Leb.u32 188 { bytes := artifactBytes, pos := 2583, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 7, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex7_decoded functionTypeIndices_tail8_decoded

theorem functionTypeIndices_tail6_decoded :
    Internal.vectorLoop Leb.u32 189 { bytes := artifactBytes, pos := 2582, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 6, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex6_decoded functionTypeIndices_tail7_decoded

theorem functionTypeIndices_tail5_decoded :
    Internal.vectorLoop Leb.u32 190 { bytes := artifactBytes, pos := 2581, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 5, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex5_decoded functionTypeIndices_tail6_decoded

theorem functionTypeIndices_tail4_decoded :
    Internal.vectorLoop Leb.u32 191 { bytes := artifactBytes, pos := 2580, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 4, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex4_decoded functionTypeIndices_tail5_decoded


theorem functionTypeIndices_tail3_decoded :
    Internal.vectorLoop Leb.u32 192 { bytes := artifactBytes, pos := 2579, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 3, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex3_decoded functionTypeIndices_tail4_decoded

theorem functionTypeIndices_tail2_decoded :
    Internal.vectorLoop Leb.u32 193 { bytes := artifactBytes, pos := 2578, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 2, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex2_decoded functionTypeIndices_tail3_decoded

theorem functionTypeIndices_tail1_decoded :
    Internal.vectorLoop Leb.u32 194 { bytes := artifactBytes, pos := 2577, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 1, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex1_decoded functionTypeIndices_tail2_decoded

theorem functionTypeIndices_tail0_decoded :
    Internal.vectorLoop Leb.u32 195 { bytes := artifactBytes, pos := 2576, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices.drop 0, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  exact vectorLoop_eq_cons functionIndex0_decoded functionTypeIndices_tail1_decoded

theorem functionTypeIndices_vector_decoded :
    vector Leb.u32 { bytes := artifactBytes, pos := 2574, limit := 2838 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 2838, limit := 2838 }) := by
  refine vector_eq_of_parts (length := 195)
    (itemsStart := { bytes := artifactBytes, pos := 2576, limit := 2838 }) ?_ ?_ ?_
  · cbv
  · decide
  · exact functionTypeIndices_tail0_decoded

#print axioms functionTypeIndices_vector_decoded

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 2572, limit := 45644 } =
      .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 2838, limit := 45644 }) := by
  refine sized_eq_of_parts (size := 264)
    (payload := { bytes := artifactBytes, pos := 2574, limit := 45644 }) (finish := { bytes := artifactBytes, pos := 2838, limit := 2838 })
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact functionTypeIndices_vector_decoded
  · rfl

#print axioms functionTypeIndices_section_decoded

end Project.EulerCertificate.Artifact
