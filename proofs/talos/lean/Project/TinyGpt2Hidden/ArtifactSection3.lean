import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem functionTypeIndices_item0 :
    Leb.u32 { bytes := artifactBytes, pos := 822, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[0]!, { bytes := artifactBytes, pos := 823, limit := 901 }) := by cbv

theorem functionTypeIndices_item1 :
    Leb.u32 { bytes := artifactBytes, pos := 823, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[1]!, { bytes := artifactBytes, pos := 824, limit := 901 }) := by cbv

theorem functionTypeIndices_item2 :
    Leb.u32 { bytes := artifactBytes, pos := 824, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[2]!, { bytes := artifactBytes, pos := 825, limit := 901 }) := by cbv

theorem functionTypeIndices_item3 :
    Leb.u32 { bytes := artifactBytes, pos := 825, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[3]!, { bytes := artifactBytes, pos := 826, limit := 901 }) := by cbv

theorem functionTypeIndices_item4 :
    Leb.u32 { bytes := artifactBytes, pos := 826, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[4]!, { bytes := artifactBytes, pos := 827, limit := 901 }) := by cbv

theorem functionTypeIndices_item5 :
    Leb.u32 { bytes := artifactBytes, pos := 827, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[5]!, { bytes := artifactBytes, pos := 828, limit := 901 }) := by cbv

theorem functionTypeIndices_item6 :
    Leb.u32 { bytes := artifactBytes, pos := 828, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[6]!, { bytes := artifactBytes, pos := 829, limit := 901 }) := by cbv

theorem functionTypeIndices_item7 :
    Leb.u32 { bytes := artifactBytes, pos := 829, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[7]!, { bytes := artifactBytes, pos := 830, limit := 901 }) := by cbv

theorem functionTypeIndices_item8 :
    Leb.u32 { bytes := artifactBytes, pos := 830, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[8]!, { bytes := artifactBytes, pos := 831, limit := 901 }) := by cbv

theorem functionTypeIndices_item9 :
    Leb.u32 { bytes := artifactBytes, pos := 831, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[9]!, { bytes := artifactBytes, pos := 832, limit := 901 }) := by cbv

theorem functionTypeIndices_item10 :
    Leb.u32 { bytes := artifactBytes, pos := 832, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[10]!, { bytes := artifactBytes, pos := 833, limit := 901 }) := by cbv

theorem functionTypeIndices_item11 :
    Leb.u32 { bytes := artifactBytes, pos := 833, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[11]!, { bytes := artifactBytes, pos := 834, limit := 901 }) := by cbv

theorem functionTypeIndices_item12 :
    Leb.u32 { bytes := artifactBytes, pos := 834, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[12]!, { bytes := artifactBytes, pos := 835, limit := 901 }) := by cbv

theorem functionTypeIndices_item13 :
    Leb.u32 { bytes := artifactBytes, pos := 835, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[13]!, { bytes := artifactBytes, pos := 836, limit := 901 }) := by cbv

theorem functionTypeIndices_item14 :
    Leb.u32 { bytes := artifactBytes, pos := 836, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[14]!, { bytes := artifactBytes, pos := 837, limit := 901 }) := by cbv

theorem functionTypeIndices_item15 :
    Leb.u32 { bytes := artifactBytes, pos := 837, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[15]!, { bytes := artifactBytes, pos := 838, limit := 901 }) := by cbv

theorem functionTypeIndices_item16 :
    Leb.u32 { bytes := artifactBytes, pos := 838, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[16]!, { bytes := artifactBytes, pos := 839, limit := 901 }) := by cbv

theorem functionTypeIndices_item17 :
    Leb.u32 { bytes := artifactBytes, pos := 839, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[17]!, { bytes := artifactBytes, pos := 840, limit := 901 }) := by cbv

theorem functionTypeIndices_item18 :
    Leb.u32 { bytes := artifactBytes, pos := 840, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[18]!, { bytes := artifactBytes, pos := 841, limit := 901 }) := by cbv

theorem functionTypeIndices_item19 :
    Leb.u32 { bytes := artifactBytes, pos := 841, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[19]!, { bytes := artifactBytes, pos := 842, limit := 901 }) := by cbv

theorem functionTypeIndices_item20 :
    Leb.u32 { bytes := artifactBytes, pos := 842, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[20]!, { bytes := artifactBytes, pos := 843, limit := 901 }) := by cbv

theorem functionTypeIndices_item21 :
    Leb.u32 { bytes := artifactBytes, pos := 843, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[21]!, { bytes := artifactBytes, pos := 844, limit := 901 }) := by cbv

theorem functionTypeIndices_item22 :
    Leb.u32 { bytes := artifactBytes, pos := 844, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[22]!, { bytes := artifactBytes, pos := 845, limit := 901 }) := by cbv

theorem functionTypeIndices_item23 :
    Leb.u32 { bytes := artifactBytes, pos := 845, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[23]!, { bytes := artifactBytes, pos := 846, limit := 901 }) := by cbv

theorem functionTypeIndices_item24 :
    Leb.u32 { bytes := artifactBytes, pos := 846, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[24]!, { bytes := artifactBytes, pos := 847, limit := 901 }) := by cbv

theorem functionTypeIndices_item25 :
    Leb.u32 { bytes := artifactBytes, pos := 847, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[25]!, { bytes := artifactBytes, pos := 848, limit := 901 }) := by cbv

theorem functionTypeIndices_item26 :
    Leb.u32 { bytes := artifactBytes, pos := 848, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[26]!, { bytes := artifactBytes, pos := 849, limit := 901 }) := by cbv

theorem functionTypeIndices_item27 :
    Leb.u32 { bytes := artifactBytes, pos := 849, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[27]!, { bytes := artifactBytes, pos := 850, limit := 901 }) := by cbv

theorem functionTypeIndices_item28 :
    Leb.u32 { bytes := artifactBytes, pos := 850, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[28]!, { bytes := artifactBytes, pos := 851, limit := 901 }) := by cbv

theorem functionTypeIndices_item29 :
    Leb.u32 { bytes := artifactBytes, pos := 851, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[29]!, { bytes := artifactBytes, pos := 852, limit := 901 }) := by cbv

theorem functionTypeIndices_item30 :
    Leb.u32 { bytes := artifactBytes, pos := 852, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[30]!, { bytes := artifactBytes, pos := 853, limit := 901 }) := by cbv

theorem functionTypeIndices_item31 :
    Leb.u32 { bytes := artifactBytes, pos := 853, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[31]!, { bytes := artifactBytes, pos := 854, limit := 901 }) := by cbv

theorem functionTypeIndices_item32 :
    Leb.u32 { bytes := artifactBytes, pos := 854, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[32]!, { bytes := artifactBytes, pos := 855, limit := 901 }) := by cbv

theorem functionTypeIndices_item33 :
    Leb.u32 { bytes := artifactBytes, pos := 855, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[33]!, { bytes := artifactBytes, pos := 856, limit := 901 }) := by cbv

theorem functionTypeIndices_item34 :
    Leb.u32 { bytes := artifactBytes, pos := 856, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[34]!, { bytes := artifactBytes, pos := 857, limit := 901 }) := by cbv

theorem functionTypeIndices_item35 :
    Leb.u32 { bytes := artifactBytes, pos := 857, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[35]!, { bytes := artifactBytes, pos := 858, limit := 901 }) := by cbv

theorem functionTypeIndices_item36 :
    Leb.u32 { bytes := artifactBytes, pos := 858, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[36]!, { bytes := artifactBytes, pos := 859, limit := 901 }) := by cbv

theorem functionTypeIndices_item37 :
    Leb.u32 { bytes := artifactBytes, pos := 859, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[37]!, { bytes := artifactBytes, pos := 860, limit := 901 }) := by cbv

theorem functionTypeIndices_item38 :
    Leb.u32 { bytes := artifactBytes, pos := 860, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[38]!, { bytes := artifactBytes, pos := 861, limit := 901 }) := by cbv

theorem functionTypeIndices_item39 :
    Leb.u32 { bytes := artifactBytes, pos := 861, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[39]!, { bytes := artifactBytes, pos := 862, limit := 901 }) := by cbv

theorem functionTypeIndices_item40 :
    Leb.u32 { bytes := artifactBytes, pos := 862, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[40]!, { bytes := artifactBytes, pos := 863, limit := 901 }) := by cbv

theorem functionTypeIndices_item41 :
    Leb.u32 { bytes := artifactBytes, pos := 863, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[41]!, { bytes := artifactBytes, pos := 864, limit := 901 }) := by cbv

theorem functionTypeIndices_item42 :
    Leb.u32 { bytes := artifactBytes, pos := 864, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[42]!, { bytes := artifactBytes, pos := 865, limit := 901 }) := by cbv

theorem functionTypeIndices_item43 :
    Leb.u32 { bytes := artifactBytes, pos := 865, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[43]!, { bytes := artifactBytes, pos := 866, limit := 901 }) := by cbv

theorem functionTypeIndices_item44 :
    Leb.u32 { bytes := artifactBytes, pos := 866, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[44]!, { bytes := artifactBytes, pos := 867, limit := 901 }) := by cbv

theorem functionTypeIndices_item45 :
    Leb.u32 { bytes := artifactBytes, pos := 867, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[45]!, { bytes := artifactBytes, pos := 868, limit := 901 }) := by cbv

theorem functionTypeIndices_item46 :
    Leb.u32 { bytes := artifactBytes, pos := 868, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[46]!, { bytes := artifactBytes, pos := 869, limit := 901 }) := by cbv

theorem functionTypeIndices_item47 :
    Leb.u32 { bytes := artifactBytes, pos := 869, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[47]!, { bytes := artifactBytes, pos := 870, limit := 901 }) := by cbv

theorem functionTypeIndices_item48 :
    Leb.u32 { bytes := artifactBytes, pos := 870, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[48]!, { bytes := artifactBytes, pos := 871, limit := 901 }) := by cbv

theorem functionTypeIndices_item49 :
    Leb.u32 { bytes := artifactBytes, pos := 871, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[49]!, { bytes := artifactBytes, pos := 872, limit := 901 }) := by cbv

theorem functionTypeIndices_item50 :
    Leb.u32 { bytes := artifactBytes, pos := 872, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[50]!, { bytes := artifactBytes, pos := 873, limit := 901 }) := by cbv

theorem functionTypeIndices_item51 :
    Leb.u32 { bytes := artifactBytes, pos := 873, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[51]!, { bytes := artifactBytes, pos := 874, limit := 901 }) := by cbv

theorem functionTypeIndices_item52 :
    Leb.u32 { bytes := artifactBytes, pos := 874, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[52]!, { bytes := artifactBytes, pos := 875, limit := 901 }) := by cbv

theorem functionTypeIndices_item53 :
    Leb.u32 { bytes := artifactBytes, pos := 875, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[53]!, { bytes := artifactBytes, pos := 876, limit := 901 }) := by cbv

theorem functionTypeIndices_item54 :
    Leb.u32 { bytes := artifactBytes, pos := 876, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[54]!, { bytes := artifactBytes, pos := 877, limit := 901 }) := by cbv

theorem functionTypeIndices_item55 :
    Leb.u32 { bytes := artifactBytes, pos := 877, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[55]!, { bytes := artifactBytes, pos := 878, limit := 901 }) := by cbv

theorem functionTypeIndices_item56 :
    Leb.u32 { bytes := artifactBytes, pos := 878, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[56]!, { bytes := artifactBytes, pos := 879, limit := 901 }) := by cbv

theorem functionTypeIndices_item57 :
    Leb.u32 { bytes := artifactBytes, pos := 879, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[57]!, { bytes := artifactBytes, pos := 880, limit := 901 }) := by cbv

theorem functionTypeIndices_item58 :
    Leb.u32 { bytes := artifactBytes, pos := 880, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[58]!, { bytes := artifactBytes, pos := 881, limit := 901 }) := by cbv

theorem functionTypeIndices_item59 :
    Leb.u32 { bytes := artifactBytes, pos := 881, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[59]!, { bytes := artifactBytes, pos := 882, limit := 901 }) := by cbv

theorem functionTypeIndices_item60 :
    Leb.u32 { bytes := artifactBytes, pos := 882, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[60]!, { bytes := artifactBytes, pos := 883, limit := 901 }) := by cbv

theorem functionTypeIndices_item61 :
    Leb.u32 { bytes := artifactBytes, pos := 883, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[61]!, { bytes := artifactBytes, pos := 884, limit := 901 }) := by cbv

theorem functionTypeIndices_item62 :
    Leb.u32 { bytes := artifactBytes, pos := 884, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[62]!, { bytes := artifactBytes, pos := 885, limit := 901 }) := by cbv

theorem functionTypeIndices_item63 :
    Leb.u32 { bytes := artifactBytes, pos := 885, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[63]!, { bytes := artifactBytes, pos := 886, limit := 901 }) := by cbv

theorem functionTypeIndices_item64 :
    Leb.u32 { bytes := artifactBytes, pos := 886, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[64]!, { bytes := artifactBytes, pos := 887, limit := 901 }) := by cbv

theorem functionTypeIndices_item65 :
    Leb.u32 { bytes := artifactBytes, pos := 887, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[65]!, { bytes := artifactBytes, pos := 888, limit := 901 }) := by cbv

theorem functionTypeIndices_item66 :
    Leb.u32 { bytes := artifactBytes, pos := 888, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[66]!, { bytes := artifactBytes, pos := 889, limit := 901 }) := by cbv

theorem functionTypeIndices_item67 :
    Leb.u32 { bytes := artifactBytes, pos := 889, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[67]!, { bytes := artifactBytes, pos := 890, limit := 901 }) := by cbv

theorem functionTypeIndices_item68 :
    Leb.u32 { bytes := artifactBytes, pos := 890, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[68]!, { bytes := artifactBytes, pos := 891, limit := 901 }) := by cbv

theorem functionTypeIndices_item69 :
    Leb.u32 { bytes := artifactBytes, pos := 891, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[69]!, { bytes := artifactBytes, pos := 892, limit := 901 }) := by cbv

theorem functionTypeIndices_item70 :
    Leb.u32 { bytes := artifactBytes, pos := 892, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[70]!, { bytes := artifactBytes, pos := 893, limit := 901 }) := by cbv

theorem functionTypeIndices_item71 :
    Leb.u32 { bytes := artifactBytes, pos := 893, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[71]!, { bytes := artifactBytes, pos := 894, limit := 901 }) := by cbv

theorem functionTypeIndices_item72 :
    Leb.u32 { bytes := artifactBytes, pos := 894, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[72]!, { bytes := artifactBytes, pos := 895, limit := 901 }) := by cbv

theorem functionTypeIndices_item73 :
    Leb.u32 { bytes := artifactBytes, pos := 895, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[73]!, { bytes := artifactBytes, pos := 896, limit := 901 }) := by cbv

theorem functionTypeIndices_item74 :
    Leb.u32 { bytes := artifactBytes, pos := 896, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[74]!, { bytes := artifactBytes, pos := 897, limit := 901 }) := by cbv

theorem functionTypeIndices_item75 :
    Leb.u32 { bytes := artifactBytes, pos := 897, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[75]!, { bytes := artifactBytes, pos := 898, limit := 901 }) := by cbv

theorem functionTypeIndices_item76 :
    Leb.u32 { bytes := artifactBytes, pos := 898, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[76]!, { bytes := artifactBytes, pos := 899, limit := 901 }) := by cbv

theorem functionTypeIndices_item77 :
    Leb.u32 { bytes := artifactBytes, pos := 899, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[77]!, { bytes := artifactBytes, pos := 900, limit := 901 }) := by cbv

theorem functionTypeIndices_item78 :
    Leb.u32 { bytes := artifactBytes, pos := 900, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices[78]!, { bytes := artifactBytes, pos := 901, limit := 901 }) := by cbv

theorem functionTypeIndices_tail79 :
    Internal.vectorLoop Leb.u32 0 { bytes := artifactBytes, pos := 901, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 79, { bytes := artifactBytes, pos := 901, limit := 901 }) := by rfl

theorem functionTypeIndices_tail78 :
    Internal.vectorLoop Leb.u32 1 { bytes := artifactBytes, pos := 900, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 78, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item78 functionTypeIndices_tail79

theorem functionTypeIndices_tail77 :
    Internal.vectorLoop Leb.u32 2 { bytes := artifactBytes, pos := 899, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 77, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item77 functionTypeIndices_tail78

theorem functionTypeIndices_tail76 :
    Internal.vectorLoop Leb.u32 3 { bytes := artifactBytes, pos := 898, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 76, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item76 functionTypeIndices_tail77

theorem functionTypeIndices_tail75 :
    Internal.vectorLoop Leb.u32 4 { bytes := artifactBytes, pos := 897, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 75, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item75 functionTypeIndices_tail76

theorem functionTypeIndices_tail74 :
    Internal.vectorLoop Leb.u32 5 { bytes := artifactBytes, pos := 896, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 74, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item74 functionTypeIndices_tail75

theorem functionTypeIndices_tail73 :
    Internal.vectorLoop Leb.u32 6 { bytes := artifactBytes, pos := 895, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 73, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item73 functionTypeIndices_tail74

theorem functionTypeIndices_tail72 :
    Internal.vectorLoop Leb.u32 7 { bytes := artifactBytes, pos := 894, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 72, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item72 functionTypeIndices_tail73

theorem functionTypeIndices_tail71 :
    Internal.vectorLoop Leb.u32 8 { bytes := artifactBytes, pos := 893, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 71, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item71 functionTypeIndices_tail72

theorem functionTypeIndices_tail70 :
    Internal.vectorLoop Leb.u32 9 { bytes := artifactBytes, pos := 892, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 70, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item70 functionTypeIndices_tail71

theorem functionTypeIndices_tail69 :
    Internal.vectorLoop Leb.u32 10 { bytes := artifactBytes, pos := 891, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 69, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item69 functionTypeIndices_tail70

theorem functionTypeIndices_tail68 :
    Internal.vectorLoop Leb.u32 11 { bytes := artifactBytes, pos := 890, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 68, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item68 functionTypeIndices_tail69

theorem functionTypeIndices_tail67 :
    Internal.vectorLoop Leb.u32 12 { bytes := artifactBytes, pos := 889, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 67, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item67 functionTypeIndices_tail68

theorem functionTypeIndices_tail66 :
    Internal.vectorLoop Leb.u32 13 { bytes := artifactBytes, pos := 888, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 66, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item66 functionTypeIndices_tail67

theorem functionTypeIndices_tail65 :
    Internal.vectorLoop Leb.u32 14 { bytes := artifactBytes, pos := 887, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 65, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item65 functionTypeIndices_tail66

theorem functionTypeIndices_tail64 :
    Internal.vectorLoop Leb.u32 15 { bytes := artifactBytes, pos := 886, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 64, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item64 functionTypeIndices_tail65

theorem functionTypeIndices_tail63 :
    Internal.vectorLoop Leb.u32 16 { bytes := artifactBytes, pos := 885, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 63, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item63 functionTypeIndices_tail64

theorem functionTypeIndices_tail62 :
    Internal.vectorLoop Leb.u32 17 { bytes := artifactBytes, pos := 884, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 62, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item62 functionTypeIndices_tail63

theorem functionTypeIndices_tail61 :
    Internal.vectorLoop Leb.u32 18 { bytes := artifactBytes, pos := 883, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 61, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item61 functionTypeIndices_tail62

theorem functionTypeIndices_tail60 :
    Internal.vectorLoop Leb.u32 19 { bytes := artifactBytes, pos := 882, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 60, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item60 functionTypeIndices_tail61

theorem functionTypeIndices_tail59 :
    Internal.vectorLoop Leb.u32 20 { bytes := artifactBytes, pos := 881, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 59, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item59 functionTypeIndices_tail60

theorem functionTypeIndices_tail58 :
    Internal.vectorLoop Leb.u32 21 { bytes := artifactBytes, pos := 880, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 58, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item58 functionTypeIndices_tail59

theorem functionTypeIndices_tail57 :
    Internal.vectorLoop Leb.u32 22 { bytes := artifactBytes, pos := 879, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 57, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item57 functionTypeIndices_tail58

theorem functionTypeIndices_tail56 :
    Internal.vectorLoop Leb.u32 23 { bytes := artifactBytes, pos := 878, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 56, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item56 functionTypeIndices_tail57

theorem functionTypeIndices_tail55 :
    Internal.vectorLoop Leb.u32 24 { bytes := artifactBytes, pos := 877, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 55, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item55 functionTypeIndices_tail56

theorem functionTypeIndices_tail54 :
    Internal.vectorLoop Leb.u32 25 { bytes := artifactBytes, pos := 876, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 54, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item54 functionTypeIndices_tail55

theorem functionTypeIndices_tail53 :
    Internal.vectorLoop Leb.u32 26 { bytes := artifactBytes, pos := 875, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 53, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item53 functionTypeIndices_tail54

theorem functionTypeIndices_tail52 :
    Internal.vectorLoop Leb.u32 27 { bytes := artifactBytes, pos := 874, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 52, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item52 functionTypeIndices_tail53

theorem functionTypeIndices_tail51 :
    Internal.vectorLoop Leb.u32 28 { bytes := artifactBytes, pos := 873, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 51, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item51 functionTypeIndices_tail52

theorem functionTypeIndices_tail50 :
    Internal.vectorLoop Leb.u32 29 { bytes := artifactBytes, pos := 872, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 50, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item50 functionTypeIndices_tail51

theorem functionTypeIndices_tail49 :
    Internal.vectorLoop Leb.u32 30 { bytes := artifactBytes, pos := 871, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 49, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item49 functionTypeIndices_tail50

theorem functionTypeIndices_tail48 :
    Internal.vectorLoop Leb.u32 31 { bytes := artifactBytes, pos := 870, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 48, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item48 functionTypeIndices_tail49

theorem functionTypeIndices_tail47 :
    Internal.vectorLoop Leb.u32 32 { bytes := artifactBytes, pos := 869, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 47, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item47 functionTypeIndices_tail48

theorem functionTypeIndices_tail46 :
    Internal.vectorLoop Leb.u32 33 { bytes := artifactBytes, pos := 868, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 46, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item46 functionTypeIndices_tail47

theorem functionTypeIndices_tail45 :
    Internal.vectorLoop Leb.u32 34 { bytes := artifactBytes, pos := 867, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 45, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item45 functionTypeIndices_tail46

theorem functionTypeIndices_tail44 :
    Internal.vectorLoop Leb.u32 35 { bytes := artifactBytes, pos := 866, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 44, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item44 functionTypeIndices_tail45

theorem functionTypeIndices_tail43 :
    Internal.vectorLoop Leb.u32 36 { bytes := artifactBytes, pos := 865, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 43, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item43 functionTypeIndices_tail44

theorem functionTypeIndices_tail42 :
    Internal.vectorLoop Leb.u32 37 { bytes := artifactBytes, pos := 864, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 42, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item42 functionTypeIndices_tail43

theorem functionTypeIndices_tail41 :
    Internal.vectorLoop Leb.u32 38 { bytes := artifactBytes, pos := 863, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 41, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item41 functionTypeIndices_tail42

theorem functionTypeIndices_tail40 :
    Internal.vectorLoop Leb.u32 39 { bytes := artifactBytes, pos := 862, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 40, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item40 functionTypeIndices_tail41

theorem functionTypeIndices_tail39 :
    Internal.vectorLoop Leb.u32 40 { bytes := artifactBytes, pos := 861, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 39, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item39 functionTypeIndices_tail40

theorem functionTypeIndices_tail38 :
    Internal.vectorLoop Leb.u32 41 { bytes := artifactBytes, pos := 860, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 38, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item38 functionTypeIndices_tail39

theorem functionTypeIndices_tail37 :
    Internal.vectorLoop Leb.u32 42 { bytes := artifactBytes, pos := 859, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 37, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item37 functionTypeIndices_tail38

theorem functionTypeIndices_tail36 :
    Internal.vectorLoop Leb.u32 43 { bytes := artifactBytes, pos := 858, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 36, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item36 functionTypeIndices_tail37

theorem functionTypeIndices_tail35 :
    Internal.vectorLoop Leb.u32 44 { bytes := artifactBytes, pos := 857, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 35, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item35 functionTypeIndices_tail36

theorem functionTypeIndices_tail34 :
    Internal.vectorLoop Leb.u32 45 { bytes := artifactBytes, pos := 856, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 34, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item34 functionTypeIndices_tail35

theorem functionTypeIndices_tail33 :
    Internal.vectorLoop Leb.u32 46 { bytes := artifactBytes, pos := 855, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 33, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item33 functionTypeIndices_tail34

theorem functionTypeIndices_tail32 :
    Internal.vectorLoop Leb.u32 47 { bytes := artifactBytes, pos := 854, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 32, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item32 functionTypeIndices_tail33

theorem functionTypeIndices_tail31 :
    Internal.vectorLoop Leb.u32 48 { bytes := artifactBytes, pos := 853, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 31, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item31 functionTypeIndices_tail32

theorem functionTypeIndices_tail30 :
    Internal.vectorLoop Leb.u32 49 { bytes := artifactBytes, pos := 852, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 30, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item30 functionTypeIndices_tail31

theorem functionTypeIndices_tail29 :
    Internal.vectorLoop Leb.u32 50 { bytes := artifactBytes, pos := 851, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 29, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item29 functionTypeIndices_tail30

theorem functionTypeIndices_tail28 :
    Internal.vectorLoop Leb.u32 51 { bytes := artifactBytes, pos := 850, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 28, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item28 functionTypeIndices_tail29

theorem functionTypeIndices_tail27 :
    Internal.vectorLoop Leb.u32 52 { bytes := artifactBytes, pos := 849, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 27, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item27 functionTypeIndices_tail28

theorem functionTypeIndices_tail26 :
    Internal.vectorLoop Leb.u32 53 { bytes := artifactBytes, pos := 848, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 26, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item26 functionTypeIndices_tail27

theorem functionTypeIndices_tail25 :
    Internal.vectorLoop Leb.u32 54 { bytes := artifactBytes, pos := 847, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 25, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item25 functionTypeIndices_tail26

theorem functionTypeIndices_tail24 :
    Internal.vectorLoop Leb.u32 55 { bytes := artifactBytes, pos := 846, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 24, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item24 functionTypeIndices_tail25

theorem functionTypeIndices_tail23 :
    Internal.vectorLoop Leb.u32 56 { bytes := artifactBytes, pos := 845, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 23, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item23 functionTypeIndices_tail24

theorem functionTypeIndices_tail22 :
    Internal.vectorLoop Leb.u32 57 { bytes := artifactBytes, pos := 844, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 22, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item22 functionTypeIndices_tail23

theorem functionTypeIndices_tail21 :
    Internal.vectorLoop Leb.u32 58 { bytes := artifactBytes, pos := 843, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 21, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item21 functionTypeIndices_tail22

theorem functionTypeIndices_tail20 :
    Internal.vectorLoop Leb.u32 59 { bytes := artifactBytes, pos := 842, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 20, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item20 functionTypeIndices_tail21

theorem functionTypeIndices_tail19 :
    Internal.vectorLoop Leb.u32 60 { bytes := artifactBytes, pos := 841, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 19, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item19 functionTypeIndices_tail20

theorem functionTypeIndices_tail18 :
    Internal.vectorLoop Leb.u32 61 { bytes := artifactBytes, pos := 840, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 18, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item18 functionTypeIndices_tail19

theorem functionTypeIndices_tail17 :
    Internal.vectorLoop Leb.u32 62 { bytes := artifactBytes, pos := 839, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 17, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item17 functionTypeIndices_tail18

theorem functionTypeIndices_tail16 :
    Internal.vectorLoop Leb.u32 63 { bytes := artifactBytes, pos := 838, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 16, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item16 functionTypeIndices_tail17

theorem functionTypeIndices_tail15 :
    Internal.vectorLoop Leb.u32 64 { bytes := artifactBytes, pos := 837, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 15, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item15 functionTypeIndices_tail16

theorem functionTypeIndices_tail14 :
    Internal.vectorLoop Leb.u32 65 { bytes := artifactBytes, pos := 836, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 14, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item14 functionTypeIndices_tail15

theorem functionTypeIndices_tail13 :
    Internal.vectorLoop Leb.u32 66 { bytes := artifactBytes, pos := 835, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 13, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item13 functionTypeIndices_tail14

theorem functionTypeIndices_tail12 :
    Internal.vectorLoop Leb.u32 67 { bytes := artifactBytes, pos := 834, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 12, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item12 functionTypeIndices_tail13

theorem functionTypeIndices_tail11 :
    Internal.vectorLoop Leb.u32 68 { bytes := artifactBytes, pos := 833, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 11, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item11 functionTypeIndices_tail12

theorem functionTypeIndices_tail10 :
    Internal.vectorLoop Leb.u32 69 { bytes := artifactBytes, pos := 832, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 10, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item10 functionTypeIndices_tail11

theorem functionTypeIndices_tail9 :
    Internal.vectorLoop Leb.u32 70 { bytes := artifactBytes, pos := 831, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 9, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item9 functionTypeIndices_tail10

theorem functionTypeIndices_tail8 :
    Internal.vectorLoop Leb.u32 71 { bytes := artifactBytes, pos := 830, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 8, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item8 functionTypeIndices_tail9

theorem functionTypeIndices_tail7 :
    Internal.vectorLoop Leb.u32 72 { bytes := artifactBytes, pos := 829, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 7, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item7 functionTypeIndices_tail8

theorem functionTypeIndices_tail6 :
    Internal.vectorLoop Leb.u32 73 { bytes := artifactBytes, pos := 828, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 6, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item6 functionTypeIndices_tail7

theorem functionTypeIndices_tail5 :
    Internal.vectorLoop Leb.u32 74 { bytes := artifactBytes, pos := 827, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 5, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item5 functionTypeIndices_tail6

theorem functionTypeIndices_tail4 :
    Internal.vectorLoop Leb.u32 75 { bytes := artifactBytes, pos := 826, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 4, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item4 functionTypeIndices_tail5

theorem functionTypeIndices_tail3 :
    Internal.vectorLoop Leb.u32 76 { bytes := artifactBytes, pos := 825, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 3, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item3 functionTypeIndices_tail4

theorem functionTypeIndices_tail2 :
    Internal.vectorLoop Leb.u32 77 { bytes := artifactBytes, pos := 824, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 2, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item2 functionTypeIndices_tail3

theorem functionTypeIndices_tail1 :
    Internal.vectorLoop Leb.u32 78 { bytes := artifactBytes, pos := 823, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 1, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item1 functionTypeIndices_tail2

theorem functionTypeIndices_tail0 :
    Internal.vectorLoop Leb.u32 79 { bytes := artifactBytes, pos := 822, limit := 901 } =
      .ok (Cache.raw.functionTypeIndices.drop 0, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  exact vectorLoop_eq_cons functionTypeIndices_item0 functionTypeIndices_tail1

theorem functionTypeIndices_vector :
    vector Leb.u32 { bytes := artifactBytes, pos := 821, limit := 901 } = .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 901, limit := 901 }) := by
  refine vector_eq_of_parts (length := 79) (itemsStart := { bytes := artifactBytes, pos := 822, limit := 901 }) ?_ ?_ functionTypeIndices_tail0
  · cbv
  · decide

theorem functionTypeIndices_section_decoded :
    sized (vector Leb.u32) { bytes := artifactBytes, pos := 820, limit := 16006 } = .ok (Cache.raw.functionTypeIndices, { bytes := artifactBytes, pos := 901, limit := 16006 }) := by
  refine sized_eq_of_parts (size := 80) (payload := { bytes := artifactBytes, pos := 821, limit := 16006 })
    (finish := { bytes := artifactBytes, pos := 901, limit := 901 }) ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact functionTypeIndices_vector
  · rfl

#print axioms functionTypeIndices_section_decoded
end Project.TinyGpt2Hidden.Artifact
