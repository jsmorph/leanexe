import Project.TinyGpt2Hidden.ArtifactByteLookup

namespace Project.TinyGpt2Hidden.Artifact

@[cbv_eval] theorem exportSlice0 :
    artifactBytes.extract 944 950 = [109, 101, 109, 111, 114, 121].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice1 :
    artifactBytes.extract 953 959 = [104, 105, 100, 100, 101, 110].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice2 :
    artifactBytes.extract 962 967 = [97, 108, 108, 111, 99].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice3 :
    artifactBytes.extract 970 975 = [114, 101, 115, 101, 116].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice4 :
    artifactBytes.extract 978 984 = [114, 101, 116, 97, 105, 110].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice5 :
    artifactBytes.extract 987 994 = [114, 101, 108, 101, 97, 115, 101].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice6 :
    artifactBytes.extract 997 1001 = [102, 114, 101, 101].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice7 :
    artifactBytes.extract 1004 1014 = [97, 108, 108, 111, 99, 67, 111, 117, 110, 116].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice8 :
    artifactBytes.extract 1017 1028 = [114, 101, 116, 97, 105, 110, 67, 111, 117, 110, 116].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice9 :
    artifactBytes.extract 1031 1043 = [114, 101, 108, 101, 97, 115, 101, 67, 111, 117, 110, 116].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice10 :
    artifactBytes.extract 1046 1055 = [102, 114, 101, 101, 67, 111, 117, 110, 116].toByteArray := by decide +kernel

@[cbv_eval] theorem exportSlice11 :
    artifactBytes.extract 943 954 = [6, 109, 101, 109, 111, 114, 121, 2, 0, 6, 104].toByteArray := by decide +kernel

#print axioms exportSlice0
end Project.TinyGpt2Hidden.Artifact
