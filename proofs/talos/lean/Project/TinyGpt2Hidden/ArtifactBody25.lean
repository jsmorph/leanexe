import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence25_71_e_5_t_tail1 :
    instructionSequenceAt 361 true { bytes := artifactBytes, pos := 3305, limit := 3541 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[25]!.body)[71]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3306, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_71_e_5_t_tail0 :
    instructionSequenceAt 362 true { bytes := artifactBytes, pos := 3304, limit := 3541 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[25]!.body)[71]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3306, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_71_e_5_e_tail3 :
    instructionSequenceAt 359 false { bytes := artifactBytes, pos := 3311, limit := 3541 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[25]!.body)[71]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 3312, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_71_e_5_e_tail0 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 3306, limit := 3541 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[25]!.body)[71]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3312, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_109_e_5_t_tail1 :
    instructionSequenceAt 323 true { bytes := artifactBytes, pos := 3428, limit := 3541 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[25]!.body)[109]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3429, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_109_e_5_t_tail0 :
    instructionSequenceAt 324 true { bytes := artifactBytes, pos := 3427, limit := 3541 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[25]!.body)[109]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3429, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_109_e_5_e_tail3 :
    instructionSequenceAt 321 false { bytes := artifactBytes, pos := 3434, limit := 3541 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[25]!.body)[109]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 3435, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_109_e_5_e_tail0 :
    instructionSequenceAt 324 false { bytes := artifactBytes, pos := 3429, limit := 3541 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[25]!.body)[109]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3435, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_20_t_tail1 :
    instructionSequenceAt 419 true { bytes := artifactBytes, pos := 3140, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[20]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3141, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_20_t_tail0 :
    instructionSequenceAt 420 true { bytes := artifactBytes, pos := 3139, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[20]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3141, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_20_e_tail1 :
    instructionSequenceAt 419 false { bytes := artifactBytes, pos := 3143, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[20]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3144, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_20_e_tail0 :
    instructionSequenceAt 420 false { bytes := artifactBytes, pos := 3141, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[20]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3144, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_27_t_tail11 :
    instructionSequenceAt 402 true { bytes := artifactBytes, pos := 3175, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[27]!) false).drop 11, .otherwise), { bytes := artifactBytes, pos := 3176, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_27_t_tail8 :
    instructionSequenceAt 405 true { bytes := artifactBytes, pos := 3170, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[27]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 3176, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_27_t_tail0 :
    instructionSequenceAt 413 true { bytes := artifactBytes, pos := 3157, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[27]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3176, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_27_e_tail1 :
    instructionSequenceAt 412 false { bytes := artifactBytes, pos := 3177, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[27]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3178, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_27_e_tail0 :
    instructionSequenceAt 413 false { bytes := artifactBytes, pos := 3176, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[27]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3178, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_41_t_tail1 :
    instructionSequenceAt 398 true { bytes := artifactBytes, pos := 3205, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[41]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3206, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_41_t_tail0 :
    instructionSequenceAt 399 true { bytes := artifactBytes, pos := 3204, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[41]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3206, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_41_e_tail1 :
    instructionSequenceAt 398 false { bytes := artifactBytes, pos := 3208, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[41]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3209, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_41_e_tail0 :
    instructionSequenceAt 399 false { bytes := artifactBytes, pos := 3206, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[41]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3209, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_51_t_tail1 :
    instructionSequenceAt 388 true { bytes := artifactBytes, pos := 3228, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[51]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3229, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_51_t_tail0 :
    instructionSequenceAt 389 true { bytes := artifactBytes, pos := 3227, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[51]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3229, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_51_e_tail1 :
    instructionSequenceAt 388 false { bytes := artifactBytes, pos := 3231, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[51]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3232, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_51_e_tail0 :
    instructionSequenceAt 389 false { bytes := artifactBytes, pos := 3229, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[51]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3232, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_58_t_tail11 :
    instructionSequenceAt 371 true { bytes := artifactBytes, pos := 3263, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[58]!) false).drop 11, .otherwise), { bytes := artifactBytes, pos := 3264, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_58_t_tail8 :
    instructionSequenceAt 374 true { bytes := artifactBytes, pos := 3258, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[58]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 3264, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_58_t_tail0 :
    instructionSequenceAt 382 true { bytes := artifactBytes, pos := 3245, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[58]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3264, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_58_e_tail1 :
    instructionSequenceAt 381 false { bytes := artifactBytes, pos := 3265, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[58]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3266, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_58_e_tail0 :
    instructionSequenceAt 382 false { bytes := artifactBytes, pos := 3264, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[58]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3266, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_71_t_tail1 :
    instructionSequenceAt 368 true { bytes := artifactBytes, pos := 3293, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[71]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3294, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_71_t_tail0 :
    instructionSequenceAt 369 true { bytes := artifactBytes, pos := 3291, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[71]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3294, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_71_e_tail6 :
    instructionSequenceAt 363 false { bytes := artifactBytes, pos := 3312, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[71]!) true).drop 6, .end), { bytes := artifactBytes, pos := 3313, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_71_e_tail0 :
    instructionSequenceAt 369 false { bytes := artifactBytes, pos := 3294, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[71]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3313, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_79_t_tail1 :
    instructionSequenceAt 360 true { bytes := artifactBytes, pos := 3328, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[79]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3329, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_79_t_tail0 :
    instructionSequenceAt 361 true { bytes := artifactBytes, pos := 3327, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[79]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3329, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_79_e_tail1 :
    instructionSequenceAt 360 false { bytes := artifactBytes, pos := 3331, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[79]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3332, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_79_e_tail0 :
    instructionSequenceAt 361 false { bytes := artifactBytes, pos := 3329, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[79]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3332, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_89_t_tail1 :
    instructionSequenceAt 350 true { bytes := artifactBytes, pos := 3351, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[89]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3352, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_89_t_tail0 :
    instructionSequenceAt 351 true { bytes := artifactBytes, pos := 3350, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[89]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3352, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_89_e_tail1 :
    instructionSequenceAt 350 false { bytes := artifactBytes, pos := 3354, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[89]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3355, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_89_e_tail0 :
    instructionSequenceAt 351 false { bytes := artifactBytes, pos := 3352, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[89]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3355, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_96_t_tail11 :
    instructionSequenceAt 333 true { bytes := artifactBytes, pos := 3386, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[96]!) false).drop 11, .otherwise), { bytes := artifactBytes, pos := 3387, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_96_t_tail8 :
    instructionSequenceAt 336 true { bytes := artifactBytes, pos := 3381, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[96]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 3387, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_96_t_tail0 :
    instructionSequenceAt 344 true { bytes := artifactBytes, pos := 3368, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[96]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3387, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_96_e_tail1 :
    instructionSequenceAt 343 false { bytes := artifactBytes, pos := 3388, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[96]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3389, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_96_e_tail0 :
    instructionSequenceAt 344 false { bytes := artifactBytes, pos := 3387, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[96]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3389, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_109_t_tail1 :
    instructionSequenceAt 330 true { bytes := artifactBytes, pos := 3416, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[109]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3417, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_109_t_tail0 :
    instructionSequenceAt 331 true { bytes := artifactBytes, pos := 3414, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[109]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3417, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_109_e_tail6 :
    instructionSequenceAt 325 false { bytes := artifactBytes, pos := 3435, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[109]!) true).drop 6, .end), { bytes := artifactBytes, pos := 3436, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_109_e_tail0 :
    instructionSequenceAt 331 false { bytes := artifactBytes, pos := 3417, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[109]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3436, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_117_t_tail1 :
    instructionSequenceAt 322 true { bytes := artifactBytes, pos := 3451, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[117]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3452, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_117_t_tail0 :
    instructionSequenceAt 323 true { bytes := artifactBytes, pos := 3450, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[117]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3452, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_117_e_tail1 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 3454, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[117]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3455, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_117_e_tail0 :
    instructionSequenceAt 323 false { bytes := artifactBytes, pos := 3452, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[117]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3455, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_127_t_tail1 :
    instructionSequenceAt 312 true { bytes := artifactBytes, pos := 3474, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[127]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 3475, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_127_t_tail0 :
    instructionSequenceAt 313 true { bytes := artifactBytes, pos := 3473, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[127]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3475, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_127_e_tail1 :
    instructionSequenceAt 312 false { bytes := artifactBytes, pos := 3477, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[127]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3478, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_127_e_tail0 :
    instructionSequenceAt 313 false { bytes := artifactBytes, pos := 3475, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[127]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3478, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_134_t_tail11 :
    instructionSequenceAt 295 true { bytes := artifactBytes, pos := 3509, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[134]!) false).drop 11, .otherwise), { bytes := artifactBytes, pos := 3510, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_134_t_tail8 :
    instructionSequenceAt 298 true { bytes := artifactBytes, pos := 3504, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[134]!) false).drop 8, .otherwise), { bytes := artifactBytes, pos := 3510, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_134_t_tail0 :
    instructionSequenceAt 306 true { bytes := artifactBytes, pos := 3491, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[134]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 3510, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_134_e_tail1 :
    instructionSequenceAt 305 false { bytes := artifactBytes, pos := 3511, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[134]!) true).drop 1, .end), { bytes := artifactBytes, pos := 3512, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_134_e_tail0 :
    instructionSequenceAt 306 false { bytes := artifactBytes, pos := 3510, limit := 3541 } =
      .ok (((Instr.childBody ((Cache.raw.codes[25]!.body)[134]!) true).drop 0, .end), { bytes := artifactBytes, pos := 3512, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail149 :
    instructionSequenceAt 293 false { bytes := artifactBytes, pos := 3540, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 149, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail144 :
    instructionSequenceAt 298 false { bytes := artifactBytes, pos := 3530, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 144, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail136 :
    instructionSequenceAt 306 false { bytes := artifactBytes, pos := 3514, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 136, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail128 :
    instructionSequenceAt 314 false { bytes := artifactBytes, pos := 3478, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 128, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail120 :
    instructionSequenceAt 322 false { bytes := artifactBytes, pos := 3459, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 120, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail112 :
    instructionSequenceAt 330 false { bytes := artifactBytes, pos := 3440, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 112, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail104 :
    instructionSequenceAt 338 false { bytes := artifactBytes, pos := 3403, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 104, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail96 :
    instructionSequenceAt 346 false { bytes := artifactBytes, pos := 3366, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 96, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail88 :
    instructionSequenceAt 354 false { bytes := artifactBytes, pos := 3347, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 88, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail80 :
    instructionSequenceAt 362 false { bytes := artifactBytes, pos := 3332, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 80, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail72 :
    instructionSequenceAt 370 false { bytes := artifactBytes, pos := 3313, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 72, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail64 :
    instructionSequenceAt 378 false { bytes := artifactBytes, pos := 3276, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 64, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail56 :
    instructionSequenceAt 386 false { bytes := artifactBytes, pos := 3239, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 56, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail48 :
    instructionSequenceAt 394 false { bytes := artifactBytes, pos := 3220, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 48, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail40 :
    instructionSequenceAt 402 false { bytes := artifactBytes, pos := 3201, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 40, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail32 :
    instructionSequenceAt 410 false { bytes := artifactBytes, pos := 3186, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 32, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail24 :
    instructionSequenceAt 418 false { bytes := artifactBytes, pos := 3150, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 24, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail16 :
    instructionSequenceAt 426 false { bytes := artifactBytes, pos := 3131, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 16, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail8 :
    instructionSequenceAt 434 false { bytes := artifactBytes, pos := 3115, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 8, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

@[cbv_eval] theorem sequence25_tail0 :
    instructionSequenceAt 442 false { bytes := artifactBytes, pos := 3099, limit := 3541 } =
      .ok (((Cache.raw.codes[25]!.body).drop 0, .end), { bytes := artifactBytes, pos := 3541, limit := 3541 }) := by cbv

theorem code25_decoded_parts :
    code { bytes := artifactBytes, pos := 3094, limit := 16006 } = .ok (Cache.raw.codes[25]!, { bytes := artifactBytes, pos := 3541, limit := 16006 }) := by
  refine code_eq_of_parts (size := 445)
    (payload := { bytes := artifactBytes, pos := 3096, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 3099, limit := 3541 })
    (bodyFinish := { bytes := artifactBytes, pos := 3541, limit := 3541 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence25_tail0
  · rfl

#print axioms code25_decoded_parts
end Project.TinyGpt2Hidden.Artifact
