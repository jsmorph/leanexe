import Project.Artifact.Binary.InstructionEvaluate
import Project.Artifact.Binary.Equality
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence57_372_t_tail1 :
    instructionSequenceAt 683 true { bytes := artifactBytes, pos := 7431, limit := 7739 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 7432, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_372_t_tail0 :
    instructionSequenceAt 684 true { bytes := artifactBytes, pos := 7430, limit := 7739 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 7432, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_372_e_tail1 :
    instructionSequenceAt 683 false { bytes := artifactBytes, pos := 7435, limit := 7739 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 7436, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_372_e_tail0 :
    instructionSequenceAt 684 false { bytes := artifactBytes, pos := 7432, limit := 7739 } =
      .ok (([Wasm.Binary.Instr.localGet 172], .end), { bytes := artifactBytes, pos := 7436, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_403_t_tail1 :
    instructionSequenceAt 652 true { bytes := artifactBytes, pos := 7512, limit := 7739 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 7513, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_403_t_tail0 :
    instructionSequenceAt 653 true { bytes := artifactBytes, pos := 7511, limit := 7739 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 7513, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_403_e_tail1 :
    instructionSequenceAt 652 false { bytes := artifactBytes, pos := 7516, limit := 7739 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 7517, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_403_e_tail0 :
    instructionSequenceAt 653 false { bytes := artifactBytes, pos := 7513, limit := 7739 } =
      .ok (([Wasm.Binary.Instr.localGet 172], .end), { bytes := artifactBytes, pos := 7517, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_434_t_tail1 :
    instructionSequenceAt 621 true { bytes := artifactBytes, pos := 7593, limit := 7739 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 7594, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_434_t_tail0 :
    instructionSequenceAt 622 true { bytes := artifactBytes, pos := 7592, limit := 7739 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 7594, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_434_e_tail1 :
    instructionSequenceAt 621 false { bytes := artifactBytes, pos := 7597, limit := 7739 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 7598, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_434_e_tail0 :
    instructionSequenceAt 622 false { bytes := artifactBytes, pos := 7594, limit := 7739 } =
      .ok (([Wasm.Binary.Instr.localGet 172], .end), { bytes := artifactBytes, pos := 7598, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_465_t_tail1 :
    instructionSequenceAt 590 true { bytes := artifactBytes, pos := 7674, limit := 7739 } =
      .ok (([], .otherwise), { bytes := artifactBytes, pos := 7675, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_465_t_tail0 :
    instructionSequenceAt 591 true { bytes := artifactBytes, pos := 7673, limit := 7739 } =
      .ok (([Wasm.Binary.Instr.unreachable], .otherwise), { bytes := artifactBytes, pos := 7675, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_465_e_tail1 :
    instructionSequenceAt 590 false { bytes := artifactBytes, pos := 7678, limit := 7739 } =
      .ok (([], .end), { bytes := artifactBytes, pos := 7679, limit := 7739 }) := by
  cbv

@[cbv_eval] theorem sequence57_465_e_tail0 :
    instructionSequenceAt 591 false { bytes := artifactBytes, pos := 7675, limit := 7739 } =
      .ok (([Wasm.Binary.Instr.localGet 172], .end), { bytes := artifactBytes, pos := 7679, limit := 7739 }) := by
  cbv

end Project.TinyGpt2Hidden.Artifact
