import Demos.Gpt32.Program
import LeanExe.Compiler.Command

namespace Demos.Gpt32

open Demos.Gpt32 in
leanexe_compile gpt32 := [expArray32, embed32, layerNorm32, Library.Numerics.LinearAlgebra.Binary32.linear32, append32, scores32,
  headMax32, headSum32, probs32, mix32, Library.Numerics.LinearAlgebra.Binary32.add32, geluArray32, logits32]

end Demos.Gpt32
