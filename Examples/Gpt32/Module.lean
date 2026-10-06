import Examples.Gpt32.Program
import Project.Compiler.Command

namespace Examples.Gpt32

open Examples.Gpt32 in
leanexe_compile gpt32 := [expArray32, embed32, layerNorm32, linear32, append32, scores32,
  headMax32, headSum32, probs32, mix32, add32, geluArray32, logits32]

end Examples.Gpt32
