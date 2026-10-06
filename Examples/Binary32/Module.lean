import Examples.Binary32.Program
import Project.Compiler.Command

namespace Examples.Binary32

open Examples.Binary32 in
leanexe_compile binary32 := [axpy32, hypot32, ratio32, matVec32, piecewise32,
  scale32, axpyArray32, condMix32]

end Examples.Binary32
