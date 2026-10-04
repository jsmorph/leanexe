import LeanExe.Examples.Binary32
import Project.Compiler.Command

namespace Project.Binary32

open LeanExe.Examples.Binary32 in
leanexe_compile binary32 := [axpy32, hypot32, ratio32]

end Project.Binary32
