import LeanExe.Examples.Words
import Project.Compiler.Command

namespace Project.Words

open LeanExe.Examples.Words in
leanexe_compile words := [Words.first, Words.sumAcc]

end Project.Words
