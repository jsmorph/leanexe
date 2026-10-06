import Examples.Words.Program
import Project.Compiler.Command

namespace Examples.Words

open Examples.Words in
leanexe_compile words := [Words.first, Words.sumAcc, Words.range]

end Examples.Words
