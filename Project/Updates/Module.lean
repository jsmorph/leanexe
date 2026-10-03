import LeanExe.Examples.Updates
import Project.Compiler.Command

namespace Project.Updates

open LeanExe.Examples.Updates in
leanexe_compile updates := [pushTwo, setTwice, insertErase, pushCopy]

end Project.Updates
