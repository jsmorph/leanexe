import Examples.Updates.Program
import LeanExe.Compiler.Command

namespace Examples.Updates

open Examples.Updates in
leanexe_compile updates := [pushTwo, setTwice, insertErase, pushCopy]

end Examples.Updates
