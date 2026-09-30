import LeanExe.Examples.Clob
import Project.Compiler.Command

namespace Project.Clob

open LeanExe.Examples.Clob in
leanexe_compile clob := [marketBuy, fillLevel, insertLevel, addToLevel, addBid]

end Project.Clob
