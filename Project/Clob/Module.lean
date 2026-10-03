import LeanExe.Examples.Clob
import Project.Compiler.Command

namespace Project.Clob

open LeanExe.Examples.Clob in
leanexe_compile clob := [marketBuy, fillLevel, insertLevel, setLevel, addBid, depth,
  findLevel, removeLevel, cancelBid, applyCommand, runCommands, stepCommand, runOut,
  fillTwice, fillKeep]

end Project.Clob
