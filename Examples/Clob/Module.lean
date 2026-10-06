import Examples.Clob.Program
import LeanExe.Compiler.Command

namespace Examples.Clob

open Examples.Clob in
leanexe_compile clob := [marketBuy, fillLevel, insertLevel, setLevel, addBid, depth,
  findLevel, removeLevel, cancelBid, applyCommand, runCommands, stepCommand, runOut,
  fillTwice, fillKeep]

end Examples.Clob
