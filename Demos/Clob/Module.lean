import Demos.Clob.Program
import LeanExe.Compiler.Command

namespace Demos.Clob

open Demos.Clob in
leanexe_compile clob := [marketBuy, fillLevel, insertLevel, setLevel, addBid, depth,
  findLevel, removeLevel, cancelBid, applyCommand, runCommands, stepCommand, runOut,
  fillTwice, fillKeep]

end Demos.Clob
