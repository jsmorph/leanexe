import Demos.Rcv.Maine.Process
import Demos.Rcv.ProcessFlat
import Verified.Wasi.ReflectCommand

/-! The Maine process compiled by the verified WASI compiler.  The list holds the functions of
`Demos/Rcv/Maine/Tabulate.lean` in the same order, from the count's `bitIndex` to `tabulate`, and
the process's functions after them: those of the Oakland process of `Demos/Rcv/Process.lean` and
this module's `started` and `begin`.  The `Flat` instances of the state are those of
`Demos/Rcv/ProcessFlat.lean`. -/

namespace Demos.Rcv.Maine.Process

open LeanExe LeanExe.Wasi LeanExe.Pipeline Demos.Rcv.ReadProgram
open Demos.Rcv.Maine.TabulateProgram
open Demos.Rcv.Process (initial remainingOutput afterWrite writeStep step)
open Library.Numerics.Decimal.Int64Text (digitCount digitByte)

set_option Elab.async false
set_option maxHeartbeats 1000000 in
verified_compile_wasi io := [Demos.Rcv.Program.bitIndex, Demos.Rcv.Program.classify,
  Demos.Rcv.Maine.Program.examineAt, Demos.Rcv.Maine.Program.tallyRound,
  Demos.Rcv.Program.continuingOf, Demos.Rcv.Program.majorityOf, Demos.Rcv.Program.fewestOf,
  Demos.Rcv.Program.tiedOf, Demos.Rcv.Program.latestOf, Demos.Rcv.Maine.Program.memberCount,
  Demos.Rcv.Maine.Program.lastPlaceOf, Demos.Rcv.Maine.Program.decideRound,
  Demos.Rcv.Program.pushRound, Demos.Rcv.Program.countedOf, Demos.Rcv.Program.countedSize,
  Demos.Rcv.Maine.Program.countValid, Demos.Rcv.Program.kindsOk, Demos.Rcv.Program.orderOk,
  Demos.Rcv.Program.wordsOk, Demos.Rcv.Program.validArray, Demos.Rcv.Maine.Program.count,
  findByte, wordByte, matchWord, hasPrefix, readNumber, identByteW, isIdent, nameByteW, isName,
  readAfter, isFormat, isContest, kindCode, candidateCode, orderFrom, readOrder, markFrom,
  fieldWord, fieldsFrom, countByte, ballotWords, readHead, candidatesFrom, ballotsFrom,
  readContest, digitCount, digitByte, Demos.Rcv.PrintProgram.pushWord,
  Demos.Rcv.PrintProgram.pushNumber, Demos.Rcv.PrintProgram.pushRange,
  Demos.Rcv.Maine.PrintProgram.pushHead, Demos.Rcv.PrintProgram.pushLine,
  Demos.Rcv.PrintProgram.pushMembers, Demos.Rcv.PrintProgram.pushVotes,
  Demos.Rcv.PrintProgram.pushElimination, Demos.Rcv.PrintProgram.pushRoundLines,
  Demos.Rcv.Maine.PrintProgram.pushFirst, Demos.Rcv.PrintProgram.toBytes,
  Demos.Rcv.Maine.PrintProgram.printReport, Demos.Rcv.PrintProgram.pushRole,
  Demos.Rcv.Maine.PrintProgram.printError, tabulate, initial, remainingOutput, afterWrite,
  started, writeStep, step, begin]

end Demos.Rcv.Maine.Process
