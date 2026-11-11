import Demos.Rcv.ProcessFlat
import Verified.Wasi.ReflectCommand

/-! The tabulator's process compiled by the verified WASI compiler.  The list holds the functions
of `Demos/Rcv/Tabulate.lean` in the same order, from the count's `bitIndex` to `tabulate`, and the
process's functions after them.  The `Flat` instances of the state are those of
`Demos/Rcv/ProcessFlat.lean`. -/

namespace Demos.Rcv.Process

open LeanExe LeanExe.Wasi LeanExe.Pipeline Demos.Rcv.ReadProgram Demos.Rcv.PrintProgram
open Demos.Rcv.Program Demos.Rcv.TabulateProgram
open Library.Numerics.Decimal.Int64Text (digitCount digitByte)

set_option Elab.async false
set_option maxHeartbeats 1000000 in
verified_compile_wasi io := [bitIndex, classify, examineAt, tallyRound, continuingOf,
  majorityOf, lowerOf, batchOf, fewestOf, tiedOf, latestOf, decideRound, pushRound, countedOf,
  countedSize, countValid, kindsOk, orderOk, wordsOk, validArray, count,
  findByte, wordByte, matchWord, hasPrefix, readNumber, identByteW, isIdent, nameByteW, isName,
  readAfter, isFormat, isContest, kindCode, candidateCode, orderFrom, readOrder, markFrom,
  fieldWord, fieldsFrom, countByte, ballotWords, readHead, candidatesFrom, ballotsFrom,
  readContest, digitCount, digitByte, pushWord, pushNumber, pushRange, pushHead, pushLine,
  pushMembers, pushVotes, pushElimination, pushRoundLines, toBytes, printReport, pushRole,
  printError, tabulate, initial, remainingOutput, afterWrite, started, writeStep, step, begin]

end Demos.Rcv.Process
