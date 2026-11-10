import Demos.Rcv.Maine.TabulateProgram
import Verified.Reflect.Command

/-!
The Maine module of the tabulator compiled by the verified compiler.  `compiled.module` exports
the Maine count `count` of `Demos/Rcv/Maine/Program.lean`, the shared reader `readContest`, the
Maine printers `printReport` and `printError`, and `tabulate`, which composes them.
`Demos/Rcv/Maine/TabulateCall.lean` states their call theorems, among them T1 over bytes for
`tabulate` and the call theorem of `count` over words.
-/

namespace Demos.Rcv.Maine.TabulateProgram

open Demos.Rcv.ReadProgram
open Library.Numerics.Decimal.Int64Text (digitCount digitByte)

set_option maxHeartbeats 1000000 in
verified_compile compiled := [Demos.Rcv.Program.bitIndex, Demos.Rcv.Program.classify,
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
  Demos.Rcv.Maine.PrintProgram.printError, tabulate]

end Demos.Rcv.Maine.TabulateProgram
