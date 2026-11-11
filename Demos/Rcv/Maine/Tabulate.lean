import Demos.Rcv.Maine.TabulateProgram
import Verified.Reflect.Command

/-!
The Maine module of the tabulator compiled by the verified compiler.  `compiled.module` exports
the Maine count `count` of `Demos/Rcv/Maine/Program.lean`, the shared reader `readContest`, the
Maine printers `printReport` and `printError`, and `tabulate`, which composes them.
`Demos/Rcv/Maine/TabulateCall.lean` states their call theorems, among them T1 over bytes for
`tabulate` and the call theorem of `count` over words.  The option `(cap := 11520)` gives the
translation to C 11,520 pages of `lx_mem`, 720 MiB, which with the closed form `tabulate_bound`
hold the call on a file of up to about 8.9 MB and leave about 26 MiB of the bare-metal machine's
1 GiB of RAM free below `lx_in` (`tests/baremetal/verified.sh`), and `(pages := 16)`, which the
syntax requires before it, is the default first page count.
-/

namespace Demos.Rcv.Maine.TabulateProgram

open Demos.Rcv.ReadProgram
open Library.Numerics.Decimal.Int64Text (digitCount digitByte)

set_option maxHeartbeats 1000000 in
verified_compile (pages := 16) (cap := 11520) compiled := [Demos.Rcv.Program.bitIndex,
  Demos.Rcv.Program.classify, Demos.Rcv.Maine.Program.examineAt, Demos.Rcv.Maine.Program.tallyRound,
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
