module

public import Demos.Rcv.TabulateProgram
public import Verified.Reflect.Command

@[expose] public section

/-!
The Oakland tabulator compiled by the verified compiler.  `compiled.module` exports the count
`count` of `Demos/Rcv/Program.lean`, the reader `readContest`, the printers `printReport` and
`printError`, and `tabulate`, which composes them.  The module imports the programs alone, so a
change of a proof does not compile it again.  `Demos/Rcv/TabulateCall.lean` states the exports'
function indices and their call theorems, among them T1 over bytes for `tabulate`.  The option
`(cap := 11520)` gives the translation to C 11,520 pages of `lx_mem`, 720 MiB, which with the closed
form `tabulate_bound` hold the call on a file of up to about 8.9 MB and leave about 26 MiB of the
bare-metal machine's 1 GiB of RAM free below `lx_in` (`tests/baremetal/verified.sh`).
-/

namespace Demos.Rcv.TabulateProgram

open LeanExe LeanExe.Pipeline Demos.Rcv.ReadProgram Demos.Rcv.PrintProgram Demos.Rcv.Program
open Library.Numerics.Decimal.Int64Text (digitCount digitByte)

set_option maxHeartbeats 1000000 in
verified_compile (cap := 11520) compiled := [bitIndex, classify, examineAt,
  tallyRound, continuingOf, majorityOf, lowerOf, batchOf, fewestOf, tiedOf, latestOf, decideRound,
  pushRound, countedOf, countedSize, countValid, kindsOk, orderOk, wordsOk, validArray, count,
  findByte, wordByte, matchWord, hasPrefix, readNumber, identByteW, isIdent, nameByteW, isName,
  readAfter, isFormat, isContest, kindCode, candidateCode, orderFrom, readOrder, markFrom,
  fieldWord, fieldsFrom, countByte, ballotWords, readHead, candidatesFrom, ballotsFrom,
  readContest, digitCount, digitByte, pushWord, pushNumber, pushRange, pushHead, pushLine,
  pushMembers, pushVotes, pushElimination, pushRoundLines, toBytes, printReport, pushRole,
  printError, tabulate]

end Demos.Rcv.TabulateProgram
