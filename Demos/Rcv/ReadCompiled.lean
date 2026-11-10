import Demos.Rcv.PrintProgram
import Verified.Reflect.Command

namespace Demos.Rcv.ReadProgram

open Demos.Rcv.PrintProgram
open Library.Numerics.Decimal.Int64Text (digitCount digitByte)

verified_compile rcvread := [findByte, wordByte, matchWord, hasPrefix, readNumber, identByteW,
  isIdent, nameByteW, isName, readAfter, isFormat, isContest, kindCode, candidateCode, orderFrom,
  readOrder, markFrom, fieldWord, fieldsFrom, countByte, ballotWords, readHead, candidatesFrom,
  ballotsFrom, readContest, digitCount, digitByte, pushWord, pushNumber, pushRange, pushHead,
  pushLine, pushMembers, pushVotes, pushElimination, pushRoundLines, toBytes, printReport, pushRole,
  printError]

end Demos.Rcv.ReadProgram
