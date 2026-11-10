import Demos.Rcv.Program
import Verified.Reflect.Command

/-!
The count of `Demos/Rcv/Program.lean` compiled by the verified compiler.  The module exports
`count`, which takes a contest array and returns the count's result words.
-/

namespace Demos.Rcv.Program

set_option maxHeartbeats 1000000 in
verified_compile compiled := [bitIndex, classify, examineAt, tallyRound, continuingOf,
  majorityOf, lowerOf, batchOf, fewestOf, tiedOf, latestOf, decideRound, pushRound, countedOf,
  countedSize, countValid, kindsOk, orderOk, wordsOk, validArray, count]

end Demos.Rcv.Program
