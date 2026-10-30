/-!
The largest entry seen so far at each position of an array of words.  A fold over the input keeps
the largest entry so far and the result built so far, and each step pushes the new largest entry
onto the result, which grows in place.
-/

namespace Examples.RunningMax

def compute (xs : Array UInt64) : Array UInt64 :=
  (xs.foldl (fun (state : UInt64 × Array UInt64) x =>
    let largest := max state.1 x
    (largest, state.2.push largest)) ((0 : UInt64), (#[] : Array UInt64))).2

end Examples.RunningMax
