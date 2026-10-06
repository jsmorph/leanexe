/-! The specification, as the request in `request.txt` states it: for an input of at
most eight words, each word plus one with wrapping arithmetic; for a longer input, the empty array.
-/

namespace Examples.Increment

def expected (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then input.map fun element => element + 1 else #[]

end Examples.Increment
