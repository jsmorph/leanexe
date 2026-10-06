/-! The specification of the earlier system's Demo 5, as its request states it: for an input of at
most eight words, the elements less than 100 in their original order; for a longer input, the empty
array. -/

namespace Examples.Below100

def expected (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then input.filter fun element => element < (100 : UInt64) else #[]

end Examples.Below100
