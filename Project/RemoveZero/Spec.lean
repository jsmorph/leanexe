/-! The specification of main's Demo 12, as its request states it: for an input of at most eight
words, the input without its first zero, in order, or the input when it has no zero; for a longer
input, the empty array. -/

namespace Project.RemoveZero

def expected (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    match input.findIdx? (fun element => element == (0 : UInt64)) with
    | some index => input.eraseIdx! index
    | none => input
  else #[]

end Project.RemoveZero
