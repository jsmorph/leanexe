/-! The specification of main's Demo 2, as its request states it: for 21 words
`#[query, key1, value1, …, key10, value10]`, `#[value, 1]` for the first pair whose key equals the
query, and `#[0, 0]` when no key matches or the input does not have 21 words. -/

namespace Examples.Lookup

def expected (input : Array UInt64) : Array UInt64 :=
  if input.size != 21 then
    #[0, 0]
  else
    let query := input[0]!
    if input[1]! = query then #[input[2]!, 1]
    else if input[3]! = query then #[input[4]!, 1]
    else if input[5]! = query then #[input[6]!, 1]
    else if input[7]! = query then #[input[8]!, 1]
    else if input[9]! = query then #[input[10]!, 1]
    else if input[11]! = query then #[input[12]!, 1]
    else if input[13]! = query then #[input[14]!, 1]
    else if input[15]! = query then #[input[16]!, 1]
    else if input[17]! = query then #[input[18]!, 1]
    else if input[19]! = query then #[input[20]!, 1]
    else #[0, 0]

end Examples.Lookup
