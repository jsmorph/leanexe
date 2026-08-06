namespace LeanExeGen.GeneratedRd1e76d3580ead0d9.Source

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size != 15 then
    #[0, 0]
  else
    let query := input[0]!
    if query = input[1]! then
      #[input[2]!, 1]
    else if query < input[1]! then
      if query = input[3]! then
        #[input[4]!, 1]
      else if query < input[3]! then
        if query = input[7]! then #[input[8]!, 1] else #[0, 0]
      else
        if query = input[9]! then #[input[10]!, 1] else #[0, 0]
    else
      if query = input[5]! then
        #[input[6]!, 1]
      else if query < input[5]! then
        if query = input[11]! then #[input[12]!, 1] else #[0, 0]
      else
        if query = input[13]! then #[input[14]!, 1] else #[0, 0]

end LeanExeGen.GeneratedRd1e76d3580ead0d9.Source
