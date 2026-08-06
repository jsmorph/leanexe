import CodeLib

namespace LeanExeGen.GeneratedReb06c2a75684e92c.Source

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size != 21 then
    #[0, 0]
  else
    let query := input[0]!
    if input[1]! = query then
      #[input[2]!, 1]
    else if input[3]! = query then
      #[input[4]!, 1]
    else if input[5]! = query then
      #[input[6]!, 1]
    else if input[7]! = query then
      #[input[8]!, 1]
    else if input[9]! = query then
      #[input[10]!, 1]
    else if input[11]! = query then
      #[input[12]!, 1]
    else if input[13]! = query then
      #[input[14]!, 1]
    else if input[15]! = query then
      #[input[16]!, 1]
    else if input[17]! = query then
      #[input[18]!, 1]
    else if input[19]! = query then
      #[input[20]!, 1]
    else
      #[0, 0]

end LeanExeGen.GeneratedReb06c2a75684e92c.Source
