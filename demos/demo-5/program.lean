namespace LeanExeGen.GeneratedRc28a1499719cbaa0.Source

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    input.filter fun element => element < (100 : UInt64)
  else
    #[]

end LeanExeGen.GeneratedRc28a1499719cbaa0.Source
