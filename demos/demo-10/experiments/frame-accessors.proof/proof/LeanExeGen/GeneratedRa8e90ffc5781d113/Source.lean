namespace LeanExeGen.GeneratedRa8e90ffc5781d113.Source

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    #[input.foldl (fun product element => product * element) 1]
  else
    #[]

end LeanExeGen.GeneratedRa8e90ffc5781d113.Source
