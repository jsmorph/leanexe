namespace LeanExeGen.GeneratedR40ee67377869b401.Source

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    #[input.foldl (fun acc value => UInt64.xor acc value) 0]
  else
    #[]

end LeanExeGen.GeneratedR40ee67377869b401.Source
