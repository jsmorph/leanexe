namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Source

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    #[input.foldl (fun sum element => sum + element) 0]
  else
    #[]

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Source
