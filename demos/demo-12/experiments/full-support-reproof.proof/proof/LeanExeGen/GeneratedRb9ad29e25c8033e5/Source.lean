namespace LeanExeGen.GeneratedRb9ad29e25c8033e5.Source

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    match input.findIdx? (fun element => element == (0 : UInt64)) with
    | some index => input.eraseIdx! index
    | none => input
  else
    #[]

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Source
