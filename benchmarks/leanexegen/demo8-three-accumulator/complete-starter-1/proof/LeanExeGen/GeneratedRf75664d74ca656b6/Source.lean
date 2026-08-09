namespace LeanExeGen.GeneratedRf75664d74ca656b6.Source

def scalarIdentity (value : UInt64) : UInt64 := Id.run do
  let mut remaining := value
  let mut audit := value
  let mut result : UInt64 := 0
  while remaining != 0 do
    remaining := remaining - 1
    result := result + 1
    audit := audit + 2
  return result

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size == 1 then
    #[scalarIdentity input[0]!]
  else
    input

end LeanExeGen.GeneratedRf75664d74ca656b6.Source
