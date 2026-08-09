namespace LeanExeGen.GeneratedR1b9b2027715ddee5.Source

def scalarIdentity (value : UInt64) : UInt64 := Id.run do
  let mut remaining := value
  let mut result : UInt64 := 0
  while remaining != 0 do
    remaining := remaining - 1
    result := result + 1
  return result

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size == 1 then
    #[scalarIdentity input[0]!]
  else
    input

end LeanExeGen.GeneratedR1b9b2027715ddee5.Source
