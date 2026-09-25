import LeanExe.Examples.Drone

def main (args : List String) : IO UInt32 := do
  let mut terrain : Array UInt64 := #[]
  for arg in args do
    match arg.toNat? with
    | none =>
      IO.eprintln s!"invalid unsigned elevation: {arg}"
      return 2
    | some n =>
      if n > 18446744073709551615 then
        IO.eprintln "elevation does not fit UInt64"
        return 2
      terrain := terrain.push n.toUInt64
  let result := LeanExe.Examples.Drone.compute terrain
  IO.println ("[" ++ String.intercalate ", " (result.toList.map (fun x => toString x.toNat)) ++ "]")
  return 0
