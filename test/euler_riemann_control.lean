import Project.EulerRiemann.Control

def main : IO Unit := do
  for n in [0, 1, 2, 3, 801] do
    let values := Project.EulerRiemann.Control.solve n
    IO.println (String.intercalate " "
      (toString n :: values.toList.map (fun word => toString word.toNat)))
