import Project.EulerRiemann.TraversalTest

def main : IO Unit := do
  for n in [2, 3, 5] do
    for advance in [false, true] do
      let values := Project.EulerRiemann.TraversalTest.sample n advance
      IO.println (String.intercalate " "
        ([toString n, if advance then "1" else "0"] ++
          values.toList.map (fun word => toString word.toNat)))
