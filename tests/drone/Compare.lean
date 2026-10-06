import Examples.Drone.Program

/-! Compares `compute` with the reference implementation's on every case of
`tests/drone/corpus.txt`.  Run with `lake env lean --run tests/drone/Compare.lean`. -/

def parse (text : String) : Array UInt64 :=
  if text.isEmpty then #[] else (text.splitOn ",").toArray.map fun w => w.toNat!.toUInt64

def main : IO UInt32 := do
  let lines := (← IO.FS.lines "tests/drone/corpus.txt").filter (!·.isEmpty)
  let mut failed := 0
  for line in lines do
    let [terrain, expected] := line.splitOn "|" | throw <| IO.userError s!"bad line: {line}"
    let got := Examples.Drone.compute (parse terrain)
    if got != parse expected then
      failed := failed + 1
      IO.println s!"fail: {terrain}"
  IO.println s!"drone corpus: {lines.size} cases, {failed} failed"
  return if failed == 0 then 0 else 1
