import Demos.Rcv.Maine.Tabulate

/-! The executable `rcv-maine-bound`: for each file, one line with its path, its size in bytes, and
`compiled.tabulate.bound` of its bytes, the bound of the Maine module's call theorem
`Demos.Rcv.Maine.TabulateProgram.tabulate_callSpec`.  `tests/rcv/page.mjs --count maine --bounds`
reads the lines. -/

open Demos.Rcv.Maine.TabulateProgram

def main (paths : List String) : IO Unit := do
  let out ← IO.getStdout
  for path in paths do
    let data ← IO.FS.readBinFile path
    out.putStrLn s!"{path} {data.size} {compiled.tabulate.bound ⟨data⟩}"
    out.flush
