import Demos.Rcv.Maine.Cases
import TestSupport.Rcv.Cases

/-! The cases of the module `rcvMaine`, the Maine tabulator of `Demos/Rcv/Maine/Tabulate.lean`.
The export `count` takes word arrays and the export `tabulate` canonical files, and the expected
results are those of the Maine specification's `Demos.Rcv.Maine.countArray` and
`Demos.Rcv.Maine.reportFile` in native Lean.  The arrays are the contest words of the contests of
`TestSupport.Rcv.Cases`, its other arrays, its random contests, and the requirements' two Maine
examples.  The files are the canonical files of those contests, of the contests with identifiers and
names outside ASCII, the Maine examples, the 17-ballot example cut after each of its lines, and the
Oakland example's edits that each break one line.  The random contests leave about a third of the
positions empty, so their ballots hold runs of empty positions before marked ones.  Every array
and file passes through a file under `build/verified/rcvMaine/`, and a case requires two retained
blocks, the host's argument and the result. -/

namespace TestSupport.Rcv.MaineCases

open Demos.Rcv Demos.Rcv.Spec
open TestSupport.Rcv.Cases (contests arrays randoms randomContest contestOfArray hex
  tabulateContests edits)
open TestSupport.OrderBook.Words (wordBytes hostArray)

/-- The directory of the cases' files, relative to the repository's root. -/
def dir : System.FilePath := "build/verified/rcvMaine"

/-- Writes the array `ws` of the case `name` and prints the case of the export `count`. -/
def emit (name : String) (ws : Array UInt64) : IO Unit := do
  let path := dir / s!"{name}.bin"
  IO.FS.writeBinFile path (wordBytes ws)
  IO.println
    s!"rcvMaine|count|array-u64|file-u64:{path}|{hostArray (Demos.Rcv.Maine.countArray ws)}|2"

/-- Writes the file `bs` of the case `name` and prints the case of the export `tabulate`. -/
def emitFile (name : String) (bs : List UInt8) : IO Unit := do
  let path := dir / s!"{name}.rcv"
  IO.FS.writeBinFile path ⟨bs.toArray⟩
  IO.println s!"rcvMaine|tabulate|bytes|bytes-file:{path}|{hex (Demos.Rcv.Maine.reportFile bs)}|2"

/-- Writes the cases' files and prints the cases. -/
def cases : IO Unit := do
  IO.FS.createDirAll dir
  for (name, c) in contests do
    emit name (contestWords c).toArray
    emitFile name (write c)
  for (name, ws) in arrays do
    emit name ws.toArray
  for (seed, n, k, N, skewed) in randoms do
    let ws := ((randomContest n k N skewed).run' seed).run
    emit s!"random-{seed}" ws
    emitFile s!"random-{seed}" (write (contestOfArray ws))
  for (name, c) in tabulateContests do
    emitFile name (write c)
  for (name, file) in [("example-maine", Demos.Rcv.Maine.Cases.exampleFile),
      ("initial-test", Demos.Rcv.Maine.Cases.initialFile)] do
    emitFile name (ascii file)
    match read (ascii file) with
    | .ok c => emit name (contestWords c).toArray
    | .error _ _ => pure ()
  let ls := (ascii Demos.Rcv.Maine.Cases.exampleFile).splitOn 10
  for i in [0:ls.length] do
    emitFile s!"cut-{i}" (text (ls.take i))
  for (name, old, new) in edits do
    emitFile name (ascii (Demos.Rcv.Cases.exampleFile.replace old new))

end TestSupport.Rcv.MaineCases
