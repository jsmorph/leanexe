import Demos.RunningSum.Stream

private structure Case where
  name : String
  input : String
  output : String
  status : UInt64 := 0

private def cases : Array Case := Id.run do
  let nines := String.ofList (List.replicate 5000 '9')
  let power := "1" ++ String.ofList (List.replicate 5000 '0')
  let mut lines := ""
  let mut sums := ""
  let mut total : Int := 0
  for index in [:1000] do
    let value : Int := if index % 3 == 0 then -(index : Int) else index
    total := total + value
    lines := lines ++ toString value ++ "\n"
    sums := sums ++ toString total ++ "\n"
  return #[
    ⟨"empty", "", "", 0⟩,
    ⟨"lines", "12\n-5\n20\n", "12\n7\n27\n", 0⟩,
    ⟨"final-line", "12\n-5\n20", "12\n7\n27\n", 0⟩,
    ⟨"crlf", "+00012\r\n-00012\r\n-0\n", "12\n0\n0\n", 0⟩,
    ⟨"negative", "-9\n-2\n+1", "-9\n-11\n-10\n", 0⟩,
    ⟨"empty-line", "\n", "", 28⟩,
    ⟨"sign-only", "+\n", "", 28⟩,
    ⟨"malformed", "1\n2x\n3\n", "1\n", 28⟩,
    ⟨"leading-space", " 1\n", "", 28⟩,
    ⟨"trailing-space", "1 \n", "", 28⟩,
    ⟨"nul", "1\n2\x00\n", "1\n", 28⟩,
    ⟨"empty-final", "1\n", "1\n", 0⟩,
    ⟨"long-carry", nines ++ "\n1\n-" ++ power, nines ++ "\n" ++ power ++ "\n0\n", 0⟩,
    ⟨"many-lines", lines, sums, 0⟩]

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments
    | throw (IO.userError "Usage: Cases.lean OUTPUT_DIRECTORY")
  let root : System.FilePath := directory
  IO.FS.createDirAll root
  let mut manifest := ""
  for test in cases do
    IO.FS.writeBinFile (root / s!"{test.name}.input") test.input.toUTF8
    IO.FS.writeBinFile (root / s!"{test.name}.expected") test.output.toUTF8
    manifest := manifest ++ s!"{test.name}\t{test.status}\n"
  IO.FS.writeFile (root / "cases.tsv") manifest
  IO.println s!"Running sum execution corpus: {cases.size} cases"
