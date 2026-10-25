import Demos.RunningSumFp.Stream

private structure Case where
  name : String
  input : String
  output : String
  status : UInt64 := 0

private def cases : Array Case := Id.run do
  let zeros := String.ofList (List.replicate 5000 '0')
  let manyInput := String.ofList ((List.replicate 500 "1\n-1\n").flatMap String.toList)
  let manyOutput := String.ofList ((List.replicate 500 "1e0\n0e0\n").flatMap String.toList)
  return #[
    ⟨"empty", "", "", 0⟩,
    ⟨"lines", "12\n-5\n20\n", "1.2e1\n7e0\n2.7e1\n", 0⟩,
    ⟨"final-line", "12\n-5\n20", "1.2e1\n7e0\n2.7e1\n", 0⟩,
    ⟨"crlf", "+00012\r\n-00012\r\n-0\n", "1.2e1\n0e0\n0e0\n", 0⟩,
    ⟨"decimal-rounding", "0.1\n0.2\n-0.3\n",
      "1e-1\n3.0000000000000004e-1\n5.551115123125783e-17\n", 0⟩,
    ⟨"ties-to-even", "9007199254740993\n1\n-9007199254740992\n",
      "9.007199254740992e15\n9.007199254740992e15\n0e0\n", 0⟩,
    ⟨"sequential-cancellation", "1e16\n1\n-1e16\n", "1e16\n1e16\n0e0\n", 0⟩,
    ⟨"subnormals", "5e-324\n5e-324\n-1e-323\n", "5e-324\n1e-323\n0e0\n", 0⟩,
    ⟨"positive-overflow", "1e308\n1e308\n-1e308\n", "1e308\nInfinity\nInfinity\n", 0⟩,
    ⟨"negative-overflow", "-1e308\n-1e308\n1e308\n", "-1e308\n-Infinity\n-Infinity\n", 0⟩,
    ⟨"infinities", "Infinity\n1\n-Infinity\n2\n", "Infinity\nInfinity\nNaN\nNaN\n", 0⟩,
    ⟨"nan", "-NaN\n1\n", "NaN\nNaN\n", 0⟩,
    ⟨"signed-zero", "-0\n0\n-0\n", "0e0\n0e0\n0e0\n", 0⟩,
    ⟨"underflow", "-1e-400\n1e-400\n", "0e0\n0e0\n", 0⟩,
    ⟨"parse-overflow", "1e400\n-1e400\n", "Infinity\nNaN\n", 0⟩,
    ⟨"general-grammar", "0x1.8p1\n-0x1p0\n.5\n+1.\n", "3e0\n2e0\n2.5e0\n3.5e0\n", 0⟩,
    ⟨"long-line", zeros ++ "1.25\n-1.25", "1.25e0\n0e0\n", 0⟩,
    ⟨"many-lines", manyInput, manyOutput, 0⟩,
    ⟨"empty-line", "\n", "", 28⟩,
    ⟨"sign-only", "+\n", "", 28⟩,
    ⟨"malformed", "1\n2x\n3\n", "1e0\n", 28⟩,
    ⟨"leading-space", " 1\n", "", 28⟩,
    ⟨"trailing-space", "1 \n", "", 28⟩,
    ⟨"incomplete-exponent", "1e\n", "", 28⟩,
    ⟨"hex-without-exponent", "0x10\n", "", 28⟩,
    ⟨"double-cr", "1\r\r\n", "", 28⟩,
    ⟨"nul", "1\n2\x00\n", "1e0\n", 28⟩]

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
  IO.println s!"Running sumfp execution corpus: {cases.size} cases"
