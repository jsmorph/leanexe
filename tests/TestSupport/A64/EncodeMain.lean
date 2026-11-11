import TestSupport.A64.Asm

/-!
The command `a64-encode` of the comparison of the AArch64 encoder with the GNU assembler.
`a64-encode gen OUT` writes to OUT the assembly of the samples of `TestSupport.A64.samples`.
`a64-encode check BIN` compares the bytes BIN, the assembler's `.text` of that file, with the
encoder's word of each sample and decodes the assembler's word of each sample, prints every
difference and a summary, and exits with status 1 when a sample differs.
-/

open TestSupport.A64

def main (args : List String) : IO UInt32 := do
  match args with
  | ["gen", out] =>
      IO.FS.writeFile out samplesAsm
      return 0
  | ["check", bin] =>
      let diffs := checkBytes (← IO.FS.readBinFile bin)
      for d in diffs do
        IO.println s!"differ: {d}"
      let forms := (samples.map formName).eraseDups
      IO.println (s!"a64-encode: {samples.length} samples of {forms.length} forms, " ++
        s!"{diffs.length} differences")
      return if diffs.isEmpty then 0 else 1
  | _ =>
      IO.eprintln "usage: a64-encode gen OUT | a64-encode check BIN"
      return 2
