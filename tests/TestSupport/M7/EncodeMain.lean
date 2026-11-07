import TestSupport.M7.Asm

/-!
The command `m7-encode` of the comparison of the Cortex-M7 encoder with the GNU assembler.
`m7-encode gen OUT` writes to OUT the assembly of the samples of `TestSupport.M7.samples`.
`m7-encode check BIN` compares the bytes BIN, the assembler's `.text` of that file, with the
encoder's halfwords of each sample and decodes the assembler's halfwords of each sample, prints
every difference and a summary, and exits with status 1 when a sample differs.
-/

open TestSupport.M7

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
      IO.println (s!"m7-encode: {samples.length} samples of {forms.length} forms, " ++
        s!"{diffs.length} differences")
      return if diffs.isEmpty then 0 else 1
  | _ =>
      IO.eprintln "usage: m7-encode gen OUT | m7-encode check BIN"
      return 2
