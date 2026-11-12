import TestSupport.A64.FlipElf

/-!
The command `a64-elf emit DIR` of the AArch64 back end's Linux executables.  It writes DIR/flip.elf,
the file of `TestSupport.A64.FlipElf.elf`, and for each length `n` of
`TestSupport.A64.FlipElf.cases` the message, DIR/flip-n.in, and its bytes with bit 5 flipped,
DIR/flip-n.want, and for each length of `TestSupport.A64.FlipElf.overLengths` the message,
DIR/flipover-n.in.  `tests/linux/a64-elf.sh` reads the files.
-/

open TestSupport.A64.FlipElf

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      match elf with
      | .error e =>
          IO.println s!"fail: flip: the executable: {e}"
          return 1
      | .ok (bytes, _) =>
          IO.FS.writeBinFile s!"{dir}/flip.elf" (ByteArray.mk bytes.toArray)
          for n in cases do
            let msg := messageArray n
            IO.FS.writeBinFile s!"{dir}/flip-{n}.in" msg
            IO.FS.writeBinFile s!"{dir}/flip-{n}.want" (flipArray msg)
          for n in overLengths do
            IO.FS.writeBinFile s!"{dir}/flipover-{n}.in" (messageArray n)
          return 0
  | _ =>
      IO.eprintln "usage: a64-elf emit DIR"
      return 2
