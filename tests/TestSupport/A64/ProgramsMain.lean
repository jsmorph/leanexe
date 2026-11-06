import TestSupport.A64.Programs

/-!
The command `a64-programs emit DIR` of the AArch64 back end's bare-metal programs.  For each program
it writes DIR/NAME.img, the arm64 Image of `genImage` at `imageBase`, DIR/NAME.expected, the bytes
that the UART must show before the status byte, and DIR/NAME.status, the status with which the
program must end, which `tests/baremetal/a64-images.sh` reads.  It prints a line for each program
whose image the generator rejects and then exits with status 1.
-/

open TestSupport.A64

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      let mut status : UInt32 := 0
      for p in programs do
        match p.image with
        | .error e =>
            IO.println s!"fail: {p.name}: the image: {e}"
            status := 1
        | .ok (img, _) =>
            IO.FS.writeBinFile s!"{dir}/{p.name}.img" (ByteArray.mk img.toArray)
            IO.FS.writeBinFile s!"{dir}/{p.name}.expected" (ByteArray.mk p.bytes.toArray)
            IO.FS.writeFile s!"{dir}/{p.name}.status" s!"{p.status}\n"
      return status
  | _ =>
      IO.eprintln "usage: a64-programs emit DIR"
      return 2
