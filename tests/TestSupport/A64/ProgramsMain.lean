import TestSupport.A64.Programs
import TestSupport.A64.Gcd
import TestSupport.A64.Crc

/-!
The command `a64-programs emit DIR` of the AArch64 back end's bare-metal programs.  For each
program it generates and places the code, runs it in the model, which must write the program's
bytes and return status 0, and writes DIR/NAME.bin, the bytes of the instructions, DIR/NAME.area,
the bytes of the area, DIR/NAME.s, the assembly that includes both and that
`tests/baremetal/a64-programs.sh` links with the startup code, and DIR/NAME.expected, the bytes
that the UART must show.  DIR must be an absolute path, since the assembly names DIR/NAME.bin and
DIR/NAME.area.  It prints one line for each program and
exits with status 1 when a program fails.
-/

open LeanExe.A64 TestSupport.A64

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      let mut status : UInt32 := 0
      for p in programs do
        match p.code with
        | .error e =>
            IO.println s!"fail: {p.name}: {e}"
            status := 1
        | .ok code =>
            match run p.module code 10000000 with
            | .error e =>
                IO.println s!"fail: {p.name}: in the model, {e}"
                status := 1
            | .ok (out, x0, steps) =>
                if out = p.bytes ∧ x0 = 0 then
                  IO.println (s!"model: {p.name}: {out.length} bytes and status 0 after " ++
                    s!"{steps} steps of {code.length} instructions")
                else
                  IO.println s!"fail: {p.name}: in the model, bytes {out} and status {x0}"
                  status := 1
                IO.FS.writeBinFile s!"{dir}/{p.name}.bin" (ByteArray.mk (imageBytes code).toArray)
                IO.FS.writeBinFile s!"{dir}/{p.name}.area"
                  (ByteArray.mk (areaBytes p.module cap).toArray)
                IO.FS.writeFile s!"{dir}/{p.name}.s"
                  (stub s!"{dir}/{p.name}.bin" s!"{dir}/{p.name}.area")
                IO.FS.writeBinFile s!"{dir}/{p.name}.expected" (ByteArray.mk p.bytes.toArray)
      return status
  | _ =>
      IO.eprintln "usage: a64-programs emit DIR"
      return 2
