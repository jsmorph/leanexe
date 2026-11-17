import TestSupport.A64.WasiElf

/-!
The command `a64-wasi emit DIR` writes the AArch64 back end's WASI executables, which
`tests/linux/a64-wasi.sh` runs: DIR/readall.elf, DIR/environ.elf, and DIR/args.elf, the files of
`readAllElf`, `environElf`, and `argsElf` of `TestSupport.A64.WasiElf`.  It prints the generator's
error and exits with status 1 when the generator rejects a module.
-/

open TestSupport.A64.WasiElf

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      let mut status : UInt32 := 0
      for (name, elf) in [("readall", readAllElf), ("environ", environElf), ("args", argsElf)] do
        match elf with
        | .error e =>
            IO.println s!"fail: {name}: the executable: {e}"
            status := 1
        | .ok (bytes, _) => IO.FS.writeBinFile s!"{dir}/{name}.elf" (ByteArray.mk bytes.toArray)
      return status
  | _ =>
      IO.eprintln "usage: a64-wasi emit DIR"
      return 2
