import TestSupport.A64.WasiElf

/-!
The command `a64-wasi emit DIR` writes the AArch64 back end's WASI executables: DIR/readall.elf,
the file of `TestSupport.A64.WasiElf.readAllElf`, which `tests/linux/a64-wasi.sh` runs.  It
prints the generator's error and exits with status 1 when the generator rejects the module.
-/

open TestSupport.A64.WasiElf

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      match readAllElf with
      | .error e =>
          IO.println s!"fail: readAll: the executable: {e}"
          return 1
      | .ok (bytes, _) =>
          IO.FS.writeBinFile s!"{dir}/readall.elf" (ByteArray.mk bytes.toArray)
          return 0
  | _ =>
      IO.eprintln "usage: a64-wasi emit DIR"
      return 2
