import TestSupport.A64.WasiElf
import LeanExe.Encoding.Decode

/-!
The command `a64-wasi emit DIR` writes the AArch64 back end's WASI executables, which
`tests/linux/a64-wasi.sh` runs: DIR/readall.elf, DIR/environ.elf, DIR/args.elf, and
DIR/clockrandom.elf, the files of `readAllElf`, `environElf`, `argsElf`, and `clockRandomElf` of
`TestSupport.A64.WasiElf`.  `a64-wasi module IN OUT CAP ...`
writes, for each triple, the executable of the module file IN with a memory's cap of CAP pages to
OUT, and prints the area's address, as `tests/linux/a64-wasi-clocks.sh` uses.  Each prints the
generator's error and exits with status 1 when the generator rejects a module.
-/

open TestSupport.A64.WasiElf

/-- Writes the executable `elf` to `path`, or prints the generator's error for `name`. -/
def writeElf (name path : String) (elf : Except String (List UInt8 × LeanExe.A64.ElfLayout)) :
    IO Bool := do
  match elf with
  | .error e =>
      IO.println s!"fail: {name}: the executable: {e}"
      return false
  | .ok (bytes, _) =>
      IO.FS.writeBinFile path (ByteArray.mk bytes.toArray)
      return true

/-- Writes the executables of the triples `IN OUT CAP` of `args`. -/
def modules : List String → IO UInt32
  | [] => return 0
  | inp :: out :: cap :: rest => do
      match Wasm.Encoding.decode (← IO.FS.readBinFile inp) with
      | .error e =>
          IO.println s!"fail: {inp}: the module does not decode: {repr e}"
          return 1
      | .ok m =>
          let elf := moduleElf m cap.toNat!
          unless ← writeElf inp out elf do return 1
          if let .ok (_, L) := elf then IO.println s!"{out}: area {L.area.toNat}"
          modules rest
  | _ => do
      IO.eprintln "usage: a64-wasi module (IN OUT CAP)..."
      return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      let mut status : UInt32 := 0
      for (name, elf) in [("readall", readAllElf), ("environ", environElf), ("args", argsElf),
          ("clockrandom", clockRandomElf)] do
        unless ← writeElf name s!"{dir}/{name}.elf" elf do status := 1
      return status
  | "module" :: rest => modules rest
  | _ =>
      IO.eprintln "usage: a64-wasi emit DIR | a64-wasi module (IN OUT CAP)..."
      return 2
