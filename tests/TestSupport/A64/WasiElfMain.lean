import TestSupport.A64.WasiElf
import LeanExe.Encoding.Decode

/-!
The command `a64-wasi emit DIR` writes the AArch64 back end's WASI executables: DIR/readall.elf
and DIR/prestat.elf, the files of `TestSupport.A64.WasiElf.readAllElf` and `prestatElf`, which
`tests/linux/a64-wasi.sh` and `tests/linux/a64-wasi-preopen.sh` run.  The command
`a64-wasi wasm IN OUT` writes to OUT the executable of the module whose binary IN holds, with
`_start` at the function that the module exports under that name and the memory's cap and the
stack's room of the commands.  Each prints the generator's error and exits with status 1 when the
generator rejects a module.
-/

open LeanExe.A64 TestSupport.A64.WasiElf

/-- Writes the executable `elf` to `path`, or prints the generator's error for `name`. -/
def writeElf (name path : String) (elf : Except String (List UInt8 × ElfLayout)) : IO UInt32 :=
  match elf with
  | .error e => do
      IO.println s!"fail: {name}: the executable: {e}"
      return 1
  | .ok (bytes, _) => do
      IO.FS.writeBinFile path (ByteArray.mk bytes.toArray)
      return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      let a ← writeElf "readAll" s!"{dir}/readall.elf" readAllElf
      let b ← writeElf "prestat" s!"{dir}/prestat.elf" prestatElf
      return max a b
  | ["wasm", input, output] =>
      match Wasm.Encoding.decode (← IO.FS.readBinFile input) with
      | .error e =>
          IO.println s!"fail: {input}: the module does not decode: {repr e}"
          return 1
      | .ok m =>
          match m.exports.find? (·.name = "_start") with
          | none =>
              IO.println s!"fail: {input}: no export _start"
              return 1
          | some e => writeElf input output (genWasiElf m e.funcIdx wasiRoom wasiCap)
  | _ =>
      IO.eprintln "usage: a64-wasi emit DIR | a64-wasi wasm IN OUT"
      return 2
