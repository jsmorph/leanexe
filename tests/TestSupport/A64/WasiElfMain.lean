import TestSupport.A64.WasiElf
import TestSupport.A64.WasiStringEdges
import LeanExe.Encoding.Decode

/-!
The command `a64-wasi emit DIR` writes the AArch64 back end's WASI executables, which
`tests/linux/a64-wasi.sh`, `tests/linux/a64-wasi-preopen.sh`, and
`tests/linux/a64-wasi-files.sh` run: DIR/readall.elf, DIR/environ.elf, DIR/args.elf,
DIR/prestat.elf, DIR/clockrandom.elf, DIR/sys.elf, and DIR/files.elf, the files of `readAllElf`,
`environElf`, `argsElf`, `prestatElf`, `clockRandomElf`, `sysElf`, and `filesElf` of
`TestSupport.A64.WasiElf`, and for each case of `TestSupport.A64.WasiStringEdges.edgeCases`
DIR/NAME.elf, with DIR/edges.txt, which lists each case as its name, `sizes` or `strings`, and its
two pointers and its window in decimal.  The command `a64-wasi wasm IN OUT` writes to OUT the
executable of the module whose binary IN holds, with `_start` at the function that the module
exports under that name and the memory's cap and the stack's room of the commands.  The command
`a64-wasi module IN OUT CAP ...` writes, for each triple, the executable of the module file IN with
a memory's cap of CAP pages to OUT, and prints the area's address, as
`tests/linux/a64-wasi-clocks.sh` uses.  Each prints the generator's error and exits with status 1
when the generator rejects a module.
-/

open LeanExe.A64 TestSupport.A64.WasiElf TestSupport.A64.WasiStringEdges

/-- Writes the executable `elf` to `path`, or prints the generator's error for `name`. -/
def writeElf (name path : String) (elf : Except String (List UInt8 × ElfLayout)) : IO UInt32 :=
  match elf with
  | .error e => do
      IO.println s!"fail: {name}: the executable: {e}"
      return 1
  | .ok (bytes, _) => do
      IO.FS.writeBinFile path (ByteArray.mk bytes.toArray)
      return 0

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
          if (← writeElf inp out elf) != 0 then return 1
          if let .ok (_, L) := elf then IO.println s!"{out}: area {L.area.toNat}"
          modules rest
  | _ => do
      IO.eprintln "usage: a64-wasi module (IN OUT CAP)..."
      return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      let mut status : UInt32 := 0
      let mut files := [("readall", readAllElf), ("environ", environElf), ("args", argsElf),
        ("prestat", prestatElf), ("clockrandom", clockRandomElf), ("sys", sysElf),
        ("files", filesElf)]
      let mut lines : List String := []
      for (name, sizes, p, q, w) in edgeCases do
        files := files ++ [(name, edgeElf sizes p q w)]
        lines := lines ++ [s!"{name} {if sizes then "sizes" else "strings"} {p} {q} {w}"]
      for (name, elf) in files do
        status := max status (← writeElf name s!"{dir}/{name}.elf" elf)
      IO.FS.writeFile s!"{dir}/edges.txt" (String.intercalate "\n" lines ++ "\n")
      return status
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
  | "module" :: rest => modules rest
  | _ =>
      IO.eprintln
        "usage: a64-wasi emit DIR | a64-wasi wasm IN OUT | a64-wasi module (IN OUT CAP)..."
      return 2
