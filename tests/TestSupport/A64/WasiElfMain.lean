import TestSupport.A64.WasiElf
import TestSupport.A64.WasiStringEdges

/-!
The command `a64-wasi emit DIR` writes the AArch64 back end's WASI executables, which
`tests/linux/a64-wasi.sh` runs: DIR/readall.elf, DIR/environ.elf, and DIR/args.elf, the files of
`readAllElf`, `environElf`, and `argsElf` of `TestSupport.A64.WasiElf`, and for each case of
`TestSupport.A64.WasiStringEdges.edgeCases` DIR/NAME.elf, with DIR/edges.txt, which lists each case
as its name, `sizes` or `strings`, and its two pointers and its window in decimal.  It prints the
generator's error and exits with status 1 when the generator rejects a module.
-/

open TestSupport.A64.WasiElf TestSupport.A64.WasiStringEdges

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      let mut status : UInt32 := 0
      let mut files := [("readall", readAllElf), ("environ", environElf), ("args", argsElf)]
      let mut lines : List String := []
      for (name, sizes, p, q, w) in edgeCases do
        files := files ++ [(name, edgeElf sizes p q w)]
        lines := lines ++ [s!"{name} {if sizes then "sizes" else "strings"} {p} {q} {w}"]
      for (name, elf) in files do
        match elf with
        | .error e =>
            IO.println s!"fail: {name}: the executable: {e}"
            status := 1
        | .ok (bytes, _) => IO.FS.writeBinFile s!"{dir}/{name}.elf" (ByteArray.mk bytes.toArray)
      IO.FS.writeFile s!"{dir}/edges.txt" (String.intercalate "\n" lines ++ "\n")
      return status
  | _ =>
      IO.eprintln "usage: a64-wasi emit DIR"
      return 2
