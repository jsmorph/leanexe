import LeanExe.WGSL.Examples.Body
import Interpreter.Wasm.IEEE32

open LeanExe.WGSL
open LeanExe.WGSL.Examples.Body

private def words : Array UInt32 :=
  #[0x3f800000, 0xc0000000, 0x3f000000, 0x40400000,
    0xbf800000, 0x3fa00000, 0xbe800000, 0x40000000]

/-- Expected results execute the original source declaration with the pure,
integer-defined IEEE32 operations. They do not evaluate the extracted tree. -/
private def vectors (entry : Source.Kernel) (shape : Source.Shape) : Lean.Json := Id.run do
  let a := (List.range shape.elementsA).map fun i => words[i % words.size]!
  let b := (List.range shape.elementsB).map fun i => words[(i + 3) % words.size]!
  let arithmetic : ScalarArithmetic := ⟨Wasm.IEEE32.add, Wasm.IEEE32.mul⟩
  let expected := (List.range (shape.rows * shape.cols)).map fun i =>
    entry arithmetic (fun n => a[n]?.getD 0) (fun n => b[n]?.getD 0)
      (i / shape.cols) (i % shape.cols)
  return Lean.Json.mkObj [
    ("a", Lean.toJson (a.map UInt32.toNat)), ("b", Lean.toJson (b.map UInt32.toNat)),
    ("expected", Lean.toJson (expected.map UInt32.toNat))]

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Vectors.lean OUTPUT_DIRECTORY")
  let directory : System.FilePath := directory
  IO.FS.createDirAll directory
  for (name, entry, shape) in cases do
    IO.FS.writeFile (directory / s!"{name}.json") (vectors entry shape).pretty
    IO.println s!"Computed original Lean definition: {name}"
