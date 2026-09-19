import Project.Gpt2.PackedBody

open LeanExe.WGSL

/-! Test-only vectors. Expected words evaluate the original Lean definitions
with the pure IEEE32 interpretation. Host code only expands repeated bytes.
For biased products, [2^24, -2^24, 1, 0, ...] dotted with ones then biased by
one gives 2. Starting with the bias instead gives 1 and must fail this test. -/

private def input (i : Nat) : UInt32 :=
  if i == 0 then 0x4b800000 else if i == 1 then 0xcb800000
  else if i == 2 then 0x3f800000 else 0

private def repeated (count : Nat) (value : UInt32) : Lean.Json :=
  Lean.Json.mkObj [("count",Lean.toJson count),("word",Lean.toJson value.toNat)]

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: PackedVectors.lean DIRECTORY")
  let directory : System.FilePath := directory
  IO.FS.createDirAll directory
  let ar := Project.WGSL.Binary32.arithmetic
  let cases : List (String × Source.Kernel × Nat × Nat × Bool) := [
    ("qkv",Gpt2Packed.qkv,768,2304,true),
    ("attention",Gpt2Packed.attention,768,768,true),
    ("expansion",Gpt2Packed.expansion,768,3072,true),
    ("projection",Gpt2Packed.projection,3072,768,true),
    ("vocabularyLeft",Gpt2.vocabularyLeft,768,25129,false),
    ("vocabularyRight",Gpt2.vocabularyRight,768,25128,false)]
  for (name, kernel, inner, cols, bias) in cases do
    let expected := kernel ar input (fun _ => 0x3f800000) 0 (cols - 1)
    let data := Lean.Json.mkObj [
      ("a",Lean.toJson ((List.range inner).map fun i => (input i).toNat)),
      ("b",repeated (inner * cols + if bias then cols else 0) 0x3f800000),
      ("expected",repeated cols expected)]
    IO.FS.writeFile (directory / s!"{name}.json") data.pretty
    IO.println s!"{name}: original Lean definition returned word {expected.toNat}"
  let smallB : Nat → UInt32 := fun i => if i == 7 then 0xbf800000 else 0x3f800000
  let data := Lean.Json.mkObj [
    ("a",Lean.toJson ((List.range 3).map fun i => (input i).toNat)),
    ("b",Lean.toJson ((List.range 8).map fun i => (smallB i).toNat)),
    ("expected",Lean.toJson ((List.range 2).map fun col =>
      (Gpt2Packed.biased 3 2 ar input smallB 0 col).toNat))]
  IO.FS.writeFile (directory / "small.json") data.pretty
