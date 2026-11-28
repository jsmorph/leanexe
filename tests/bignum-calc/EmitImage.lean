import Demos.BignumCalc.BytesBare

/-!
Writes the AArch64 Image of the calculator, the bytes of `Demos.BignumCalc.image`, to the path
given, and prints its size, its number of program instructions, the bytes of memory that it uses
from its base, and the stack's bound of `calcBytes`.  `Demos/BignumCalc/Image.lean` compares the
file with the generator's bytes in the kernel.
Usage: lake env lean --run tests/bignum-calc/EmitImage.lean IMAGE
-/

open Demos.BignumCalc LeanExe.A64

def main : List String → IO UInt32
  | [path] =>
      match image with
      | .ok (bytes, layout) => do
          IO.FS.writeBinFile path ⟨bytes.toArray⟩
          IO.println s!"emit-image: {path}: {bytes.length} bytes, \
            {imageBytesProgLength messageCompiled.module imageEntry imageMax imageRoom imageCap
              imageBase} instructions, memory {layout.size} bytes, stack bound \
            {stackBound messageCompiled.module imageEntry} bytes"
          pure 0
      | .error e => do
          IO.eprintln s!"emit-image: {e}"
          pure 1
  | _ => throw <| IO.userError "usage: EmitImage.lean IMAGE"
