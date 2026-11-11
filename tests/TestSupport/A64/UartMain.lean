import TestSupport.A64.Uart

/-!
The command `a64-uart emit DIR` of the AArch64 image that reads its arguments from the UART.  It
writes DIR/gcduart.img, the image of `TestSupport.A64.Uart.image`, and for each pair `i` of
`TestSupport.A64.Uart.cases` the bytes that the UART delivers, DIR/gcduart-i.in, and the bytes
that it must show, DIR/gcduart-i.want, which `tests/baremetal/a64-uart.sh` reads.
-/

open TestSupport.A64.Uart

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      match image with
      | .error e =>
          IO.println s!"fail: gcduart: the image: {e}"
          return 1
      | .ok (img, _) =>
          IO.FS.writeBinFile s!"{dir}/gcduart.img" (ByteArray.mk img.toArray)
          for (c, i) in cases.zipIdx do
            IO.FS.writeBinFile s!"{dir}/gcduart-{i}.in" (ByteArray.mk (input c).toArray)
            IO.FS.writeBinFile s!"{dir}/gcduart-{i}.want" (ByteArray.mk (expected c).toArray)
          return 0
  | _ =>
      IO.eprintln "usage: a64-uart emit DIR"
      return 2
