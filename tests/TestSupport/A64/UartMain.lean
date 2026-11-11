import TestSupport.A64.Uart
import TestSupport.A64.Flip

/-!
The command `a64-uart emit DIR` of the AArch64 images that read their input from the UART.  It
writes DIR/gcduart.img, the image of `TestSupport.A64.Uart.image`, and for each pair `i` of
`TestSupport.A64.Uart.cases` the bytes that the UART delivers, DIR/gcduart-i.in, and the bytes
that it must show, DIR/gcduart-i.want.  It writes DIR/flip.img, the image of
`TestSupport.A64.Flip.image`, and for each length `n` of `TestSupport.A64.Flip.cases`, DIR/flip-n.in
and DIR/flip-n.want, and for each length `L` above `inMax` of `TestSupport.A64.Flip.overLengths`,
DIR/flipover-L.in, the eight bytes of `L`, and DIR/flipover-L.want, the status 64.
`tests/baremetal/a64-uart.sh` reads the files.
-/

def writeBytes (path : String) (bs : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path (ByteArray.mk bs.toArray)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      match TestSupport.A64.Uart.image, TestSupport.A64.Flip.image with
      | .error e, _ =>
          IO.println s!"fail: gcduart: the image: {e}"
          return 1
      | _, .error e =>
          IO.println s!"fail: flip: the image: {e}"
          return 1
      | .ok (img, _), .ok (flipImg, _) =>
          writeBytes s!"{dir}/gcduart.img" img
          for (c, i) in TestSupport.A64.Uart.cases.zipIdx do
            writeBytes s!"{dir}/gcduart-{i}.in" (TestSupport.A64.Uart.input c)
            writeBytes s!"{dir}/gcduart-{i}.want" (TestSupport.A64.Uart.expected c)
          writeBytes s!"{dir}/flip.img" flipImg
          for n in TestSupport.A64.Flip.cases do
            writeBytes s!"{dir}/flip-{n}.in" (TestSupport.A64.Flip.input n)
            writeBytes s!"{dir}/flip-{n}.want" (TestSupport.A64.Flip.expected n)
          for L in TestSupport.A64.Flip.overLengths do
            writeBytes s!"{dir}/flipover-{L}.in" (LeanExe.A64.bytesOf L)
            writeBytes s!"{dir}/flipover-{L}.want" [64]
          return 0
  | _ =>
      IO.eprintln "usage: a64-uart emit DIR"
      return 2
