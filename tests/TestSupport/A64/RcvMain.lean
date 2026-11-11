import TestSupport.A64.Rcv

/-!
The command `a64-rcv emit DIR` of the tabulator's AArch64 image, which reads a canonical file from
the UART.  It writes DIR/rcv.img, the image of `TestSupport.A64.Rcv.image`, which
`tests/baremetal/a64-rcv.sh` runs.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      match TestSupport.A64.Rcv.image with
      | .error e =>
          IO.println s!"fail: rcv: the image: {e}"
          return 1
      | .ok (img, _) =>
          IO.FS.writeBinFile s!"{dir}/rcv.img" (ByteArray.mk img.toArray)
          return 0
  | _ =>
      IO.eprintln "usage: a64-rcv emit DIR"
      return 2
