import TestSupport.A64.Rcv
import TestSupport.A64.RcvMaine

/-!
The command `a64-rcv emit DIR` of the tabulators' AArch64 images, which read a canonical file from
the UART.  It writes DIR/rcv.img, the image of `TestSupport.A64.Rcv.image`, the Oakland tabulator,
and DIR/maine.img, the image of `TestSupport.A64.RcvMaine.image`, the Maine tabulator, which
`tests/baremetal/a64-rcv.sh` runs.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] =>
      for (name, image) in [("rcv", TestSupport.A64.Rcv.image),
          ("maine", TestSupport.A64.RcvMaine.image)] do
        match image with
        | .error e =>
            IO.println s!"fail: {name}: the image: {e}"
            return 1
        | .ok (img, _) => IO.FS.writeBinFile s!"{dir}/{name}.img" (ByteArray.mk img.toArray)
      return 0
  | _ =>
      IO.eprintln "usage: a64-rcv emit DIR"
      return 2
