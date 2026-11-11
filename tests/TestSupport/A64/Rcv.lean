import Demos.Rcv.Tabulate
import TestSupport.A64.Programs

/-!
The Oakland tabulator as a bare-metal program that reads its input from the UART: `tabulate`,
function 63 of `Demos.Rcv.TabulateProgram.compiled.module`, which takes a canonical file as a
buffer of bytes and returns its report.  The image of `genBytesImage` at `imageBase` reads a
length of eight bytes, the lowest first, and a file of that many bytes, at most `inMax`, and writes
the file's report and the status 0, the status 64 for a length above `inMax`, or the status 65 for
a byte with an error flag.  The memory's cap, `rcvCap` pages, holds the file's block and the bound
of `tabulate` above the heap's `top` for every file of at most `inMax` bytes, and the stack's room
`room` of `TestSupport.A64.Programs`, 512 KiB, holds the 6,240 bytes of `stackBound` of
`tabulate`.  `TestSupport.A64.RcvRuns` states the program's theorem.
-/

namespace TestSupport.A64.Rcv

open LeanExe.A64 TestSupport.A64

/-- The index of `tabulate` among the functions of the module. -/
def entry : Nat := 63

/-- The largest length of a file: 8,800,000 bytes. -/
def inMax : UInt64 := 8800000

/-- The memory's cap in pages: room above the heap's `top` for the block of a file of `inMax`
bytes and for the bound of `tabulate` on it, `80 L + 33,702,909` bytes for a file of `L` bytes. -/
def rcvCap : Nat := 11392

/-- The image of the tabulator's program at `imageBase`. -/
def image : Except String (List UInt8 × Layout) :=
  genBytesImage Demos.Rcv.TabulateProgram.compiled.module entry inMax room rcvCap imageBase

end TestSupport.A64.Rcv
