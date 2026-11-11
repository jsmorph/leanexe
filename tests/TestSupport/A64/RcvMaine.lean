import Demos.Rcv.Maine.Tabulate
import TestSupport.A64.Rcv

/-!
The Maine tabulator as a bare-metal program that reads its input from the UART: `tabulate`,
function 64 of `Demos.Rcv.Maine.TabulateProgram.compiled.module`, on a canonical file of at most
`inMax` bytes, the limit of `TestSupport.A64.Rcv`, in the image of `genBytesImage` at `imageBase`,
whose entry routine is that of the Oakland tabulator's image.  The bound of the Maine `tabulate`,
`80 L + 33,958,029` bytes for a file of `L` bytes, exceeds the Oakland module's by 255,120 bytes, so
the memory's cap, `maineCap` pages, is 3 pages larger than `rcvCap`.  The stack's room `room` of
`TestSupport.A64.Programs` holds the 6,272 bytes of `stackBound` of `tabulate`.
`TestSupport.A64.RcvMaineRuns` states the program's theorem.
-/

namespace TestSupport.A64.RcvMaine

open LeanExe.A64 TestSupport.A64

/-- The index of `tabulate` among the functions of the Maine module. -/
def entry : Nat := 64

/-- The memory's cap in pages: room above the heap's `top` for the block of a file of `inMax`
bytes and for the bound of `tabulate` on it. -/
def maineCap : Nat := 11395

/-- The image of the Maine tabulator's program at `imageBase`. -/
def image : Except String (List UInt8 × Layout) :=
  genBytesImage Demos.Rcv.Maine.TabulateProgram.compiled.module entry Rcv.inMax room maineCap
    imageBase

end TestSupport.A64.RcvMaine
