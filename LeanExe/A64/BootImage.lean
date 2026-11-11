import LeanExe.A64.Startup
import LeanExe.A64.Table

/-!
The bytes of a program's arm64 Image, laid out as `LeanExe.A64.Startup` describes: the header,
the startup and the program, zeros to the vector table, the vector table, the translation table,
zeros to the area, and the area's first `areaPrefix` bytes.  The parts are joined from the right,
so that the kernel's evaluation of the bytes passes each byte of the code through one append.
-/

namespace LeanExe.A64

open Wasm

/-- The image of the program that `gp` gives from its base, at `image`, with an area of `cap`
pages for the module `m` and a stack of `room` bytes: its bytes and its layout.  The image must end
within the GiB of RAM from `0x40000000`, and the area's prefix must fit in the area. -/
def genImageWith (gp : UInt64 → GenM (List Instr)) (m : Module) (room : UInt64) (cap : Nat)
    (image : UInt64) : GenM (List UInt8 × Layout) := do
  let prog ← gp (image + UInt64.ofNat (64 + 4 * startupLength))
  let L := layoutOf image prog.length m cap room
  unless 0x40000000 ≤ image.toNat ∧ image.toNat + L.size ≤ 0x80000000 ∧
      areaPrefix m ≤ areaSize cap do
    throw s!"an image of {L.size} bytes at {image} outside the GiB of RAM, or data past its area"
  let start ← startupCode L
  let pad1 := (L.vectors - image).toNat - 64 - 4 * (start.length + prog.length)
  let pad2 := (L.area - L.table).toNat - 32
  let bytes := imageHeader L.size ++ (imageBytes (start ++ prog) ++ (List.replicate pad1 0 ++
    (vectorBytes ++ (tableBytes ++ (List.replicate pad2 0 ++ areaPrefixBytes m)))))
  return (bytes, L)

/-- The image of the program that runs function `k` of `m` on `args` and writes its result as
`o`, at `image`, with an area of `cap` pages and a stack of `room` bytes. -/
def genImage (m : Module) (k : Nat) (args : List UInt64) (room : UInt64) (cap : Nat)
    (o : Output) (image : UInt64) : GenM (List UInt8 × Layout) :=
  genImageWith (fun base => genProgram m k args uartAddr base room cap o) m room cap image

/-- The image of the program that runs function `k` of `m` on `n` words read from the UART and
writes its result as `o`, at `image`, with an area of `cap` pages and a stack of `room` bytes. -/
def genInImage (m : Module) (k n : Nat) (room : UInt64) (cap : Nat) (o : Output)
    (image : UInt64) : GenM (List UInt8 × Layout) :=
  genImageWith (fun base => genInProgram m k n uartAddr base room cap o) m room cap image

end LeanExe.A64
