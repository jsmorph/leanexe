import LeanExe.A64.Boot

/-!
The startup places a level-1 translation table of 32 bytes, aligned to 32 bytes, in the image and
writes its address to `TTBR0_EL1`.  Each valid descriptor maps one GiB of the 32-bit input address
space as a block at the same addresses.  `tableWords` holds the descriptors, and `tableBytes` holds
the bytes of the image's copy.
-/

namespace LeanExe.A64

/-- The descriptors of the table, the lowest GiB first.  The first maps the GiB from 0 as
Device-nGnRnE memory, attribute index 0, with PXN and UXN set.  The second maps the GiB from
`0x40000000` as Normal Write-Back memory, attribute index 1, Inner Shareable, with UXN set and PXN
clear.  Both set the access flag and set AP[2:1] to 0b00, which allows reads and writes at EL1 and
no access at EL0.  The last two are invalid, so translation of an address from `0x80000000`
faults. -/
def tableWords : List UInt64 := [0x0060000000000401, 0x0040000040000705, 0, 0]

/-- The bytes of the table, each descriptor's lowest byte first. -/
def tableBytes : List UInt8 := tableWords.flatMap fun w => (List.range 8).map (byteOf w)

end LeanExe.A64
