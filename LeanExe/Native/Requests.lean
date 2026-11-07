/-!
The requests of a step in the program with requests (`reqMain` of `LeanExe/Native/Bare.lean`),
as functions of the verified compiler's dialect.  `main` writes the low 32 bits of a request
whose bit 63 is set to the register `(q >> 32) & 65535` of `lx_reg`, and reads that register
otherwise.  Each request is a sum of fields whose bits do not overlap, so that its properties
reduce to linear arithmetic on its value.
-/

namespace LeanExe.Native

/-- The request that reads register `r`. -/
def readReq (r : UInt64) : UInt64 := r * 4294967296

/-- The request that writes the low 32 bits of `v` to register `r`. -/
def writeReq (r v : UInt64) : UInt64 := 9223372036854775808 + r * 4294967296 + v % 4294967296

end LeanExe.Native
