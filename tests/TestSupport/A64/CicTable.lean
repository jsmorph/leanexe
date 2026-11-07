import Library.Numerics.Filters.Cic.Program
import LeanExe.Dialect.Build
import Verified.Reflect.Command

/-!
The CIC filter's bare-metal program for AArch64: the filter `cic` of
`Library.Numerics.Filters.Cic`, of order 3, decimation 8, and differential delay 1, on a fixed table
of 64 signed 16-bit samples.  The entry is a wrapper, as CRC-32's and SHA-256's are in
`TestSupport.Bare`: `cicCheck n` applies `cicFirst` to the table `input` and the number `n` of
samples to filter, and the Image passes 64, the whole table.
-/

namespace TestSupport.A64.Cic

open Library.Numerics.Filters.Cic

/-- The input of the CIC filter's Image: 64 samples of 16 bits, each stored as its two's-complement
word, which give 8 outputs.  An output reads the 22 samples that end at its time.  Samples 0 to 23
hold −32768 and samples 24 to 47 hold 32767, each for 24 samples, so that the input steps from the
0 before time 0 to the most negative sample and then to the most positive.  Output 2, at time 23,
and output 5, at time 47, read 22 equal samples, so they equal the gain 512 times the extreme:
−2^24, the least output that Hogenauer's bound admits for 16-bit samples, and 16,776,704.  Samples
48 to 63 are segments of 4 samples that alternate between 16384 and −16384, a square wave of period
8, the product of the decimation and the delay, with zero sum over each period.
`tests/cic/table.py lean` prints this listing. -/
def input : Array UInt64 :=
  #[0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000,
    0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000,
    0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000,
    0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000,
    0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000,
    0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000, 0xFFFFFFFFFFFF8000,
    0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF,
    0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF,
    0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF,
    0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF,
    0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF,
    0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF, 0x0000000000007FFF,
    0x0000000000004000, 0x0000000000004000, 0x0000000000004000, 0x0000000000004000,
    0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFC000,
    0x0000000000004000, 0x0000000000004000, 0x0000000000004000, 0x0000000000004000,
    0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFC000, 0xFFFFFFFFFFFFC000]

/-- The filter `cic` of the first `n` samples of `xs`, with 0 past the end of `xs`. -/
def cicFirst (xs : Array UInt64) (n : UInt64) : Array UInt64 :=
  cic (LeanExe.build n fun i => xs[i.toNat]!)

def cicCheck (n : UInt64) : Array UInt64 := cicFirst input n

verified_compile compiled := [integratePass, decimatePass, combPass, cic, cicFirst, cicCheck]

end TestSupport.A64.Cic
