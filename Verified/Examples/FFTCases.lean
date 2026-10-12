import Verified.Examples.FFT

namespace Verified.Examples.FFTCases

def cases : List (Array Float) :=
  [#[], #[Float.ofBits 0x7FF8000000000042], #[0.0, -0.0], #[1.0, -2.0],
    #[Float.ofBits 1, Float.ofBits 0x8000000000000001,
      Float.ofBits 2, Float.ofBits 0x8000000000000002],
    #[Float.ofBits 0x7FF0000000000000, 0.0, 1.0, -1.0],
    #[Float.ofBits 0xFFF0000000000000, Float.ofBits 0x7FF0000000000000, -1.0, 1.0],
    #[Float.ofBits 0x7FF8000000000042, 1.0, 0.0, -0.0],
    #[Float.ofBits 0x7FEFFFFFFFFFFFFF, Float.ofBits 0xFFEFFFFFFFFFFFFF,
      Float.ofBits 0xFFEFFFFFFFFFFFFF, Float.ofBits 0x7FEFFFFFFFFFFFFF],
    #[1.0, -2.0, 3.0, 4.0, Float.ofBits 0x7FF8000000000042]] ++
    [1, 2, 3, 4, 5, 7, 8, 16, 31, 32, 64, 128, 1024, 2048].map (Fourier.signal · 17)

def words (xs : Array Float) : String :=
  String.intercalate "," (xs.toList.map fun x => toString x.toBits)

def output (xs : Array Float) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map fun x => toString x.toBits) ++ "]"

end Verified.Examples.FFTCases

open Verified.Examples Verified.Examples.FFTCases in
def main : IO Unit := do
  for xs in cases do
    for (name, f) in [("fft", FFT.fft), ("inverse", FFT.inverse),
        ("powerSpectrum", FFT.powerSpectrum)] do
      IO.println s!"{name}|array-u64:{words xs}|{output (f xs)}"
