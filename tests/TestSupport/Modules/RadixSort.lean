import Library.Sorting.RadixSort.Spec
import Library.Random.SplitMix64.Program
import TestSupport.Modules.Quicksort

/-! The inputs of the verified compiler's cases of radix sort. -/

namespace Library.Sorting.RadixSort

open TestSupport.Host

/-- The arrays of the verified compiler's cases: the inputs of quicksort, `quicksortInputs`, which
include those of straight insertion and heapsort, and arrays that test single passes.  For each
byte, 300 words that differ only in that byte, whose other bytes are those of `0x0123456789abcdef`,
make that pass the only one that changes their order.  Eight arrays of 300 words, whose bytes are
each 0 or 255 by the bits of a SplitMix64 output, fill only the first and the last count in every
pass.  For each byte, 300 words whose higher bytes are those of `0x0123456789abcdef` and whose other
bytes are arbitrary make every pass up to that byte determine the order.  The other arrays hold
2,000 words whose bytes lie in 0 to 3, so that every pass has equal bytes, 2,000 words whose bytes
other than the lowest and the highest are 0, and 17,000 words whose lowest byte is 7, so that the
first pass holds a count above `2^14`. -/
def radixInputs : List (List UInt64) :=
  let draw := fun (k : Nat) => (Library.Random.SplitMix64.splitMix (UInt64.ofNat k)).2
  let base : UInt64 := 0x0123456789abcdef
  let oneByte := (List.range 8).map fun b =>
    let shift := UInt64.ofNat (8 * b)
    (List.range 300).map fun k =>
      (base &&& ~~~((255 : UInt64) <<< shift)) ||| ((draw (k + 1000 * b) &&& 255) <<< shift)
  let zeroOrFull := (List.range 8).map fun b =>
    (List.range 300).map fun k =>
      let w := draw (k + 10000 + 1000 * b)
      (List.range 8).foldl (fun acc i =>
        if (w >>> UInt64.ofNat i) &&& 1 = 1 then acc ||| ((255 : UInt64) <<< UInt64.ofNat (8 * i))
        else acc) 0
  let fewPerByte := (List.range 2000).map fun k => draw (k + 50000) &&& 0x0303030303030303
  let ends := (List.range 2000).map fun k => draw (k + 60000) &&& 0xff000000000000ff
  let oneCount := (List.range 17000).map fun k => (draw (k + 70000) &&& 0xff00) ||| 7
  let lowBytes := (List.range 8).map fun b =>
    let mask : UInt64 :=
      if b < 7 then ((1 : UInt64) <<< UInt64.ofNat (8 * b + 8)) - 1 else 0xffffffffffffffff
    (List.range 300).map fun k => (base &&& ~~~mask) ||| (draw (k + 20000 + 1000 * b) &&& mask)
  Library.Sorting.Quicksort.quicksortInputs ++ oneByte ++ zeroOrFull ++ lowBytes ++
    [fewPerByte, ends, oneCount]

end Library.Sorting.RadixSort
