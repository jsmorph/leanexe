import Library.Hashing.Crc.Program
import Library.Hashing.Sha256.Program
import Library.Hashing.Words.Encoding
import Verified.Reflect.Command

/-!
Programs of the bare-metal test (`docs/native-bare-metal.md`, test 2) that the libraries do not
compile as they stand: CRC-32 and SHA-256 of a short message whose bytes come in as words, so
that `main` calls the entry on constants.  The function builds the message in the heap.  Each
entry is a wrapper, which applies a function to the constant table of its hash before its own
parameters: `crcCheck` takes the words of `123456789`, and `shaCheck` the word of `abc`.
-/

namespace TestSupport.Bare

open Library.Hashing.Crc in
/-- CRC-32 by the table `t` of the `9` bytes in the words `a` and `b`. -/
def crcMsg (t : Array UInt64) (a b : UInt64) : UInt64 :=
  crcWith t (((#[] : Array UInt64).push a).push b) 9

open Library.Hashing.Crc in
def crcCheck (a b : UInt64) : UInt64 := crcMsg crc32Table a b

verified_compile crcCompiled := [Library.Hashing.Crc.updateWith, Library.Hashing.Crc.crcWith,
  crcMsg, crcCheck]

open Library.Hashing.Sha256 Library.Hashing.Words in
/-- SHA-256 by the round constants `k` of the `3` bytes in the word `a`, as the array of the
digest's four words. -/
def shaMsg (k : Array UInt64) (a : UInt64) : Array UInt64 :=
  let d := sha256With k ((#[] : Array UInt64).push a) 3
  ((((#[] : Array UInt64).push d.w0).push d.w1).push d.w2).push d.w3

open Library.Hashing.Sha256 in
def shaCheck (a : UInt64) : Array UInt64 := shaMsg roundConstants a

open Library.Hashing.Sha256 Library.Hashing.Words in
verified_compile shaCompiled := [bswap, paddedWord, loadBlock, roundStep, advance, compress,
  hashFrom, sha256With, shaMsg, shaCheck]

end TestSupport.Bare
