import Library.Hashing.Hmac.Program
import TestSupport.Hashing.Sha256Cases

/-! The cases of the modules `hmac_sha256` and `hmac_sha512`: keys whose lengths reach each side of
the block sizes of 64 and 128 bytes, against messages whose lengths cross the padding boundaries
of both hash functions.  The bytes after a key or a message in its last word are nonzero, and
some byte counts exceed their arrays, whose missing words read as zero.  Each case requires two
retained blocks, the host's key and message, and at most two allocations, the host's. -/

namespace TestSupport.Hashing.HmacCases

open Library.Hashing.Hmac Library.Hashing.Words TestSupport.Hashing.Sha256Cases

def keyLengths : List Nat := [0, 1, 8, 31, 32, 63, 64, 65, 127, 128, 129, 200]

def messageLengths : List Nat := [0, 1, 55, 56, 63, 64, 111, 112, 127, 128, 300]

def emit (key : Array UInt64) (kn : UInt64) (msg : Array UInt64) (n : UInt64) : IO Unit := do
  let a := s!"{arg key} i64:{kn} {arg msg} i64:{n}"
  let d := hmacSha256 key kn msg n
  IO.println s!"hmac_sha256|hmacSha256|{kinds 4}|{a}|{words [d.w0, d.w1, d.w2, d.w3]}|2|2"
  let d := hmacSha512 key kn msg n
  IO.println
    s!"hmac_sha512|hmacSha512|{kinds 8}|{a}|{words [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7]}|2|2"

def cases : IO Unit := do
  for kn in keyLengths do
    for n in messageLengths do
      emit (message 3 kn) kn.toUInt64 (message 1 n) n.toUInt64
  for (size, kn) in [(0, 5), (2, 30), (8, 100), (9, 150)] do
    emit (message 3 (8 * size)) kn.toUInt64 (message 1 20) 20

end TestSupport.Hashing.HmacCases
