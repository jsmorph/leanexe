import Library.Hashing.Crc.Program

/-! The cases of the module `crc`: CRC-32 and CRC-32C of messages of 0 to 17 bytes and of lengths
around multiples of eight and of 4,096, of the check string `123456789`, and of byte counts beyond
the array, whose missing words read as zero; and the updates from the CRC of each split of a
message, with and without nonzero high bits in the CRC argument.  The bytes after a message in its
last word are nonzero.  A case requires one retained block, the host's message, and at most one
allocation, the host's. -/

namespace TestSupport.Hashing.CrcCases

open Library.Hashing.Crc

/-- Byte `i` of a test message. -/
def byte (seed i : Nat) : UInt64 := ((i * 131 + seed * 17 + i / 7) % 256).toUInt64

/-- `n` message bytes packed eight to a word, with `0xA5` after the message. -/
def message (seed n : Nat) : Array UInt64 :=
  (List.range ((n + 7) / 8)).toArray.map fun w =>
    (List.range 8).foldl (fun acc j =>
      let i := 8 * w + j
      acc ||| ((if i < n then byte seed i else 0xA5) <<< (8 * j).toUInt64)) 0

/-- The bytes `bs` packed eight to a word, with `0xA5` after them. -/
def packed (bs : List UInt8) : Array UInt64 :=
  (List.range ((bs.length + 7) / 8)).toArray.map fun w =>
    (List.range 8).foldl (fun acc j =>
      acc ||| ((bs.getD (8 * w + j) 0xA5).toUInt64 <<< (8 * j).toUInt64)) 0

def arg (xs : Array UInt64) : String :=
  "array-u64:" ++ ",".intercalate (xs.toList.map toString)

def emit (msg : Array UInt64) (n : UInt64) : IO Unit := do
  IO.println s!"crc|crc32|i64|{arg msg} i64:{n}|{crc32 msg n}|1|1"
  IO.println s!"crc|crc32c|i64|{arg msg} i64:{n}|{crc32c msg n}|1|1"

def emitUpdate (c : UInt64) (msg : Array UInt64) (n : UInt64) : IO Unit := do
  IO.println s!"crc|crc32Update|i64|i64:{c} {arg msg} i64:{n}|{crc32Update c msg n}|1|1"
  IO.println s!"crc|crc32cUpdate|i64|i64:{c} {arg msg} i64:{n}|{crc32cUpdate c msg n}|1|1"

def lengths : List Nat := List.range 18 ++ [31, 32, 33, 63, 64, 65, 255, 256, 1000, 4095, 4096, 4097]

def cases : IO Unit := do
  for n in lengths do
    emit (message 1 n) n.toUInt64
  emit (packed "123456789".toUTF8.toList) 9
  for (size, n) in [(0, 5), (1, 9), (2, 30), (3, 100)] do
    emit (message 2 (8 * size)) n.toUInt64
  for n in [0, 1, 9, 100, 1000] do
    for k in [0, 1, n / 2, n] do
      let m := (List.range n).map fun i => (byte 3 i).toUInt8
      let rest := packed (m.drop k)
      for c in [crc32 (packed (m.take k)) k.toUInt64, crc32c (packed (m.take k)) k.toUInt64,
          0xFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0x123456789ABCDEF0] do
        emitUpdate c rest (n - k).toUInt64

end TestSupport.Hashing.CrcCases
