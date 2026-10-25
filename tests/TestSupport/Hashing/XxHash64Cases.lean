import Library.Hashing.XxHash64.Program

/-! The cases of the module `xxhash64`: XXH64 of messages of 0 to 40 bytes, which reach each case of
step 5 and the first stripes, and of lengths around multiples of 32 and of 4,096, under several
seeds; and byte counts beyond the array, whose missing words read as zero.  The bytes after a
message in its last word are nonzero.  A case requires one retained block, the host's message,
and at most one allocation, the host's. -/

namespace TestSupport.Hashing.XxHash64Cases

open Library.Hashing.XxHash64

/-- Byte `i` of a test message. -/
def byte (seed i : Nat) : UInt64 := ((i * 131 + seed * 17 + i / 7) % 256).toUInt64

/-- `n` message bytes packed eight to a word, with `0xA5` after the message. -/
def message (seed n : Nat) : Array UInt64 :=
  (List.range ((n + 7) / 8)).toArray.map fun w =>
    (List.range 8).foldl (fun acc j =>
      let i := 8 * w + j
      acc ||| ((if i < n then byte seed i else 0xA5) <<< (8 * j).toUInt64)) 0

def arg (xs : Array UInt64) : String :=
  "array-u64:" ++ ",".intercalate (xs.toList.map toString)

def emit (msg : Array UInt64) (n seed : UInt64) : IO Unit :=
  IO.println s!"xxhash64|xxh64|i64|{arg msg} i64:{n} i64:{seed}|{xxh64 msg n seed}|1|1"

def lengths : List Nat :=
  List.range 41 ++ [63, 64, 65, 95, 96, 97, 255, 256, 257, 1000, 4095, 4096, 4097]

def cases : IO Unit := do
  for seed in [0, 0x9E3779B1, 0xFFFFFFFFFFFFFFFF] do
    for n in lengths do
      emit (message 1 n) n.toUInt64 seed
  for (size, n) in [(0, 5), (1, 9), (2, 30), (3, 100)] do
    emit (message 2 (8 * size)) n.toUInt64 7

end TestSupport.Hashing.XxHash64Cases
