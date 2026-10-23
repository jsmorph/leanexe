import Library.Hashing.Sha256.Program

/-! The cases of the module `sha256`: the two digests of messages whose lengths reach every position
of a 64-byte block around the boundaries at 56 and 64 bytes, and of longer messages.
The bytes after a message in its last word are nonzero.  Some byte counts exceed the array, whose
missing words read as zero.  Each case requires one retained block, the host's message, and at
most one allocation, the host's. -/

namespace TestSupport.Hashing.Sha256Cases

open Library.Hashing.Sha256 Library.Hashing.Words

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

def words (ws : List UInt64) : String := " ".intercalate (ws.map toString)

def kinds (k : Nat) : String := "list:" ++ ",".intercalate (List.replicate k "i64")

def lengths : List Nat :=
  List.range 18 ++ (List.range 21).map (· + 50) ++ (List.range 21).map (· + 110) ++
    [183, 184, 247, 248, 1000, 4096]

def emit (msg : Array UInt64) (n : UInt64) : IO Unit := do
  let a := s!"{arg msg} i64:{n}"
  let d := sha256 msg n
  IO.println s!"sha256|sha256|{kinds 4}|{a}|{words [d.w0, d.w1, d.w2, d.w3]}|1|1"
  let d := sha224 msg n
  IO.println s!"sha256|sha224|{kinds 4}|{a}|{words [d.w0, d.w1, d.w2, d.w3]}|1|1"

def cases : IO Unit := do
  for n in lengths do
    emit (message 1 n) n.toUInt64
  for (size, n) in [(0, 5), (1, 9), (2, 30), (3, 100)] do
    emit (message 2 (8 * size)) n.toUInt64
  for x in [(0 : UInt64), 1, 0x0123456789abcdef, 0xffffffffffffffff, 0x8000000000000001] do
    IO.println s!"sha256|bswap|i64|i64:{x}|{bswap x}|0|0"

end TestSupport.Hashing.Sha256Cases
