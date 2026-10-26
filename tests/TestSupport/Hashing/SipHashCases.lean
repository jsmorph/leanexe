import Library.Hashing.SipHash.Program

/-! The cases of the module `siphash`: SipHash-2-4 and SipHash-1-3 of messages of 0 to 17 bytes and
of lengths around multiples of eight and of 256, where the byte `n mod 256` wraps, under several
keys; byte counts beyond the array, whose missing words read as zero; and SipRound of two states.
The bytes after a message in its last word are nonzero.  A case requires one retained block, the
host's message, and at most one allocation, the host's. -/

namespace TestSupport.Hashing.SipHashCases

open Library.Hashing.SipHash

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

def keys : List (UInt64 × UInt64) :=
  [(0x0706050403020100, 0x0f0e0d0c0b0a0908), (0, 0), (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF),
    (0x0123456789ABCDEF, 0xFEDCBA9876543210)]

def emit (k0 k1 : UInt64) (msg : Array UInt64) (n : UInt64) : IO Unit := do
  let a := s!"i64:{k0} i64:{k1} {arg msg} i64:{n}"
  IO.println s!"siphash|siphash24|i64|{a}|{siphash24 k0 k1 msg n}|1|1"
  IO.println s!"siphash|siphash13|i64|{a}|{siphash13 k0 k1 msg n}|1|1"

def lengths : List Nat :=
  List.range 18 ++ [23, 24, 25, 63, 64, 65, 255, 256, 257, 511, 512, 513, 1000, 4096]

def cases : IO Unit := do
  for (k0, k1) in keys do
    for n in lengths do
      emit k0 k1 (message 1 n) n.toUInt64
  for (size, n) in [(0, 5), (1, 9), (2, 30), (3, 100)] do
    emit 1 2 (message 2 (8 * size)) n.toUInt64
  for s in [(⟨0, 0, 0, 0⟩ : Spec.State), ⟨1, 2, 3, 0xFFFFFFFFFFFFFFFF⟩] do
    let r := sipRound s
    IO.println s!"siphash|sipRound|list:i64,i64,i64,i64|i64:{s.v0} i64:{s.v1} i64:{s.v2} \
      i64:{s.v3}|{r.v0} {r.v1} {r.v2} {r.v3}|0|0"

end TestSupport.Hashing.SipHashCases
