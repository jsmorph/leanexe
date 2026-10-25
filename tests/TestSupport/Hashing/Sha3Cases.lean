import Library.Hashing.Sha3.Program

/-! The cases of the module `sha3`: the four digests of messages whose lengths reach the ends of
the blocks of every rate, 72, 104, 136, 144, and 168 bytes, where the suffix and the last bit of
the padding share a byte or fall in separate blocks, and of longer messages; SHAKE128 and SHAKE256
outputs of lengths around their rates; byte counts beyond the array, whose missing words read as
zero; and KECCAK-p[1600, 24] of two states.  The bytes after a message in its last word are
nonzero.  A hash case requires one retained block, the host's message, and at most one
allocation, the host's; a SHAKE case retains the message and its output and allocates nothing
else. -/

namespace TestSupport.Hashing.Sha3Cases

open Library.Hashing.Sha3 Library.Hashing.Words

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

def arrayOut (xs : Array UInt64) : String :=
  "[" ++ ", ".intercalate (xs.toList.map toString) ++ "]"

def lanes (s : Lanes) : List UInt64 :=
  [s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13, s.a14,
    s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

def rates : List Nat := [72, 104, 136, 144, 168]

def lengths : List Nat :=
  List.range 18 ++ rates.flatMap (fun r => [r - 2, r - 1, r, r + 1]) ++ [272, 335, 1000, 4096]

def emitHashes (msg : Array UInt64) (n : UInt64) : IO Unit := do
  let a := s!"{arg msg} i64:{n}"
  let d := sha3_224 msg n
  IO.println s!"sha3|sha3_224|{kinds 4}|{a}|{words [d.w0, d.w1, d.w2, d.w3]}|1|1"
  let d := sha3_256 msg n
  IO.println s!"sha3|sha3_256|{kinds 4}|{a}|{words [d.w0, d.w1, d.w2, d.w3]}|1|1"
  let d := sha3_384 msg n
  IO.println s!"sha3|sha3_384|{kinds 6}|{a}|{words [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5]}|1|1"
  let d := sha3_512 msg n
  IO.println
    s!"sha3|sha3_512|{kinds 8}|{a}|{words [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7]}|1|1"

def emitShakes (msg : Array UInt64) (n d : UInt64) : IO Unit := do
  let a := s!"{arg msg} i64:{n} i64:{d}"
  IO.println s!"sha3|shake128|array-u64|{a}|{arrayOut (shake128 msg n d)}|2|2"
  IO.println s!"sha3|shake256|array-u64|{a}|{arrayOut (shake256 msg n d)}|2|2"

def cases : IO Unit := do
  for n in lengths do
    emitHashes (message 1 n) n.toUInt64
  for (size, n) in [(0, 5), (1, 9), (2, 30), (3, 100)] do
    emitHashes (message 2 (8 * size)) n.toUInt64
  for n in [0, 1, 135, 136, 167, 168, 1000] do
    for d in [0, 1, 7, 8, 16, 32, 64, 135, 136, 137, 167, 168, 169, 500] do
      emitShakes (message 3 n) n.toUInt64 d.toUInt64
  emitShakes (message 4 0) 20 40
  for s in [zeroLanes, ⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
      22, 23, 24, 0xFFFFFFFFFFFFFFFF⟩] do
    IO.println s!"sha3|keccakF|{kinds 25}|{" ".intercalate ((lanes s).map (s!"i64:{·}"))}|\
      {words (lanes (keccakF s))}|0|0"

end TestSupport.Hashing.Sha3Cases
