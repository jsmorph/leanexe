/-! XXH64, transcribed from the "XXH64 Algorithm Description" of Y. Collet, "xxHash fast digest
algorithm", version 0.2.0 (29/06/23), in the xxHash repository's `doc/xxhash_spec.md`.  The words
are 64-bit unsigned integers, with `+`, `-`, and `*` modulo `2^64`, `xor` as `^^^`, `>>` as a
shift to the right that fills with zeros, and `<<<` as rotation to the left, which `rotl` takes from `BitVec.rotateLeft`.  Input is
read in little-endian order.  `xxh64 m seed` follows the seven steps: the four accumulators of
step 1, the stripes of 32 bytes of step 2, the convergence of step 3 and its `mergeAccumulator`,
the length of step 4, the remaining input of step 5 in lanes of 8 bytes, at most one lane of 4,
and single bytes, and the avalanche of step 6.  For an input of fewer than 32 bytes the single
accumulator `seed + PRIME64_5` replaces steps 1 to 3.  Step 7 states that the output is the
64-bit value, which it writes most significant byte first for display. -/

namespace Library.Hashing.XxHash64.Spec

def PRIME64_1 : UInt64 := 0x9E3779B185EBCA87
def PRIME64_2 : UInt64 := 0xC2B2AE3D27D4EB4F
def PRIME64_3 : UInt64 := 0x165667B19E3779F9
def PRIME64_4 : UInt64 := 0x85EBCA77C2B2AE63
def PRIME64_5 : UInt64 := 0x27D4EB2F165667C5

/-- `x` rotated to the left by `r` bits, the `<<<` of the operation notations. -/
def rotl (x : UInt64) (r : Nat) : UInt64 := UInt64.ofBitVec (x.toBitVec.rotateLeft r)

/-- The little-endian value of the bytes `bs`, the first byte least significant. -/
def le (bs : List UInt8) : UInt64 := UInt64.ofNat (bs.foldr (fun b acc => b.toNat + 256 * acc) 0)

/-- The four accumulators. -/
structure Accs where
  acc1 : UInt64
  acc2 : UInt64
  acc3 : UInt64
  acc4 : UInt64
  deriving Inhabited, DecidableEq, Repr

/-- Step 1. -/
def initAccs (seed : UInt64) : Accs :=
  ⟨seed + PRIME64_1 + PRIME64_2, seed + PRIME64_2, seed + 0, seed - PRIME64_1⟩

/-- The round of step 2. -/
def round (accN laneN : UInt64) : UInt64 :=
  let accN := accN + laneN * PRIME64_2
  let accN := rotl accN 31
  accN * PRIME64_1

/-- Lane `t` of a stripe `s`, counting from 0: its bytes `8 t` to `8 t + 7`, read little-endian. -/
def lane (s : List UInt8) (t : Nat) : UInt64 := le ((s.drop (8 * t)).take 8)

/-- Step 2 for one stripe: lane `t` of the 32 bytes `s` updates accumulator `t + 1`. -/
def stripe (a : Accs) (s : List UInt8) : Accs :=
  ⟨round a.acc1 (lane s 0), round a.acc2 (lane s 1), round a.acc3 (lane s 2),
    round a.acc4 (lane s 3)⟩

/-- Step 2 over the input: each full stripe in turn, with the bytes that remain. -/
def stripes (a : Accs) (m : List UInt8) : Accs × List UInt8 :=
  if 32 ≤ m.length then stripes (stripe a (m.take 32)) (m.drop 32) else (a, m)
termination_by m.length
decreasing_by simp; omega

/-- `mergeAccumulator` of step 3. -/
def mergeAccumulator (acc accN : UInt64) : UInt64 :=
  let acc := acc ^^^ round 0 accN
  let acc := acc * PRIME64_1
  acc + PRIME64_4

/-- Step 3. -/
def converge (a : Accs) : UInt64 :=
  let acc := rotl a.acc1 1 + rotl a.acc2 7 + rotl a.acc3 12 + rotl a.acc4 18
  let acc := mergeAccumulator acc a.acc1
  let acc := mergeAccumulator acc a.acc2
  let acc := mergeAccumulator acc a.acc3
  mergeAccumulator acc a.acc4

/-- The first loop of step 5, over lanes of 8 bytes, with the bytes that remain. -/
def lanes8 (acc : UInt64) (m : List UInt8) : UInt64 × List UInt8 :=
  if 8 ≤ m.length then
    let lane := le (m.take 8)
    let acc := acc ^^^ round 0 lane
    let acc := rotl acc 27 * PRIME64_1
    lanes8 (acc + PRIME64_4) (m.drop 8)
  else (acc, m)
termination_by m.length
decreasing_by simp; omega

/-- The lane of 4 bytes of step 5, when at least 4 bytes remain. -/
def lane4 (acc : UInt64) (m : List UInt8) : UInt64 × List UInt8 :=
  if 4 ≤ m.length then
    let lane := le (m.take 4)
    let acc := acc ^^^ lane * PRIME64_1
    let acc := rotl acc 23 * PRIME64_2
    (acc + PRIME64_3, m.drop 4)
  else (acc, m)

/-- The last loop of step 5, over single bytes. -/
def bytes (acc : UInt64) (m : List UInt8) : UInt64 :=
  m.foldl (fun acc b => rotl (acc ^^^ b.toUInt64 * PRIME64_5) 11 * PRIME64_1) acc

/-- Step 5. -/
def consume (acc : UInt64) (m : List UInt8) : UInt64 :=
  let (acc, m) := lanes8 acc m
  let (acc, m) := lane4 acc m
  bytes acc m

/-- Step 6. -/
def avalanche (acc : UInt64) : UInt64 :=
  let acc := acc ^^^ (acc >>> 33)
  let acc := acc * PRIME64_2
  let acc := acc ^^^ (acc >>> 29)
  let acc := acc * PRIME64_3
  acc ^^^ (acc >>> 32)

/-- XXH64 of the bytes `m` with the seed `seed`. -/
def xxh64 (m : List UInt8) (seed : UInt64) : UInt64 :=
  let (acc, rest) :=
    if 32 ≤ m.length then
      let (a, rest) := stripes (initAccs seed) m
      (converge a, rest)
    else (seed + PRIME64_5, m)
  let acc := acc + UInt64.ofNat m.length
  avalanche (consume acc rest)

end Library.Hashing.XxHash64.Spec
