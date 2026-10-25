import LeanExe.Dialect.Loop
import Library.Hashing.XxHash64.Spec

/-! XXH64 of `Library.Hashing.XxHash64.Spec` for a message of `n` bytes packed eight to a word as
`Library.Hashing.Words` describes, and a seed.  The packing makes the lanes of the stripes and the
lanes of 8 bytes of step 5 the words of the array, the lane of 4 bytes the low half of the next
word, and each remaining byte a byte of that word, so the program reads every one in place.  The
accumulators are the specification's structure of four words, and no function allocates. -/

namespace Library.Hashing.XxHash64

open Library.Hashing.XxHash64.Spec (Accs PRIME64_1 PRIME64_2 PRIME64_3 PRIME64_4 PRIME64_5)

/-- `x` rotated left by `k` bits, for `k` from 1 to 63. -/
@[inline] def rotl (x k : UInt64) : UInt64 := (x <<< k) ||| (x >>> (64 - k))

/-- The round of step 2. -/
@[inline] def round (acc lane : UInt64) : UInt64 := rotl (acc + lane * PRIME64_2) 31 * PRIME64_1

/-- Step 2 for stripe `j`, whose lanes are words `4 j` to `4 j + 3`. -/
def stripeAt (msg : Array UInt64) (a : Accs) (j : UInt64) : Accs :=
  let w := j <<< 2
  ⟨round a.acc1 msg[w.toNat]!, round a.acc2 msg[(w + 1).toNat]!,
    round a.acc3 msg[(w + 2).toNat]!, round a.acc4 msg[(w + 3).toNat]!⟩

/-- `mergeAccumulator` of step 3. -/
@[inline] def mergeAccumulator (acc accN : UInt64) : UInt64 :=
  (acc ^^^ round 0 accN) * PRIME64_1 + PRIME64_4

/-- Step 3. -/
def converge (a : Accs) : UInt64 :=
  let acc := rotl a.acc1 1 + rotl a.acc2 7 + rotl a.acc3 12 + rotl a.acc4 18
  mergeAccumulator (mergeAccumulator (mergeAccumulator (mergeAccumulator acc a.acc1) a.acc2)
    a.acc3) a.acc4

/-- Step 6. -/
def avalanche (acc : UInt64) : UInt64 :=
  let acc := (acc ^^^ (acc >>> 33)) * PRIME64_2
  let acc := (acc ^^^ (acc >>> 29)) * PRIME64_3
  acc ^^^ (acc >>> 32)

/-- Steps 1 to 3 for an input of at least 32 bytes, and the single accumulator otherwise. -/
@[inline] def start (msg : Array UInt64) (n seed : UInt64) : UInt64 :=
  if n < 32 then seed + PRIME64_5 else
    converge (LeanExe.loop (n >>> 5) ⟨seed + PRIME64_1 + PRIME64_2, seed + PRIME64_2, seed,
      seed - PRIME64_1⟩ fun j a => stripeAt msg a j)

/-- The lanes of 8 bytes of step 5: the words from `4 ⌊n / 32⌋` to `⌊n / 8⌋ - 1`. -/
@[inline] def lanes8 (msg : Array UInt64) (n acc : UInt64) : UInt64 :=
  let w0 := (n >>> 5) <<< 2
  LeanExe.loop ((n >>> 3) - w0) acc fun i acc =>
    rotl (acc ^^^ round 0 msg[(w0 + i).toNat]!) 27 * PRIME64_1 + PRIME64_4

/-- The lane of 4 bytes of step 5, the low half of word `⌊n / 8⌋`, when `n mod 8 ≥ 4`. -/
@[inline] def lane4 (msg : Array UInt64) (n acc : UInt64) : UInt64 :=
  if (n &&& 7) < 4 then acc else
    rotl (acc ^^^ (msg[(n >>> 3).toNat]! &&& 0xFFFFFFFF) * PRIME64_1) 23 * PRIME64_2 + PRIME64_3

/-- The single bytes of step 5, from position `n - n mod 4`. -/
@[inline] def bytes (msg : Array UInt64) (n acc : UInt64) : UInt64 :=
  let p := n - (n &&& 3)
  LeanExe.loop (n &&& 3) acc fun i acc =>
    let q := p + i
    let b := (msg[(q >>> 3).toNat]! >>> ((q &&& 7) <<< 3)) &&& 0xFF
    rotl (acc ^^^ b * PRIME64_5) 11 * PRIME64_1

/-- XXH64 of the `n` bytes of `msg` with the seed `seed`. -/
def xxh64 (msg : Array UInt64) (n seed : UInt64) : UInt64 :=
  avalanche (bytes msg n (lane4 msg n (lanes8 msg n (start msg n seed + n))))

end Library.Hashing.XxHash64
