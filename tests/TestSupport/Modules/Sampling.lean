import Library.Random.Sampling.Program
import Library.Random.SplitMix64.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the shuffle. -/

namespace Library.Random.Sampling

open TestSupport.Host

/-- `n` words of SplitMix64 from the state `s`. -/
def wordsFrom : UInt64 → Nat → List UInt64
  | _, 0 => []
  | s, n + 1 =>
    let r := Library.Random.SplitMix64.splitMix s
    r.2 :: wordsFrom r.1 n

/-- The positions `0, …, n - 1` as words. -/
def positions (n : Nat) : List UInt64 := (List.range n).map UInt64.ofNat

/-- The least word that selects `i` from `m` positions, `⌈i·2^64 / m⌉`. -/
def least (m i : Nat) : UInt64 := UInt64.ofNat ((i * 2 ^ 64 + m - 1) / m)

/-- The pairs of a word array and an array to shuffle, with `n` the number of words to shuffle.
The chosen pairs shuffle 0, 1, and 2 words with no word, 1 word with one word, `[1, 2]` with the
word 0, which selects position 0, and with the word `2^64 - 1`, which selects position `j`,
`[2^64 - 1, 0]` with no word, eight positions with seven words, all 0, all `2^64 - 1`, or all
`2^63`, which selects `⌊(j + 1) / 2⌋`, and arrays with repeated words.  `boundaries` shuffles `m`
positions with the first word, which the step `j = m - 1` reads, at the least word `⌈i·2^64 / m⌉`
that selects `i` and at the word below it, for `m` of 3, 5, and 7 with each `i` from 1 to `m - 1`,
and for `m` of 1,000 and 1,024 with `i` of 1, `m / 2`, and `m - 1`, so that the carry from the low
half in `scale` decides the index.  Word arrays from SplitMix64 shuffle the positions of every
length `n` from 2 to 40 with `n - 1` words, 100 positions with 50, 99, and 150 words, and 2,000
and 4,500 positions with `n - 1` words, where the two arrays of 4,500 words take more than one
64 KiB page of memory. -/
def shuffleInputs : List (List UInt64 × List UInt64) :=
  let half : UInt64 := 9223372036854775808
  let chosen : List (List UInt64 × List UInt64) :=
    [([], []), ([], [7]), ([], [1, 2]), ([5], [7]), ([0], [1, 2]), ([maxU], [1, 2]),
      ([], [maxU, 0]), (List.replicate 7 0, positions 8), (List.replicate 7 maxU, positions 8),
      (List.replicate 7 half, positions 8), (wordsFrom 5 9, [3, 3, 1, 1, 2, 2, 3, 3, 0, 0]),
      (wordsFrom 6 4, [maxU, 0, maxU, 0, maxU])]
  let boundary := fun (m i : Nat) =>
    [(least m i :: List.replicate (m - 2) 0, positions m),
      ((least m i - 1) :: List.replicate (m - 2) 0, positions m)]
  let boundaries :=
    ([3, 5, 7].flatMap fun m => (List.range (m - 1)).flatMap fun i => boundary m (i + 1)) ++
      [1000, 1024].flatMap fun m => [1, m / 2, m - 1].flatMap fun i => boundary m i
  let lengths := (List.range 39).map fun i => (wordsFrom (UInt64.ofNat (100 + i)) (i + 1),
    positions (i + 2))
  let long : List (List UInt64 × List UInt64) :=
    [(wordsFrom 1 50, positions 100), (wordsFrom 2 99, positions 100),
      (wordsFrom 3 150, positions 100), (wordsFrom 4 1999, positions 2000),
      (wordsFrom 7 4499, positions 4500)]
  chosen ++ boundaries ++ lengths ++ long

end Library.Random.Sampling
