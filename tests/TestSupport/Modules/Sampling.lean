import Library.Random.Sampling.Program
import Library.Random.SplitMix64.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the sampling module. -/

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

/-- `⌈i·2^64 / m⌉`, the least word `u` with `⌊m·u / 2^64⌋ ≥ i`: for the shuffle the least word that
selects position `i` of `m`, for Algorithm S the least word that passes over a record when `i` of
`m` records are still to be chosen, and for Algorithm R the least word that gives the index `i` for
record `m - 1`, which leaves the record out when there are `i` candidates. -/
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

/-- The triples of a word array, an array of records, and a sample size for selection sampling.The
chosen triples sample 0 records with sizes 0 and 3, 1 record with sizes 0, 1, and 2 and with size 1
and the words 0 and `2^64 - 1`, 5 records with size 0, 5 records with all words 0, which choose the
first records, 5 and 10 records with all words `2^64 - 1`, which choose the last ones, and 6 records
with sizes 6, 9, `2^64 - 1`, and `2^32 + 1`, which choose every record.  They also take records with
repeated words, records of 0, 1, and `2^64 - 1`, no words for 6 records, 3 words for 6 records,
whose missing words are 0, and 9 words for 6 records.  The threshold triples put a word at the least
word that passes over its record and at the word below it: the first word for 3 of 7 records, an
inexact threshold, for 500 of 1,000, the exact threshold `2^63`, and for 333 of 1,000, an inexact
one, the second word, after a first word 0 that chooses record 0, for 3 of 7, and the fifth word of
13 records with 5 to choose, after words that choose records 0 and 1 and pass over records 2 and 3,
where 3 of 9 records are still to be chosen.  SplitMix64 words sample `⌊N / 2⌋` of the positions of
every length `N` from 1 to 30, 10, 500, and 999 of 1,000 positions, 100 of 4,000, and 2,500 of
5,000, whose two arrays take more than one 64 KiB page of memory. -/
def sampleInputs : List (List UInt64 × List UInt64 × UInt64) :=
  let chosen : List (List UInt64 × List UInt64 × UInt64) :=
    [([], [], 0), ([], [], 3), ([5], [7], 0), ([5], [7], 1), ([0], [7], 1), ([maxU], [7], 1),
      ([5], [7], 2), (List.replicate 5 0, positions 5, 2), (List.replicate 5 maxU, positions 5, 2),
      (wordsFrom 9 6, positions 6, 6), (wordsFrom 9 6, positions 6, 9),
      (wordsFrom 9 6, positions 6, maxU), (wordsFrom 9 6, positions 6, 4294967297),
      (wordsFrom 10 6, [4, 4, 2, 2, 9, 9], 3), (wordsFrom 15 6, [maxU, 0, maxU, 0, maxU, 1], 3),
      (wordsFrom 16 3, positions 6, 3), (wordsFrom 17 9, positions 6, 3),
      (wordsFrom 31 5, positions 5, 0), ([], positions 6, 3),
      (List.replicate 10 maxU, positions 10, 4)]
  let threshold := fun (M c : Nat) =>
    [(least M c :: List.replicate (M - 1) 0, positions M, UInt64.ofNat c),
      ((least M c - 1) :: List.replicate (M - 1) 0, positions M, UInt64.ofNat c)]
  let second :=
    [(0 :: least 6 2 :: List.replicate 5 0, positions 7, 3),
      (0 :: (least 6 2 - 1) :: List.replicate 5 0, positions 7, 3)]
  let lengths := (List.range 30).map fun i =>
    (wordsFrom (UInt64.ofNat (200 + i)) (i + 1), positions (i + 1), UInt64.ofNat ((i + 1) / 2))
  let long : List (List UInt64 × List UInt64 × UInt64) :=
    [(wordsFrom 11 1000, positions 1000, 10), (wordsFrom 12 1000, positions 1000, 500),
      (wordsFrom 13 1000, positions 1000, 999), (wordsFrom 14 4000, positions 4000, 100),
      (wordsFrom 18 5000, positions 5000, 2500)]
  let fifth :=
    [([0, 0, maxU, maxU, least 9 3] ++ List.replicate 8 0, positions 13, 5),
      ([0, 0, maxU, maxU, least 9 3 - 1] ++ List.replicate 8 0, positions 13, 5)]
  chosen ++ threshold 7 3 ++ threshold 1000 500 ++ threshold 1000 333 ++ second ++ fifth ++
    lengths ++ long

/-- The triples of a word array, an array of records, and a reservoir size for reservoir sampling,
whose step for record `t ≥ k` reads word `t - k`.  The chosen triples take 0 records with sizes 0
and 3, 1 record with sizes 0, 1, and 2, 5 records with size 0, and 5 records with size 2 and all
words 0, which put every later record into candidate 0, all words `2^64 - 1`, which keep the first
records, and all words `2^63`, which replace candidate `⌊(t + 1) / 2⌋` when it is below `k`. 6
records take sizes 6, 9, `2^64 - 1`, and `2^32 + 1`, which keep every record.  They also take
records with repeated words, records of 0, 1, and `2^64 - 1`, no words for 6 records with size 2 and
for 4 records with size 0, two words for no records, a word array shorter than `N - k`, whose
missing words are 0, and a longer one.  The threshold triples put the word of record 4 of 7, with 3
candidates, at the least word that gives each index from 1 to 3, `⌈i·2^64 / 5⌉`, and at the word
below it: index 3 leaves the record out, and the others replace candidate `i` or `i - 1`.  For
record 999 of 1,000 with 500 candidates they do the same at `⌈333·2^64 / 1,000⌉`, an inexact
threshold, and at `2^63`, the exact one that leaves the record out, and for record 7 of 8 with 3
candidates at the exact threshold `⌈3·2^64 / 8⌉`.  SplitMix64 words keep `⌊N / 2⌋` of the positions
of every length `N` from 1 to 30, 10, 500, and 999 of 1,000 positions, 100 of 4,000, and 2,500 of
5,000. -/
def reservoirInputs : List (List UInt64 × List UInt64 × UInt64) :=
  let half : UInt64 := 9223372036854775808
  let chosen : List (List UInt64 × List UInt64 × UInt64) :=
    [([], [], 0), ([], [], 3), ([5], [7], 0), ([5], [7], 1), ([5], [7], 2),
      (wordsFrom 30 5, positions 5, 0),
      (List.replicate 3 0, positions 5, 2), (List.replicate 3 maxU, positions 5, 2),
      (List.replicate 3 half, positions 5, 2), (wordsFrom 9 6, positions 6, 6),
      (wordsFrom 9 6, positions 6, 9), (wordsFrom 9 6, positions 6, maxU),
      (wordsFrom 9 6, positions 6, 4294967297), (wordsFrom 10 4, [4, 4, 2, 2, 9, 9], 2),
      (wordsFrom 15 3, [maxU, 0, maxU, 0, maxU, 1], 3), ([], positions 6, 2),
      (wordsFrom 16 2, positions 8, 3), (wordsFrom 17 9, positions 8, 3), ([], positions 4, 0),
      ([5, 6], [], 2)]
  let at4 := fun (u : UInt64) => (maxU :: u :: [maxU, maxU], positions 7, (3 : UInt64))
  let at999 := fun (u : UInt64) => (List.replicate 499 maxU ++ [u], positions 1000, (500 : UInt64))
  let threshold := [1, 2, 3].flatMap (fun i => [at4 (least 5 i), at4 (least 5 i - 1)]) ++
    [at999 (least 1000 333), at999 (least 1000 333 - 1), at999 (least 1000 500),
      at999 (least 1000 500 - 1),
      (List.replicate 4 maxU ++ [least 8 3], positions 8, 3),
      (List.replicate 4 maxU ++ [least 8 3 - 1], positions 8, 3)]
  let lengths := (List.range 30).map fun i =>
    (wordsFrom (UInt64.ofNat (300 + i)) (i + 1), positions (i + 1), UInt64.ofNat ((i + 1) / 2))
  let long : List (List UInt64 × List UInt64 × UInt64) :=
    [(wordsFrom 21 990, positions 1000, 10), (wordsFrom 22 500, positions 1000, 500),
      (wordsFrom 23 1, positions 1000, 999), (wordsFrom 24 3900, positions 4000, 100),
      (wordsFrom 25 2500, positions 5000, 2500)]
  chosen ++ threshold ++ lengths ++ long

end Library.Random.Sampling
