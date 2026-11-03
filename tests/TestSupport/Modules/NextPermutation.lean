import Library.Combinatorics.NextPermutation.Spec
import Library.Random.SplitMix64.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the next arrangement, and their results by a
recursion on lists that does not follow Algorithm L. -/

namespace Library.Combinatorics.NextPermutation

open TestSupport.Host

/-- The next arrangement of a list: the first word followed by the next arrangement of the rest,
when the rest has one, and otherwise the least word of the rest above the first word, followed by
the other words in nondecreasing order, or nothing when no word of the rest lies above the first. -/
def nextOf : List UInt64 → Option (List UInt64)
  | [] => none
  | x :: xs =>
    match nextOf xs with
    | some ys => some (x :: ys)
    | none =>
      match (xs.filter (x < ·)).min? with
      | none => none
      | some y => some (y :: ((x :: xs).erase y).mergeSort fun a b => a ≤ b)

/-- The flag and the words that a case expects: 1 and `nextOf xs`, or 0 and the words in
nondecreasing order when `nextOf` finds no greater arrangement. -/
def expectedOf (xs : List UInt64) : UInt64 × List UInt64 :=
  match nextOf xs with
  | some ys => (1, ys)
  | none => (0, xs.mergeSort fun a b => a ≤ b)

/-- The lists of `n` words from `vals`. -/
def tuples (vals : List UInt64) : Nat → List (List UInt64)
  | 0 => [[]]
  | n + 1 => (tuples vals n).flatMap fun t => vals.map (· :: t)

/-- The arrays of the verified compiler's cases.  The arrays of up to 5 words from 0, 1, and 2 put
the last ascent at every position, with repeated words, the 120 arrangements of 1 to 5 are the steps
of one cycle, and the arrays of 1 to 3 words from 0, `2^63 - 1`, `2^63`, and `2^64 - 1` detect a
signed comparison.  Arrays of 6 to 999 words draw words from those four by the SplitMix64 output of
the position, and a second array of each length puts its second half in nonincreasing order, so
that the last ascent lies inside the array and step L3 passes over as many as 247 words.  The long
arrays hold 1,000 words in increasing order, whose next arrangement exchanges the last two, 1,000
words in decreasing order, the greatest arrangement, 1 followed by 999 words in decreasing order,
whose last ascent is at position 0, 1,000 arbitrary words, and 2,000 words drawn from three
arbitrary words by the SplitMix64 output of the position.  An array of 10,000 words holds 3 at
position 0 and `(10,000 - k) / 4` at each later position `k`, so that step L3 passes over words
equal to 3 before it stops at the last 4.  The arrays of 20,000 words are 1, 3, and 2 followed by
0s, so that step L3 passes over 19,997 words, and 1 followed by the words from 19,999 down to 1.
The rest are 1,000 equal words and 2,000 words in nonincreasing order with each word repeated, two
greatest arrangements, and `2^63`, `2^64 - 1`, and `2^63 + 1` followed by 997 words of 5. -/
def nextPermInputs : List (List UInt64) :=
  let draw := fun (k : Nat) => (Library.Random.SplitMix64.splitMix (UInt64.ofNat k)).2.toNat
  let small := (List.range 6).flatMap (tuples [0, 1, 2])
  let high := (List.range 3).flatMap fun n =>
    tuples [0, 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff] (n + 1)
  let long := [
    (List.range 1000).map UInt64.ofNat,
    (List.range 1000).map fun k => UInt64.ofNat (1000 - k),
    1 :: (List.range 999).map fun k => UInt64.ofNat (1000 - k),
    (List.range 1000).map fun k => rw (k + 5000),
    (List.range 2000).map fun k => rw (draw k % 3 + 9000),
    (List.range 10000).map fun k => if k = 0 then 3 else UInt64.ofNat ((10000 - k) / 4)]
  let extremes : List UInt64 :=
    [0, 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff]
  let drawn := fun (n : Nat) => (List.range n).map fun k => extremes[draw (k + 1000 * n) % 4]!
  let split := fun (n : Nat) =>
    (drawn n).take (n / 2) ++ ((drawn n).drop (n / 2)).mergeSort fun a b => b ≤ a
  let middle := [6, 7, 8, 16, 33, 100, 255, 999].flatMap fun n => [drawn n, split n]
  let more := [
    [1, 3, 2] ++ List.replicate 19997 0,
    (List.range 20000).map fun k => if k = 0 then 1 else UInt64.ofNat (20000 - k),
    List.replicate 1000 7,
    (List.range 2000).map fun k => UInt64.ofNat ((1999 - k) / 10),
    [0x8000000000000000, 0xffffffffffffffff, 0x8000000000000001] ++ List.replicate 997 5]
  small ++ [1, 2, 3, 4, 5].permutations ++ high ++ long ++ middle ++ more

end Library.Combinatorics.NextPermutation
