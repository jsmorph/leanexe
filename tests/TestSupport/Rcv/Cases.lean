import Demos.Rcv.Cases
import Library.Random.SplitMix64.Program
import TestSupport.OrderBook.Words

/-! The cases of the module `rcvCount`, the export `count` of `Demos/Rcv/Compiled.lean`, whose
expected results are those of the specification `Demos.Rcv.Spec.countArray` in native Lean.  The
arrays are the contest words of the contests of `Demos/Rcv/Cases.lean`, the invalid arrays of that
file, and random contests that SplitMix64 draws from fixed seeds.  Every array passes through a file
of little-endian words under `build/verified/rcvCount/`, which `cases` writes, since the larger
arrays exceed the length of a command-line argument.  A case requires two retained blocks, the
host's array and the result. -/

namespace TestSupport.Rcv.Cases

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Cases
open TestSupport.OrderBook.Words (wordBytes hostArray)

/-- The directory of the cases' files, relative to the repository's root. -/
def dir : System.FilePath := "build/verified/rcvCount"

/-- Writes the array `ws` to the file of the case `name` and prints the case. -/
def emit (name : String) (ws : Array UInt64) : IO Unit := do
  let path := dir / s!"{name}.bin"
  IO.FS.writeBinFile path (wordBytes ws)
  IO.println s!"rcvCount|count|array-u64|file-u64:{path}|{hostArray (countArray ws)}|2"

/-- The contests of `Demos/Rcv/Cases.lean`, each with a name. -/
def contests : List (String × Contest) :=
  [("worked", worked), ("tie3-123", tie3 [1, 2, 3]), ("tie3-321", tie3 [3, 2, 1]),
    ("final-tie-12", finalTie [1, 2]), ("final-tie-21", finalTie [2, 1]),
    ("boundary-5", boundary 5), ("boundary-6", boundary 6), ("tied-batch", tiedBatch),
    ("nested", nested), ("batch-majority", batchMajority),
    ("all-inactive", contestOf [.listed, .listed, .aggregateWritein] [1, 2, 3] 2
      [bl [[], []], bl [[3], []], bl [[1, 2], []], [unnamedOvervote, pw [1]]]),
    ("no-ballots", contestOf (listed 2) [1, 2] 1 []),
    ("one-candidate", contestOf (listed 1) [1] 1 [bl [[1]], bl [[1]], bl [[]]]),
    ("one-candidate-blank", contestOf (listed 1) [1] 1 [bl [[]]]),
    ("no-counted",
      contestOf [.aggregateWritein, .excluded] [2, 1] 1 [bl [[1]], bl [[2]], bl [[]]]),
    ("t15-first", t15 [[3], [1], [2]]), ("t15-second", t15 [[1], [3], [2]]), ("wide", wide)]

/-- The arrays of `Demos/Rcv/Cases.lean` outside its contests: `small`, the arrays that are not
valid contests, and a valid array with an unnamed overvote. -/
def arrays : List (String × List UInt64) :=
  [("small", small), ("short-by-one", small.dropLast), ("long-by-one", small ++ [0]),
    ("kind-4", [2, 1, 2, 4, 0, 1, 2, 1, 2]), ("order-repeat", [2, 1, 2, 0, 0, 1, 1, 1, 2]),
    ("order-zero", [2, 1, 2, 0, 0, 0, 1, 1, 2]), ("order-above", [2, 1, 2, 0, 0, 2, 3, 1, 2]),
    ("overvote-and-bit", [2, 1, 2, 0, 0, 1, 2, unnamedOvervote + 1, 2]),
    ("bit-above-n", [2, 1, 2, 0, 0, 1, 2, 1, 4]), ("n-0", [0, 1, 0]), ("k-0", [1, 0, 0, 0, 1]),
    ("k-64", [1, 64, 0, 0, 1]), ("empty", []), ("one-word", [1]), ("two-words", [2, 1]),
    ("n-64", [64, 1, 0] ++ List.replicate 64 0 ++ (List.range' 1 64).map Nat.toUInt64),
    ("ballots-2-32", [1, 1, 4294967296, 0, 1]),
    ("unnamed-overvote", [2, 1, 2, 0, 0, 1, 2, unnamedOvervote, 2])]

/-- A generator of words, the state of SplitMix64. -/
abbrev Gen := StateM UInt64

/-- The next word of SplitMix64. -/
def next : Gen UInt64 := modifyGet fun s =>
  let (s', v) := Library.Random.SplitMix64.splitMix s
  (v, s')

/-- A word below `n`, for a positive `n`. -/
def below (n : UInt64) : Gen UInt64 := return (← next) % n

/-- A candidate from 1 to `n`.  Without `skewed`, each candidate has the same probability.  With
it and four or more candidates, each of candidates 1 to 3 has the probability 7 in 30, and the
rest form a tail from candidate 4 in which each candidate is 3/8 as likely as the one before, so
that no candidate holds a majority and the tail behind a candidate qualifies for a batch. -/
def candidate (n : UInt64) (skewed : Bool) : Gen UInt64 := do
  if !skewed || n < 4 then return 1 + (← below n)
  if (← below 10) < 7 then return 1 + (← below 3)
  let mut i : UInt64 := 4
  while i < n && (← below 8) < 3 do
    i := i + 1
  return i

/-- A position word over `n` candidates: empty, one candidate, two candidates, or the unnamed
overvote, with the probabilities 35, 50, 10, and 5 percent. -/
def positionWord (n : UInt64) (skewed : Bool) : Gen UInt64 := do
  let r ← below 100
  if r < 35 then return 0
  else if r < 85 then return (1 : UInt64) <<< ((← candidate n skewed) - 1)
  else if r < 95 then
    return ((1 : UInt64) <<< ((← candidate n skewed) - 1)) ||| (1 : UInt64) <<< (← below n)
  else return unnamedOvervote

/-- The contest array of a random contest of `n` candidates, `k` positions, and `N` ballots: kinds
`listed` with probability 7 in 10 and each other kind with 1 in 10, a random tie-break order, and
position words of `positionWord`. -/
def randomContest (n k N : Nat) (skewed : Bool) : Gen (Array UInt64) := do
  let mut ws : Array UInt64 := #[n.toUInt64, k.toUInt64, N.toUInt64]
  for _ in [0:n] do
    let r ← below 10
    ws := ws.push (if r < 7 then 0 else if r < 8 then 1 else if r < 9 then 2 else 3)
  let mut order := (List.range' 1 n).toArray.map Nat.toUInt64
  for i in [0:n] do
    let j := i + (← below (n - i).toUInt64).toNat
    order := order.swapIfInBounds i j
  ws := ws ++ order
  for _ in [0:N * k] do
    ws := ws.push (← positionWord n.toUInt64 skewed)
  return ws

/-- The random contests: a seed, `n`, `k`, `N`, and whether the votes are skewed.  The small
contests give ties, the skewed ones batches, and the largest has the size of a district contest of
the corpus. -/
def randoms : List (UInt64 × Nat × Nat × Nat × Bool) :=
  [(1, 2, 1, 7, false), (2, 3, 2, 9, false), (3, 3, 3, 12, false), (4, 4, 2, 10, false),
    (5, 5, 3, 12, false), (6, 4, 1, 6, false), (7, 5, 4, 30, false), (8, 6, 3, 40, false),
    (9, 6, 3, 200, true), (10, 8, 4, 500, true), (11, 10, 5, 1000, true), (12, 12, 6, 2000, true),
    (13, 12, 5, 2000, false), (14, 20, 8, 1500, true), (15, 63, 5, 300, true),
    (16, 63, 63, 100, true), (17, 63, 3, 2000, false), (18, 10, 5, 20000, true)]

/-- Writes the cases' files and prints the cases. -/
def cases : IO Unit := do
  IO.FS.createDirAll dir
  for (name, c) in contests do
    emit name (contestWords c).toArray
  for (name, ws) in arrays do
    emit name ws.toArray
  for (seed, n, k, N, skewed) in randoms do
    emit s!"random-{seed}" ((randomContest n k N skewed).run' seed).run

end TestSupport.Rcv.Cases
