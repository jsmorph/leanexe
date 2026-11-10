import Demos.Rcv.Spec

/-!
Executable cases of the specification of the Oakland tabulator.  Each `#guard` evaluates the
specification when the module builds.  The expected values come from the requirements: the worked
example's ballot file and report, copied byte for byte, and for the edge cases of the requirements'
section "Tests" the interpretations, reports, and result words derived by hand from the rules.  The
malformed files of that section need the reader, which the first increment does not hold.  The 2022
District 4 contest is checked natively by `rcv-spec district4` of `Demos/Rcv/Native.lean`.
-/

namespace Demos.Rcv.Cases

open Demos.Rcv Demos.Rcv.Spec

/-- The word of a position that marks the candidates `is`. -/
def pw (is : List Nat) : UInt64 :=
  (is.foldl (fun (acc : Nat) (i : Nat) => acc + (2 : Nat) ^ (i - 1)) 0).toUInt64

/-- A ballot's position words, each position given by the candidates it marks. -/
def bl (fields : List (List Nat)) : List UInt64 := fields.map pw

/-- A contest named `case` whose candidate `i` has the kind `kinds[i - 1]` and the name `Ci`. -/
def contestOf (kinds : List Kind) (order : List Nat) (k : Nat) (ballots : List (List UInt64)) :
    Contest :=
  { contest := ascii "case"
    positions := k
    candidates := (kinds.zipIdx 1).map fun p : Kind × Nat =>
      { kind := p.1, name := ascii s!"C{p.2}" }
    order
    ballots := ballots.map fun ps : List UInt64 => { ident := none, positions := ps } }

/-- `m` copies of a ballot. -/
def copies (m : Nat) (ps : List UInt64) : List (List UInt64) := List.replicate m ps

/-- Lines of ASCII text, each followed by LF. -/
def lines (ls : List String) : List UInt8 := ascii (String.join (ls.map fun l : String => l ++ "\n"))

/-- The report of `c` after its header lines. -/
def body (c : Contest) : List UInt8 := text ((reportLines c).drop (7 + c.candidates.length))

def listed (n : Nat) : List Kind := List.replicate n .listed

/-! ## The worked example -/

def exampleFile : String :=
  "rcv-ballots 1
contest example-1
positions 3
candidates 5
candidate 1 listed A
candidate 2 listed B
candidate 3 listed C
candidate 4 named-writein D
candidate 5 aggregate-writein Write-in
order 2 1 3 4 5
ballots 15
id-01,1,2,
1,,
5,1,
1|2,1,
1,3,2
1,1,
2,1,
2,,
,2,
2,3,1
3,2,
4,,
5,,
,,
*,2,
"

def ruleLine : String :=
  "rule oakland-1105 revision 1, Oakland City Charter sections 1103 and 1105 (February 2007), Cal. Elec. Code sections 15341 (updated 1999-01-01) and 15342(d) (updated 2012-01-01), texts read 2026-11-09"

/-- The report of the example after its first two lines, as the requirements give it. -/
def exampleBody : String :=
  "contest example-1
positions 3
candidates 5
candidate 1 listed A
candidate 2 listed B
candidate 3 listed C
candidate 4 named-writein D
candidate 5 aggregate-writein Write-in
order 2 1 3 4 5
ballots 15
round 1
continuing 11
votes 1 5
votes 2 4
votes 3 1
votes 4 1
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 0
eliminate batch 3 4
round 2
continuing 10
votes 1 5
votes 2 5
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 1
tie 1 2
eliminate order 1
round 3
continuing 7
votes 2 7
inactive blank 1
inactive uncounted 1
inactive overvote 2
inactive exhausted 4
winner 2
"

def worked : Contest :=
  { contest := ascii "example-1"
    positions := 3
    candidates :=
      [{ kind := .listed, name := ascii "A" }, { kind := .listed, name := ascii "B" },
        { kind := .listed, name := ascii "C" }, { kind := .namedWritein, name := ascii "D" },
        { kind := .aggregateWritein, name := ascii "Write-in" }]
    order := [2, 1, 3, 4, 5]
    ballots :=
      { ident := some (ascii "id-01"), positions := bl [[1], [2], []] } ::
        ([bl [[1], [], []], bl [[5], [1], []], bl [[1, 2], [1], []], bl [[1], [3], [2]],
          bl [[1], [1], []], bl [[2], [1], []], bl [[2], [], []], bl [[], [2], []],
          bl [[2], [3], [1]], bl [[3], [2], []], bl [[4], [], []], bl [[5], [], []],
          bl [[], [], []], [unnamedOvervote, pw [2], pw []]].map fun ps : List UInt64 =>
            { ident := none, positions := ps }) }

#guard worked.WellFormed
#guard write worked == ascii exampleFile
#guard ascii (ruleIdentifier) == (ascii ruleLine).drop 5
#guard report worked == ascii ("rcv-report 1\n" ++ ruleLine ++ "\n" ++ exampleBody)

/-! The example's contest words: `n`, `k`, `N`, the kinds, the order, and the ballots' words. -/
#guard contestWords worked ==
  [5, 3, 15, 0, 0, 0, 1, 2, 2, 1, 3, 4, 5,
    1, 2, 0, 1, 0, 0, 16, 1, 0, 3, 1, 0, 1, 4, 2, 1, 1, 0, 2, 1, 0, 2, 0, 0, 0, 2, 0, 2, 4, 1,
    4, 2, 0, 8, 0, 0, 16, 0, 0, 0, 0, 0, 9223372036854775808, 2, 0]

/-! The example's result words: 1, three rounds of 14 words, and the winner 2. -/
#guard countWords (contestWords worked) ==
  [1, 3,
    15, 11, 5, 4, 1, 1, 0, 1, 1, 2, 0, 3, 12, 0,
    3, 10, 5, 5, 0, 0, 0, 1, 1, 2, 1, 2, 1, 3,
    2, 7, 0, 7, 0, 0, 0, 1, 1, 2, 4, 0, 0, 0,
    2]

/-! ## Positions -/

#guard position 0 == .empty
#guard position 1 == .single 1
#guard position (pw [63]) == .single 63
#guard position (pw [1, 2]) == .multiple
#guard position unnamedOvervote == .multiple
#guard marks (pw [1, 5, 63]) == [1, 5, 63]

/-! ## Interpretation

Candidates 1 to 3 are listed, 4 excluded, and 5 the aggregate write-in, so `K` is 1 to 3. -/

def kindsI : List Kind := [.listed, .listed, .listed, .excluded, .aggregateWritein]

#guard countedSet kindsI == [1, 2, 3]

/-! An overvote at each position, named and unnamed, after empty and uncounted positions and after
an eliminated candidate, whether or not its candidates continue. -/
#guard [bl [[1, 2], [], []], bl [[], [1, 2], []], bl [[], [], [1, 2]],
    [unnamedOvervote, 0, 0], [0, unnamedOvervote, 0], [0, 0, unnamedOvervote],
    bl [[5], [2, 3], []], bl [[4], [5], [1, 3]], bl [[4, 5], [1], []], bl [[1, 5], [2], []]].all
  fun ps : List UInt64 => interpret kindsI [1, 2, 3] ps == .inactive .overvote
#guard interpret kindsI [1, 2, 3] (bl [[1], [2, 3], []]) == .counts 1
#guard interpret kindsI [2, 3] (bl [[1], [2, 3], []]) == .inactive .overvote
#guard interpret kindsI [3] (bl [[1, 2], [3], []]) == .inactive .overvote
#guard interpret kindsI [2, 3] [pw [1], unnamedOvervote, pw [2]] == .inactive .overvote

/-- The ballot of `k` positions whose position `j`, counted from 0, marks candidate `j + 1` when bit
`j` of `m` is set and is empty otherwise. -/
def patternBallot (k m : Nat) : List UInt64 :=
  (List.range k).map fun j : Nat => if m.testBit j then pw [j + 1] else 0

/-- The candidate of the first marked position of `patternBallot k m`. -/
def firstMarked (k m : Nat) : Nat := ((List.range k).find? fun j : Nat => m.testBit j).getD 0 + 1

/-! Every pattern of empty positions for `k` from 1 to 4: blank when no position is marked, and
otherwise a vote for the first marked candidate when every candidate continues, exhausted when none
continues, and uncounted when every candidate is uncounted. -/
#guard (List.range' 1 4).all fun k : Nat => (List.range (2 ^ k)).all fun m : Nat =>
  interpret (listed 4) [1, 2, 3, 4] (patternBallot k m) ==
    if m = 0 then .inactive .blank else .counts (firstMarked k m)
#guard (List.range' 1 4).all fun k : Nat => (List.range (2 ^ k)).all fun m : Nat =>
  interpret (listed 4) [] (patternBallot k m) ==
    if m = 0 then .inactive .blank else .inactive .exhausted
#guard (List.range' 1 4).all fun k : Nat => (List.range (2 ^ k)).all fun m : Nat =>
  interpret (List.replicate 4 .aggregateWritein) [] (patternBallot k m) ==
    if m = 0 then .inactive .blank else .inactive .uncounted

/-! Duplicate rankings. -/
#guard interpret kindsI [1, 2, 3] (bl [[1], [1], [2]]) == .counts 1
#guard interpret kindsI [2, 3] (bl [[1], [1], [2]]) == .counts 2
#guard interpret kindsI [3] (bl [[1], [1], [2]]) == .inactive .exhausted
#guard interpret kindsI [1, 3] (bl [[2], [2], [2]]) == .inactive .exhausted

/-! Ballots that rank only uncounted candidates, and uncounted rankings before a counted one. -/
#guard interpret kindsI [1, 2, 3] (bl [[5], [], []]) == .inactive .uncounted
#guard interpret kindsI [1, 2, 3] (bl [[4], [5], [4]]) == .inactive .uncounted
#guard interpret kindsI [1, 2, 3] (bl [[], [5], []]) == .inactive .uncounted
#guard interpret kindsI [1, 2, 3] (bl [[5], [1], []]) == .counts 1
#guard interpret kindsI [2, 3] (bl [[5], [1], []]) == .inactive .exhausted
#guard interpret kindsI [1, 2, 3] (bl [[], [], []]) == .inactive .blank

/-! ## Rounds -/

/-! A tie at the lowest place with three candidates, under two orders. -/
def tie3 (order : List Nat) : Contest :=
  contestOf (listed 3) order 1 (copies 3 (bl [[1]]) ++ copies 2 (bl [[2]]) ++ copies 2 (bl [[3]]))

#guard body (tie3 [1, 2, 3]) == lines
  ["round 1", "continuing 7", "votes 1 3", "votes 2 2", "votes 3 2", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "tie 2 3",
    "eliminate order 3",
    "round 2", "continuing 5", "votes 1 3", "votes 2 2", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 2", "winner 1"]
#guard body (tie3 [3, 2, 1]) == lines
  ["round 1", "continuing 7", "votes 1 3", "votes 2 2", "votes 3 2", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "tie 2 3",
    "eliminate order 2",
    "round 2", "continuing 5", "votes 1 3", "votes 3 2", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 2", "winner 1"]

/-! A tied final round under both orders. -/
def finalTie (order : List Nat) : Contest :=
  contestOf (listed 2) order 1 (copies 2 (bl [[1]]) ++ copies 2 (bl [[2]]))

#guard body (finalTie [1, 2]) == lines
  ["round 1", "continuing 4", "votes 1 2", "votes 2 2", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "tie 1 2",
    "eliminate order 2",
    "round 2", "continuing 2", "votes 1 2", "inactive blank 0", "inactive uncounted 0",
    "inactive overvote 0", "inactive exhausted 2", "winner 1"]
#guard body (finalTie [2, 1]) == lines
  ["round 1", "continuing 4", "votes 1 2", "votes 2 2", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "tie 1 2",
    "eliminate order 1",
    "round 2", "continuing 2", "votes 2 2", "inactive blank 0", "inactive uncounted 0",
    "inactive overvote 0", "inactive exhausted 2", "winner 2"]

/-! The strict test at its boundary: candidate 1's 5 votes equal the 5 of candidates 3 and 4, so no
batch qualifies, and 6 votes exceed them by one, so candidates 3 and 4 go as a batch. -/
def boundary (top : Nat) : Contest :=
  contestOf (listed 4) [1, 2, 3, 4] 2
    (copies top (bl [[1], []]) ++ copies top (bl [[2], []]) ++ copies 3 (bl [[3], []]) ++
      copies 2 (bl [[4], [1]]))

#guard body (boundary 5) == lines
  ["round 1", "continuing 15", "votes 1 5", "votes 2 5", "votes 3 3", "votes 4 2",
    "inactive blank 0", "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0",
    "eliminate lowest 4",
    "round 2", "continuing 15", "votes 1 7", "votes 2 5", "votes 3 3", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "eliminate lowest 3",
    "round 3", "continuing 12", "votes 1 7", "votes 2 5", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 3", "winner 1"]
#guard body (boundary 6) == lines
  ["round 1", "continuing 17", "votes 1 6", "votes 2 6", "votes 3 3", "votes 4 2",
    "inactive blank 0", "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0",
    "eliminate batch 3 4",
    "round 2", "continuing 14", "votes 1 8", "votes 2 6", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 3", "winner 1"]

/-! A batch whose members tie, which needs no drawing. -/
def tiedBatch : Contest :=
  contestOf (listed 4) [1, 2, 3, 4] 2
    (copies 7 (bl [[1], []]) ++ copies 7 (bl [[2], []]) ++ copies 3 (bl [[3], [1]]) ++
      copies 3 (bl [[4], []]))

#guard body tiedBatch == lines
  ["round 1", "continuing 20", "votes 1 7", "votes 2 7", "votes 3 3", "votes 4 3",
    "inactive blank 0", "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0",
    "eliminate batch 3 4",
    "round 2", "continuing 17", "votes 1 10", "votes 2 7", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 3", "winner 1"]

/-! Two nested qualifying sets of two or more candidates, `{4, 5}` for candidate 3 and `{3, 4, 5}`
for candidate 2, of which the larger goes. -/
def nested : Contest :=
  contestOf (listed 5) [1, 2, 3, 4, 5] 1
    (copies 20 (bl [[1]]) ++ copies 12 (bl [[2]]) ++ copies 6 (bl [[3]]) ++ copies 3 (bl [[4]]) ++
      copies 2 (bl [[5]]))

#guard body nested == lines
  ["round 1", "continuing 43", "votes 1 20", "votes 2 12", "votes 3 6", "votes 4 3", "votes 5 2",
    "inactive blank 0", "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0",
    "eliminate batch 3 4 5",
    "round 2", "continuing 32", "votes 1 20", "votes 2 12", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 11", "winner 1"]

/-! A batch inside which the single count ends: eliminating candidate 4 alone would give candidate 1
12 of 23 continuing ballots, a majority. -/
def batchMajority : Contest :=
  contestOf (listed 4) [1, 2, 3, 4] 2
    (copies 10 (bl [[1], []]) ++ copies 8 (bl [[2], []]) ++ copies 3 (bl [[3], []]) ++
      copies 2 (bl [[4], [1]]))

#guard body batchMajority == lines
  ["round 1", "continuing 23", "votes 1 10", "votes 2 8", "votes 3 3", "votes 4 2",
    "inactive blank 0", "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0",
    "eliminate batch 3 4",
    "round 2", "continuing 20", "votes 1 12", "votes 2 8", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 3", "winner 1"]

/-! Every ballot inactive. -/
#guard body (contestOf [.listed, .listed, .aggregateWritein] [1, 2, 3] 2
    [bl [[], []], bl [[3], []], bl [[1, 2], []], [unnamedOvervote, pw [1]]]) == lines
  ["round 1", "continuing 0", "votes 1 0", "votes 2 0", "inactive blank 1",
    "inactive uncounted 1", "inactive overvote 2", "inactive exhausted 0", "winner none"]

/-! No ballots. -/
#guard body (contestOf (listed 2) [1, 2] 1 []) == lines
  ["round 1", "continuing 0", "votes 1 0", "votes 2 0", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "winner none"]

/-! One candidate, with and without a continuing ballot. -/
#guard body (contestOf (listed 1) [1] 1 [bl [[1]], bl [[1]], bl [[]]]) == lines
  ["round 1", "continuing 2", "votes 1 2", "inactive blank 1", "inactive uncounted 0",
    "inactive overvote 0", "inactive exhausted 0", "winner 1"]
#guard body (contestOf (listed 1) [1] 1 [bl [[]]]) == lines
  ["round 1", "continuing 0", "votes 1 0", "inactive blank 1", "inactive uncounted 0",
    "inactive overvote 0", "inactive exhausted 0", "winner none"]

/-! No counted candidate. -/
#guard body (contestOf [.aggregateWritein, .excluded] [2, 1] 1 [bl [[1]], bl [[2]], bl [[]]]) == lines
  ["round 1", "continuing 0", "inactive blank 1", "inactive uncounted 2", "inactive overvote 0",
    "inactive exhausted 0", "winner none"]

/-! The contests of T15. -/
def t15 (last : List (List Nat)) : Contest :=
  contestOf (listed 3) [1, 2, 3] 3
    (copies 6 (bl [[1], [2], [3]]) ++ copies 5 (bl [[2], [1], [3]]) ++
      copies 4 (bl [[3], [2], [1]]) ++ copies 2 (bl last))

#guard body (t15 [[3], [1], [2]]) == lines
  ["round 1", "continuing 17", "votes 1 6", "votes 2 5", "votes 3 6", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "eliminate lowest 2",
    "round 2", "continuing 17", "votes 1 11", "votes 3 6", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "winner 1"]
#guard body (t15 [[1], [3], [2]]) == lines
  ["round 1", "continuing 17", "votes 1 8", "votes 2 5", "votes 3 4", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "eliminate lowest 3",
    "round 2", "continuing 17", "votes 1 8", "votes 2 9", "inactive blank 0",
    "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "winner 2"]

/-! 63 candidates and 63 positions.  One ballot ranks 63 down to 1 and the other 1 up to 63, so
round 1 eliminates the batch of 2 to 62, which hold no votes, round 2 breaks the tie of 1 and 63 by
the order, and round 3 gives candidate 1 both ballots. -/
def wide : Contest :=
  contestOf (listed 63) (List.range' 1 63) 63
    [(List.range' 1 63).map fun p : Nat => pw [64 - p], (List.range' 1 63).map fun p : Nat => pw [p]]

#guard wide.WellFormed
#guard body wide == lines
  (["round 1", "continuing 2"] ++
    (List.range' 1 63).map (fun i : Nat => s!"votes {i} {if i = 1 ∨ i = 63 then 1 else 0}") ++
    ["inactive blank 0", "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0",
      "eliminate batch " ++ " ".intercalate ((List.range' 2 61).map toString),
      "round 2", "continuing 2", "votes 1 1", "votes 63 1", "inactive blank 0",
      "inactive uncounted 0", "inactive overvote 0", "inactive exhausted 0", "tie 1 63",
      "eliminate order 63",
      "round 3", "continuing 2", "votes 1 2", "inactive blank 0", "inactive uncounted 0",
      "inactive overvote 0", "inactive exhausted 0", "winner 1"])
#guard countWords (contestWords wide) ==
  ([1, 3] ++
    ([2 ^ 63 - 1, 2, 1] ++ List.replicate 61 0 ++ [1, 0, 0, 0, 0, 3, 2 ^ 62 - 2, 0]) ++
    ([2 ^ 62 + 1, 2, 1] ++ List.replicate 61 0 ++ [1, 0, 0, 0, 0, 2, 2 ^ 62, 2 ^ 62 + 1]) ++
    ([1, 2, 2] ++ List.replicate 62 0 ++ [0, 0, 0, 0, 0, 0, 0]) ++ [1]).map Nat.toUInt64

/-! Identifiers of 1 and 64 bytes, which the count ignores. -/
def withIdents (ids : List (Option (List UInt8))) : Contest :=
  let c : Contest := finalTie [1, 2]
  { c with ballots := (c.ballots.zip ids).map fun p : Ballot × Option (List UInt8) =>
      { p.1 with ident := p.2 } }

def id64 : List UInt8 := List.replicate 64 (0x61 : UInt8)

#guard (withIdents [some (ascii "a"), some id64, none, some (ascii "A-z_0.9:")]).WellFormed
#guard write (withIdents [some (ascii "a"), some id64, none, some (ascii "A-z_0.9:")]) ==
  ascii ("rcv-ballots 1\ncontest case\npositions 1\ncandidates 2\ncandidate 1 listed C1\n" ++
    "candidate 2 listed C2\norder 1 2\nballots 4\na,1\n") ++ id64 ++ ascii ",1\n2\nA-z_0.9:,2\n"
#guard report (withIdents [some (ascii "a"), some id64, none, some (ascii "A-z_0.9:")]) ==
  report (finalTie [1, 2])
#guard !decide (withIdents [some (0x61 :: id64), none, none, none]).WellFormed
#guard !decide (withIdents [some [], none, none, none]).WellFormed
#guard !decide (withIdents [some (ascii "a b"), none, none, none]).WellFormed

/-! Contest identifiers of 1 and 64 bytes, which the file and the report print. -/
#guard ({ finalTie [1, 2] with contest := ascii "x" }).WellFormed
#guard ({ finalTie [1, 2] with contest := id64 }).WellFormed
#guard !decide ({ finalTie [1, 2] with contest := 0x61 :: id64 }).WellFormed
#guard (write { finalTie [1, 2] with contest := id64 }).take 87 ==
  ascii "rcv-ballots 1\ncontest " ++ id64 ++ [(0x0A : UInt8)]
#guard (reportLines { finalTie [1, 2] with contest := ascii "x" }).take 3 ==
  [ascii "rcv-report 1", ascii ruleLine, ascii "contest x"]

/-! Names are bytes, which the report copies. -/
#guard headerLines { finalTie [1, 2] with
    candidates := [{ kind := .listed, name := [0x4A, 0xC3, 0xA9] },
      { kind := .excluded, name := ascii "x y" }] } ==
  [ascii "contest case", ascii "positions 1", ascii "candidates 2",
    ascii "candidate 1 listed J" ++ [(0xC3 : UInt8), (0xA9 : UInt8)],
    ascii "candidate 2 excluded x y", ascii "order 1 2", ascii "ballots 4"]

/-! ## Constraints of the contest structure -/

#guard (finalTie [1, 2]).WellFormed
#guard !decide (finalTie [1, 1]).WellFormed
#guard !decide (finalTie [1]).WellFormed
#guard !decide (finalTie [0, 1, 2]).WellFormed
#guard !decide ({ finalTie [1, 2] with positions := 0, ballots := [] }).WellFormed
#guard !decide ({ finalTie [1, 2] with positions := 64, ballots := [] }).WellFormed
#guard !decide (contestOf (listed 64) (List.range' 1 64) 1 []).WellFormed
#guard !decide (contestOf [] [] 1 []).WellFormed
#guard !decide ({ finalTie [1, 2] with contest := [] }).WellFormed
#guard !decide (contestOf (listed 2) [1, 2] 1 [bl [[1], [2]]]).WellFormed
#guard !decide (contestOf (listed 2) [1, 2] 1 [bl [[3]]]).WellFormed
#guard !decide (contestOf (listed 2) [1, 2] 1 [[unnamedOvervote + 1]]).WellFormed
#guard (contestOf (listed 2) [1, 2] 1 [[unnamedOvervote], bl [[1, 2]], bl [[]]]).WellFormed
/-- `finalTie [1, 2]` with candidates of the names `a` and `b`. -/
def named (a b : List UInt8) : Contest :=
  { finalTie [1, 2] with
    candidates := [{ kind := .listed, name := a }, { kind := .listed, name := b }] }

#guard !decide (named [0x41, 0x7F] (ascii "B")).WellFormed
#guard !decide (named [] (ascii "B")).WellFormed
#guard !decide (named (List.replicate 256 (0x41 : UInt8)) (ascii "B")).WellFormed
#guard (named (List.replicate 255 (0xFF : UInt8)) [(0x20 : UInt8)]).WellFormed

/-! ## Word forms -/

/-- Two listed candidates, one position, and two ballots, one for each: round 1 ties them, the order
1 2 eliminates candidate 2, and round 2 gives candidate 1 its ballot. -/
def small : List UInt64 := [2, 1, 2, 0, 0, 1, 2, 1, 2]

#guard countWords small ==
  [1, 2, 3, 2, 1, 1, 0, 0, 0, 0, 2, 2, 3, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1]
#guard countWords (contestWords (finalTie [1, 2])) == countWords [2, 1, 4, 0, 0, 1, 2, 1, 1, 2, 2]

/-! Invalid arrays give `[0]`: a wrong length, a kind of 4, an order that is not a permutation, a
position word with bit 63 and another bit, a position word with a bit at or above `n`, `n`, `k`
outside 1 to 63, and arrays too short for a header. -/
#guard [small.dropLast, small ++ [0], [2, 1, 2, 4, 0, 1, 2, 1, 2], [2, 1, 2, 0, 0, 1, 1, 1, 2],
    [2, 1, 2, 0, 0, 0, 1, 1, 2], [2, 1, 2, 0, 0, 2, 3, 1, 2],
    [2, 1, 2, 0, 0, 1, 2, unnamedOvervote + 1, 2], [2, 1, 2, 0, 0, 1, 2, 1, 4],
    [0, 1, 0], [1, 0, 0, 0, 1], [1, 64, 0, 0, 1], [], [1], [2, 1]].all
  fun ws : List UInt64 => countWords ws == [0]
#guard countWords ([64, 1, 0] ++ List.replicate 64 0 ++ (List.range' 1 64).map Nat.toUInt64) == [0]
#guard countWords [2, 1, 2, 0, 0, 1, 2, unnamedOvervote, 2] ==
  [1, 1, 3, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 2]

end Demos.Rcv.Cases
