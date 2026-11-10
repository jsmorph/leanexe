import Demos.Rcv.Maine.Variants

/-!
Native tests of the statements of T12, T13, T14, and T15 of [the requirements](requirements.md),
section "Theorems", for the Maine count, which ran before their proofs in
`Demos/Rcv/Maine/Properties.lean`.  Each check transcribes a theorem's conclusion as a Boolean
function over the specification's definitions and evaluates it on every contest whose premises it
meets: the contest words of the edge cases that `tests/rcv/maine/edges.py` writes, seeded random
contests, and every multiset of up to `SIZE` ballots of a small alphabet under two orders.

The fault counters evaluate false variants of the statements, which a run must reject on some
contests: T12 with half of the ballots in place of more than half, with a candidate outside `K`,
with the Oakland conclusion that the count ends after round 1, and with half of the continuing
ballots of round 1; T13 without its premise that `K` has two or more candidates, with ties allowed
in the premise, and in the form of the Condorcet winner criterion; T14 with a position before `p`
changed, with position `p` changed, and with the positions after `p` changed when the count does
not name `w`; and monotonicity, which T15 refutes.

`rcv-maine-properties edges FILE...` checks the contests of the contest-word files `NAME.words`
that hold valid arrays, `random SEED COUNT MAXN MAXK MAXB` checks random contests of up to `MAXN`
candidates of every kind, `MAXK` positions, and `MAXB` ballots, `exhaustive SIZE` checks the small
multisets, and `t15` checks the two contests of T15.  Each mode prints its counts, and the exit
status is 1 if a statement fails.
-/

namespace Demos.Rcv.Maine.PropertiesNative

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Maine

abbrev Ballots := List (List UInt64)

structure Input where
  kinds : List Kind
  order : List Nat
  ballots : Ballots

/-- The ballots whose interpretation against `S` counts for `w`. -/
def votesAgainst (kinds : List Kind) (S : List Nat) (bs : Ballots) (w : Nat) : Nat :=
  bs.countP fun ps : List UInt64 => interpret kinds S ps == .counts w

/-- `a` beats `b`: more ballots count for `a` than for `b` against `{a, b}`. -/
def beats (kinds : List Kind) (bs : Ballots) (a b : Nat) : Bool :=
  votesAgainst kinds [a, b] bs b < votesAgainst kinds [a, b] bs a

/-- `a` beats or ties `b`. -/
def beatsOrTies (kinds : List Kind) (bs : Ballots) (a b : Nat) : Bool :=
  votesAgainst kinds [a, b] bs b ≤ votesAgainst kinds [a, b] bs a

/-- The ballots whose first position is single and marks `w`, for every candidate `w`. -/
def firstOf (bs : Ballots) (w : Nat) : Nat :=
  bs.countP fun ps : List UInt64 => ps.head?.map position == some (.single w)

def bit (i : Nat) : UInt64 := ((2 : Nat) ^ (i - 1)).toUInt64

/-- The positions `ps` with the position at index `j` moved to the earlier index `i`. -/
def move (ps : List UInt64) (j i : Nat) : List UInt64 :=
  ps.take i ++ ps[j]! :: (ps.drop i).take (j - i) ++ ps.drop (j + 1)

/-- `ps'` raises `w` on `ps`: it moves a position of `ps` that marks only `w` to an earlier position
and leaves the other positions in their order. -/
def raises (w : Nat) (ps ps' : List UInt64) : Bool :=
  (List.range ps.length).any fun j : Nat => (List.range j).any fun i : Nat =>
    position ps[j]! == .single w && ps' == move ps j i

/-! ## Random numbers -/

structure Gen where
  s : UInt64

def Gen.next (g : Gen) : Nat × Gen :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat, ⟨s⟩)

def Gen.below (g : Gen) (m : Nat) : Nat × Gen :=
  let (x, g) := g.next
  (if m = 0 then 0 else x % m, g)

def Gen.shuffle {α : Type} (g : Gen) (xs : List α) : List α × Gen := Id.run do
  let mut g := g
  let mut a := xs.toArray
  for i in (List.range a.size).reverse do
    let (j, g') := g.below (i + 1)
    g := g'
    a := a.swapIfInBounds i j
  return (a.toList, g)

/-- A random position word of a contest with `n` candidates: empty, single, double, or the unnamed
overvote, empty more often than in the Oakland tests so that runs of empty positions arise. -/
def Gen.word (g : Gen) (n : Nat) : UInt64 × Gen :=
  let (r, g) := g.below 100
  if r < 45 then (0, g)
  else if r < 90 then
    let (i, g) := g.below n
    (bit (i + 1), g)
  else if r < 97 then
    let (i, g) := g.below n
    let (j, g) := g.below n
    (bit (i + 1) ||| bit (j + 1), g)
  else (unnamedOvervote, g)

def Gen.words (g : Gen) (n m : Nat) : List UInt64 × Gen := Id.run do
  let mut g := g
  let mut ws : List UInt64 := []
  for _ in List.range m do
    let (w, g') := g.word n
    g := g'
    ws := ws ++ [w]
  return (ws, g)

/-- The positions of a ballot that ranks the candidates `perm` in single positions, each after no,
one, or two empty positions, cut or filled with empty positions to `k`. -/
def Gen.ranked (g : Gen) (perm : List Nat) (k : Nat) : List UInt64 × Gen := Id.run do
  let mut g := g
  let mut ps : List UInt64 := []
  for i in perm do
    let (r, g') := g.below 10
    g := g'
    let gap := if r < 7 then 0 else if r < 9 then 1 else 2
    ps := ps ++ List.replicate gap 0 ++ [bit i]
  return ((ps ++ List.replicate k 0).take k, g)

/-- A random contest.  Half of the ballots rank distinct candidates in single positions with
occasional runs of empty positions, and the others hold random words.  A favorite candidate of any
kind takes the first position of a share of the ballots from none to 60 percent, so that the
initial test and round 1 have a majority in some contests. -/
def Gen.input (g : Gen) (maxN maxK maxB : Nat) : Input × Gen := Id.run do
  let mut g := g
  let (n0, g1) := g.below maxN
  g := g1
  let n := n0 + 1
  let (k0, g2) := g.below maxK
  g := g2
  let k := k0 + 1
  let (nb, g3) := g.below (maxB + 1)
  g := g3
  let mut kinds : List Kind := []
  for _ in List.range n do
    let (r, g') := g.below 10
    g := g'
    kinds := kinds ++ [if r < 7 then .listed else if r < 8 then .namedWritein
      else if r < 9 then .aggregateWritein else .excluded]
  let (order, g4) := g.shuffle (List.range' 1 n)
  g := g4
  let (f, g5) := g.below n
  g := g5
  let (bias, g6) := g.below 4
  g := g6
  let mut ballots : Ballots := []
  for _ in List.range nb do
    let (mode, g') := g.below 2
    g := g'
    let mut ps : List UInt64 := []
    if mode = 0 then
      let (perm, g') := g.shuffle (List.range' 1 n)
      g := g'
      let (len, g'') := g.below (k + 1)
      g := g''
      let (ws, g''') := g.ranked (perm.take len) k
      g := g'''
      ps := ws
    else
      let (ws, g') := g.words n k
      g := g'
      ps := ws
    let (r, g') := g.below 10
    g := g'
    if r < 2 * bias then ps := bit (f + 1) :: ps.drop 1
    ballots := ps :: ballots
  return ({ kinds, order, ballots }, g)

/-! ## The statements -/

structure Stats where
  contests : Nat := 0
  initial : Nat := 0
  t12Test : Nat := 0
  t12Round : Nat := 0
  t12RoundRounds : Nat := 0
  t12RoundMulti : Nat := 0
  t13 : Nat := 0
  t13Late : Nat := 0
  t13Test : Nat := 0
  t14 : Nat := 0
  t14Changed : Nat := 0
  t14Rounds : Nat := 0
  t14Test : Nat := 0
  fault12Half : Nat := 0
  fault12Kind : Nat := 0
  fault12One : Nat := 0
  fault12RoundHalf : Nat := 0
  fault13Size : Nat := 0
  fault13Ties : Nat := 0
  fault13Winner : Nat := 0
  tried14Before : Nat := 0
  fault14Before : Nat := 0
  tried14At : Nat := 0
  fault14At : Nat := 0
  tried14NoWin : Nat := 0
  fault14NoWin : Nat := 0
  triedMonotone : Nat := 0
  faultMonotone : Nat := 0
  failures : Nat := 0
  messages : List String := []

def Stats.need (s : Stats) (b : Bool) (msg : String) : Stats :=
  if b then s
  else { s with failures := s.failures + 1,
                messages := if s.messages.length < 20 then msg :: s.messages else s.messages }

def Stats.summary (s : Stats) : String :=
  s!"{s.contests} contests, {s.initial} decided by the initial test; " ++
  s!"T12: {s.t12Test} winners of the test, {s.t12Round} holders of round 1, " ++
  s!"{s.t12RoundRounds} of them in counts with rounds, {s.t12RoundMulti} among three or more " ++
  s!"counted; T13: {s.t13} counted losers, {s.t13Late} in counts of two or more rounds, " ++
  s!"{s.t13Test} in counts the test decides; T14: {s.t14} replacements, {s.t14Changed} changed, " ++
  s!"{s.t14Rounds} of counts with two or more rounds, {s.t14Test} of counts the test decides; " ++
  s!"{s.failures} failing.  Faults: T12 test at half {s.fault12Half}, " ++
  s!"T12 test outside K {s.fault12Kind}, T12 ending after round 1 {s.fault12One}, " ++
  s!"T12 round 1 at half {s.fault12RoundHalf}, T13 one candidate {s.fault13Size}, " ++
  s!"T13 ties {s.fault13Ties}, Condorcet winner {s.fault13Winner}, " ++
  s!"T14 before p {s.fault14Before} of {s.tried14Before}, T14 at p {s.fault14At} of " ++
  s!"{s.tried14At}, T14 without the winner {s.fault14NoWin} of {s.tried14NoWin}, " ++
  s!"monotonicity {s.faultMonotone} of {s.triedMonotone}"

/-- T12 and its false variants.  The statement quantifies over every `w`, so the check takes every
candidate index and one above them. -/
def checkT12 (name : String) (x : Input) (cnt : Count) (s : Stats) : Stats := Id.run do
  let K := countedSet x.kinds
  let N := x.ballots.length
  let T := (tally (interpret x.kinds) K x.ballots).continuing
  let byTest := fun (w : Nat) => cnt.rounds.isEmpty && cnt.winner == some w
  let mut s := s
  for w in List.range' 1 (x.kinds.length + 1) do
    let f := firstOf x.ballots w
    if w ∈ K && N < 2 * f then
      s := { s.need (byTest w) s!"{name}: T12 test {w}" with t12Test := s.t12Test + 1 }
    if w ∈ K && 0 < N && N ≤ 2 * f && !byTest w then
      s := { s with fault12Half := s.fault12Half + 1 }
    if !(w ∈ K) && N < 2 * f && !byTest w then
      s := { s with fault12Kind := s.fault12Kind + 1 }
    let v := votesAgainst x.kinds K x.ballots w
    if T < 2 * v then
      s := { s.need (cnt.winner == some w) s!"{name}: T12 round 1 {w}" with
        t12Round := s.t12Round + 1,
        t12RoundRounds := s.t12RoundRounds + (if cnt.rounds.isEmpty then 0 else 1),
        t12RoundMulti := s.t12RoundMulti + (if 3 ≤ K.length then 1 else 0) }
      if cnt.rounds.length != 1 then s := { s with fault12One := s.fault12One + 1 }
    if 0 < T && T ≤ 2 * v && cnt.winner != some w then
      s := { s with fault12RoundHalf := s.fault12RoundHalf + 1 }
  return s

/-- T13 and its false variants. -/
def checkT13 (name : String) (x : Input) (cnt : Count) (s : Stats) : Stats := Id.run do
  let K := countedSet x.kinds
  let mut s := s
  for l in List.range' 1 (x.kinds.length + 1) do
    let others := K.filter (· != l)
    let prem := others.all fun a : Nat => beats x.kinds x.ballots a l
    if 2 ≤ K.length then
      if prem then
        s := { s.need (cnt.winner != some l) s!"{name}: T13 {l}" with
          t13 := s.t13 + (if l ∈ K then 1 else 0),
          t13Test := s.t13Test + (if l ∈ K && cnt.rounds.isEmpty then 1 else 0) }
        if l ∈ K && 2 ≤ cnt.rounds.length then s := { s with t13Late := s.t13Late + 1 }
      if (others.all fun a : Nat => beatsOrTies x.kinds x.ballots a l) && cnt.winner == some l then
        s := { s with fault13Ties := s.fault13Ties + 1 }
      if l ∈ K && (others.all fun a : Nat => beats x.kinds x.ballots l a) && cnt.winner != some l
      then s := { s with fault13Winner := s.fault13Winner + 1 }
    else if prem && cnt.winner == some l then
      s := { s with fault13Size := s.fault13Size + 1 }
  return s

/-- The replacements of the ballot at index `j`, whose position `q + 1` marks only `w`: `tails`
follow its first `q + 1` positions in the replacements of T14, and `words` replace a position
before `p` or position `p` itself in the false variants. -/
def checkT14At (name : String) (x : Input) (cnt : Count) (j q : Nat) (tails : List (List UInt64))
    (words : List UInt64) (wins : Bool) (s : Stats) : Stats := Id.run do
  let b := x.ballots[j]!
  let p := q + 1
  let recount := fun (b' : List UInt64) => count x.kinds x.order (x.ballots.set j b')
  let mut s := s
  if wins then
    for tail in tails do
      let b' := b.take p ++ tail
      let k := recount b'
      s := { s.need (k.rounds == cnt.rounds && k.winner == cnt.winner)
          s!"{name}: T14 ballot {j} position {p}" with
        t14 := s.t14 + 1, t14Changed := s.t14Changed + (if b' != b then 1 else 0),
        t14Rounds := s.t14Rounds + (if 2 ≤ cnt.rounds.length then 1 else 0),
        t14Test := s.t14Test + (if cnt.rounds.isEmpty then 1 else 0) }
    let mut i := 0
    for wd in words do
      let b' := b.set (i % p) wd
      i := i + 1
      if b' != b then
        let changed := recount b' != cnt
        if i % p == q then
          s := { s with
            tried14At := s.tried14At + 1,
            fault14At := s.fault14At + (if changed then 1 else 0) }
        else
          s := { s with
            tried14Before := s.tried14Before + 1,
            fault14Before := s.fault14Before + (if changed then 1 else 0) }
  else
    for tail in tails do
      let b' := b.take p ++ tail
      if b' != b then
        s := { s with
          tried14NoWin := s.tried14NoWin + 1,
          fault14NoWin := s.fault14NoWin + (if recount b' != cnt then 1 else 0) }
  return s

/-- The positions that mark only a counted candidate, as triples of the candidate, the ballot's
index, and the position's index, at most `cap` of them, spread evenly over the ballots. -/
def places (x : Input) (cap : Nat) : List (Nat × Nat × Nat) :=
  let K := countedSet x.kinds
  let all := (List.range x.ballots.length).flatMap fun j : Nat =>
    let b := x.ballots[j]!
    (List.range b.length).filterMap fun q : Nat => match position b[q]! with
      | .single w => if w ∈ K then some (w, j, q) else none
      | _ => none
  let stride := all.length / cap + 1
  all.zipIdx.filterMap fun p : (Nat × Nat × Nat) × Nat =>
    if p.2 % stride == 0 then some p.1 else none

/-- Monotonicity, refuted by T15: moving the winner's single position to the front of a ballot
keeps the winner. -/
def checkMonotone (x : Input) (cnt : Count) (ps : List (Nat × Nat × Nat)) (s : Stats) :
    Stats := Id.run do
  let mut s := s
  for (w, j, q) in ps do
    if 0 < q && cnt.winner == some w then
      let k := count x.kinds x.order (x.ballots.set j (move x.ballots[j]! q 0))
      s := { s with
        triedMonotone := s.triedMonotone + 1,
        faultMonotone := s.faultMonotone + (if k.winner != some w then 1 else 0) }
  return s

/-- All checks on one contest.  `tailsOf r` gives the tails that follow the first `p` positions of
a ballot with `r` positions after `p`, and `words` the words of the false variants of T14.  T14
and monotonicity take at most 48 positions of each contest. -/
def checkInput (name : String) (x : Input) (tailsOf : Nat → List (List UInt64))
    (words : List UInt64) (s : Stats) : Stats := Id.run do
  let cnt := count x.kinds x.order x.ballots
  let mut s := { s with contests := s.contests + 1,
                        initial := s.initial + (if cnt.rounds.isEmpty then 1 else 0) }
  s := checkT12 name x cnt s
  s := checkT13 name x cnt s
  let ps := places x 48
  for (w, j, q) in ps do
    s := checkT14At name x cnt j q (tailsOf (x.ballots[j]!.length - (q + 1))) words
      (cnt.winner == some w) s
  checkMonotone x cnt ps s

/-! ## T15 -/

/-- The ballots of T15: six `1,2,3`, five `2,1,3`, four `3,2,1`, and two `last`. -/
def t15Ballots (last : List Nat) : Ballots :=
  List.replicate 6 ([1, 2, 3].map bit) ++ List.replicate 5 ([2, 1, 3].map bit) ++
    List.replicate 4 ([3, 2, 1].map bit) ++ List.replicate 2 (last.map bit)

def checkT15 : IO Bool := do
  let kinds : List Kind := [.listed, .listed, .listed]
  let a := t15Ballots [3, 1, 2]
  let b := t15Ballots [1, 3, 2]
  let first := count kinds [1, 2, 3] a
  let second := count kinds [1, 2, 3] b
  let raised := raises 1 ([3, 1, 2].map bit) ([1, 3, 2].map bit)
  let same := a.take 15 == b.take 15
  let oakland := first == Spec.count kinds [1, 2, 3] a && second == Spec.count kinds [1, 2, 3] b
  let firsts := firstCounts kinds a == [(1, 6), (2, 5), (3, 6)] &&
    firstCounts kinds b == [(1, 8), (2, 5), (3, 4)]
  let elims := first.rounds.map Round.elimination == [some (.lowest 2), none] &&
    second.rounds.map Round.elimination == [some (.lowest 3), none]
  IO.println s!"t15: raised {raised}, first 15 ballots equal {same}, first winner {first.winner}, \
    second winner {second.winner}, the Oakland counts {oakland}, first counts {firsts}, \
    eliminations {elims}"
  return raised && same && first.winner == some 1 && second.winner == some 2 && oakland &&
    firsts && elims

/-! ## Inputs -/

/-- The words of the exhaustive contests' alphabet and of the false variants of T14 there. -/
def smallWords : List UInt64 := [0, bit 1, bit 2, bit 3, bit 4, bit 1 ||| bit 2, unnamedOvervote]

/-- Tails of `r` positions from `smallWords`, and a tail one position shorter and one longer. -/
def smallTails (r : Nat) : List (List UInt64) :=
  let base : List (List UInt64) := match r with
    | 0 => [[]]
    | 1 => smallWords.map fun w : UInt64 => [w]
    | _ => (List.range smallWords.length).map fun i : Nat =>
      (List.range r).map fun t : Nat => smallWords[(i + 3 * t) % smallWords.length]!
  base ++ [List.replicate (r - 1) 0, List.replicate r (bit 2) ++ [bit 3]]

/-- The alphabet of the exhaustive contests: three listed candidates and an aggregate write-in,
four positions, and the blank ballot, the unnamed overvote, an overvote after a ranking, the
write-in alone and before a single empty position, two empty positions before a ranking at the
start and after one, a single empty position between rankings, and twelve rankings of the listed
candidates. -/
def alphabet : Ballots :=
  let rankings : List (List Nat) :=
    [[1], [2], [3], [1, 2], [2, 1], [3, 1], [1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2],
      [3, 2, 1]]
  [[0, 0, 0, 0], [unnamedOvervote, 0, 0, 0], [bit 1, bit 2 ||| bit 3, 0, 0], [bit 4, 0, 0, 0],
      [bit 4, 0, bit 1, 0], [0, 0, bit 1, 0], [bit 1, 0, 0, bit 2], [bit 2, 0, bit 3, 0]] ++
    rankings.map fun r : List Nat => (r.map bit) ++ List.replicate (4 - r.length) 0

/-- The multisets of `size` elements of `lo, …, m - 1`, as nondecreasing lists. -/
def multisets (m : Nat) : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | size + 1, lo =>
    (List.range' lo (m - lo)).flatMap fun i : Nat => (multisets m size i).map (i :: ·)

/-- The little-endian 64-bit words of a file. -/
def wordsOf (bs : ByteArray) : List UInt64 :=
  (List.range (bs.size / 8)).map fun j : Nat =>
    (List.range 8).foldr
      (fun (b : Nat) (acc : UInt64) => (acc <<< 8) ||| (bs.get! (8 * j + b)).toUInt64) 0

/-- Random tails and words for one contest of `n` candidates. -/
def Gen.material (g : Gen) (n : Nat) : (Nat → List (List UInt64)) × List UInt64 × Gen :=
  let (t1, g) := g.words n 8
  let (t2, g) := g.words n 8
  let (ws, g) := g.words n 6
  (fun r : Nat => [t1.take r, t2.take (r + 1), (t1.drop 3).take (r - 1)], ws, g)

/-! ## Main -/

def printStats (label : String) (s : Stats) : IO UInt32 := do
  for m in s.messages.reverse do IO.println s!"failure: {m}"
  IO.println s!"{label}: {s.summary}"
  return if s.failures == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "edges" :: files =>
    let mut s : Stats := {}
    let mut g : Gen := ⟨11⟩
    let mut invalid := 0
    for path in files do
      let ws := wordsOf (← IO.FS.readBinFile path)
      let d := readWords ws
      if decide (d.Valid ws.length) then
        let x : Input := { kinds := d.kinds.map kindOfCode, order := d.order, ballots := d.ballots }
        let (tails, wds, g') := g.material d.n
        g := g'
        s := checkInput path x tails wds s
      else invalid := invalid + 1
    IO.println s!"edge files: {files.length}, invalid arrays: {invalid}"
    printStats "edges" s
  | ["random", seed, n, maxN, maxK, maxB] =>
    let mut g : Gen := ⟨seed.toNat!.toUInt64⟩
    let mut s : Stats := {}
    for i in List.range n.toNat! do
      let (x, g') := g.input maxN.toNat! maxK.toNat! maxB.toNat!
      let (tails, ws, g'') := g'.material x.kinds.length
      g := g''
      s := checkInput s!"random {i}" x tails ws s
    printStats "random" s
  | ["exhaustive", size] =>
    let kinds : List Kind := [.listed, .listed, .listed, .aggregateWritein]
    let mut s : Stats := {}
    for m in (List.range (size.toNat! + 1)).flatMap fun k : Nat => multisets alphabet.length k 0 do
      let ballots := m.map fun i : Nat => alphabet[i]!
      for order in [[1, 2, 3, 4], [3, 2, 1, 4]] do
        s := checkInput s!"exhaustive {m} {order}" { kinds, order, ballots } smallTails
          (smallWords ++ smallWords) s
    printStats "exhaustive" s
  | ["t15"] =>
    return if ← checkT15 then 0 else 1
  | _ =>
    IO.eprintln ("usage: rcv-maine-properties edges FILE... | " ++
      "random SEED COUNT MAXN MAXK MAXB | exhaustive SIZE | t15")
    return 2

end Demos.Rcv.Maine.PropertiesNative

def main (args : List String) : IO UInt32 := Demos.Rcv.Maine.PropertiesNative.main args
